// Command goclient dials a QUIC echo server through katzenpost's quic/common.
package main

import (
	"bytes"
	"context"
	"crypto/tls"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"io"
	"net"
	"net/url"
	"os"
	"time"

	"github.com/katzenpost/katzenpost/quic/common"
	"github.com/quic-go/quic-go"
)

func fatal(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "goclient: "+format+"\n", args...)
	os.Exit(1)
}

func payload(n int) []byte {
	b := make([]byte, n)
	for i := range b {
		b[i] = byte(i % 251)
	}
	return b
}

func roundTrip(s *quic.Stream, want []byte) error {
	werr := make(chan error, 1)
	go func() {
		_, err := s.Write(want)
		if cerr := s.Close(); err == nil {
			err = cerr
		}
		werr <- err
	}()
	got, err := io.ReadAll(s)
	if err != nil {
		return fmt.Errorf("read: %w", err)
	}
	if err := <-werr; err != nil {
		return fmt.Errorf("write: %w", err)
	}
	if !bytes.Equal(got, want) {
		i := 0
		for i < len(got) && i < len(want) && got[i] == want[i] {
			i++
		}
		return fmt.Errorf("echo mismatch: sent %d bytes, got %d, first difference at %d", len(want), len(got), i)
	}
	return nil
}

func main() {
	connect := flag.String("connect", "127.0.0.1:4433", "server UDP address")
	pinHex := flag.String("pin", "", "hex sha256 of the server's SubjectPublicKeyInfo")
	size := flag.Int("payload-size", 100000, "bytes sent on each stream")
	streams := flag.Int("streams", 1, "number of sequential bidirectional streams")
	timeout := flag.Duration("timeout", 60*time.Second, "overall deadline")
	useMLDSA := flag.Bool("mldsa", false, "accept only an ML-DSA-65 certificate, over plain quic-go and crypto/tls")
	flag.Parse()

	pin, err := hex.DecodeString(*pinHex)
	if err != nil || len(pin) != 32 {
		fatal("--pin must be 64 hex characters")
	}
	if *size < 0 || *streams < 1 {
		fatal("--payload-size must be >= 0 and --streams >= 1")
	}

	ctx, cancel := context.WithTimeout(context.Background(), *timeout)
	defer cancel()
	dialCtx, dialCancel := context.WithTimeout(ctx, 10*time.Second)
	var qconn *quic.Conn
	var first *quic.Stream
	auth := "Ed25519"
	if *useMLDSA {
		qconn, err = dialMLDSA(dialCtx, *connect, pin)
		auth = "ML-DSA-65"
	} else {
		u := &url.URL{Scheme: "quic", Host: *connect}
		var conn net.Conn
		conn, err = common.DialURL(u, dialCtx, nil, pin, (*common.Options)(nil).ForClient())
		if err == nil {
			qc := conn.(*common.QuicConn)
			qconn, first = qc.Conn, qc.Stream
		}
	}
	dialCancel()
	if errors.Is(err, common.ErrQUICKeyMismatch) {
		fatal("pin mismatch: %v", err)
	}
	if err != nil {
		fatal("dial: %v", err)
	}
	defer qconn.CloseWithError(0, "")

	cs := qconn.ConnectionState().TLS
	suite := tls.CipherSuiteName(cs.CipherSuite)
	if cs.CurveID != tls.X25519MLKEM768 {
		fatal("negotiated group %s, want %s", cs.CurveID, tls.X25519MLKEM768)
	}

	want := payload(*size)
	for i := 0; i < *streams; i++ {
		s := first
		if i > 0 || s == nil {
			if s, err = qconn.OpenStreamSync(ctx); err != nil {
				fatal("stream %d: open: %v", i, err)
			}
		}
		if deadline, ok := ctx.Deadline(); ok {
			s.SetDeadline(deadline)
		}
		if err := roundTrip(s, want); err != nil {
			fatal("stream %d: %v", i, err)
		}
	}
	fmt.Printf("OK bytes=%d group=%s suite=%s auth=%s\n", *size**streams, cs.CurveID, suite, auth)
}
