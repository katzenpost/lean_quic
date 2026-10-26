// Command goserver is a QUIC echo server built on katzenpost's quic/common.
package main

import (
	"context"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"encoding/hex"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"

	signschemes "github.com/katzenpost/hpqc/sign/schemes"
	"github.com/katzenpost/katzenpost/quic/common"
	"github.com/quic-go/quic-go"
)

func fatal(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "goserver: "+format+"\n", args...)
	os.Exit(1)
}

// loadKey feeds the seed to common.LoadStaticKey, which reads it from a file.
func loadKey(seed []byte) (*common.StaticKey, error) {
	base, err := os.UserCacheDir()
	if err != nil {
		return nil, err
	}
	if err := os.MkdirAll(base, 0o700); err != nil {
		return nil, err
	}
	dir, err := os.MkdirTemp(base, "goserver-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(dir)
	path := filepath.Join(dir, "quic.key")
	if err := os.WriteFile(path, seed, 0o600); err != nil {
		return nil, err
	}
	return common.ReadStaticKey(path)
}

func main() {
	listen := flag.String("listen", "127.0.0.1:4433", "UDP address to listen on")
	seedHex := flag.String("seed", "", "32-byte hex seed of the Ed25519 TLS key")
	certOut := flag.String("cert-out", "", "also write the leaf certificate DER to this file")
	useMLDSA := flag.Bool("mldsa", false, "authenticate with ML-DSA-65 over plain quic-go and crypto/tls; the seed is its FIPS 204 seed")
	flag.Parse()

	seed, err := hex.DecodeString(*seedHex)
	if err != nil || len(seed) != 32 {
		fatal("--seed must be 64 hex characters")
	}
	if *useMLDSA {
		serveMLDSA(*listen, seed)
		return
	}
	key, err := loadKey(seed)
	if err != nil {
		fatal("load key: %v", err)
	}
	cert, err := key.GetCertificate(nil)
	if err != nil {
		fatal("certificate: %v", err)
	}
	leaf, err := x509.ParseCertificate(cert.Certificate[0])
	if err != nil {
		fatal("parse certificate: %v", err)
	}
	if *certOut != "" {
		if err := os.WriteFile(*certOut, cert.Certificate[0], 0o644); err != nil {
			fatal("write certificate: %v", err)
		}
	}
	spki := sha256.Sum256(leaf.RawSubjectPublicKeyInfo)
	if hex.EncodeToString(spki[:]) != hex.EncodeToString(key.Hash()) {
		fatal("certificate SPKI hash differs from StaticKey.Hash")
	}

	_, identity, err := signschemes.ByName("Ed25519").GenerateKey()
	if err != nil {
		fatal("identity key: %v", err)
	}
	l, err := common.ListenWithEpochKeys(*listen, identity, key, nil)
	if err != nil {
		fatal("listen: %v", err)
	}
	if w := l.UDPBuffers().Warning(); w != "" {
		fmt.Fprintln(os.Stderr, "goserver:", w)
	}
	printReady(spki[:])

	for {
		c, err := l.Accept()
		if err != nil {
			fatal("accept: %v", err)
		}
		go serve(c.(*common.QuicConn))
	}
}

func printReady(spki []byte) {
	fmt.Printf("SPKI-SHA256 %x\nREADY\n", spki)
	os.Stdout.Sync()
}

func logConn(cs tls.ConnectionState) {
	fmt.Fprintf(os.Stderr, "conn group=%s alpn=%s suite=%s\n",
		cs.CurveID, cs.NegotiatedProtocol, tls.CipherSuiteName(cs.CipherSuite))
}

func serve(qc *common.QuicConn) {
	logConn(qc.Conn.ConnectionState().TLS)
	// The first stream goes through QuicConn exactly as katzenpost reads it.
	if err := echoFirst(qc); err != nil {
		logStreamErr(err)
		return
	}
	for {
		s, err := qc.Conn.AcceptStream(context.Background())
		if err != nil {
			return
		}
		if err := echo(s, s); err != nil {
			logStreamErr(err)
		}
		s.Close()
	}
}

func echoFirst(qc *common.QuicConn) error {
	buf := make([]byte, 64<<10)
	for {
		n, err := qc.Read(buf)
		if n > 0 {
			if _, werr := qc.Write(buf[:n]); werr != nil {
				return werr
			}
		}
		if errors.Is(err, io.EOF) {
			return qc.Stream.Close()
		}
		if err != nil {
			return err
		}
	}
}

func echo(w io.Writer, r io.Reader) error {
	_, err := io.Copy(w, r)
	return err
}

func logStreamErr(err error) {
	var appErr *quic.ApplicationError
	if errors.As(err, &appErr) && appErr.ErrorCode == 0 {
		return
	}
	fmt.Fprintf(os.Stderr, "stream error: %v\n", err)
}
