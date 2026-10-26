package main

import (
	"context"
	"crypto/mldsa"
	"crypto/rand"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"math/big"
	"net"
	"time"

	"github.com/quic-go/quic-go"
)

// mldsaCertificate is a self-signed ML-DSA-65 certificate for the key with FIPS 204 seed seed.
func mldsaCertificate(seed []byte) (tls.Certificate, error) {
	key, err := mldsa.NewPrivateKey(mldsa.MLDSA65(), seed)
	if err != nil {
		return tls.Certificate{}, err
	}
	serial, err := rand.Int(rand.Reader, new(big.Int).Lsh(big.NewInt(1), 127))
	if err != nil {
		return tls.Certificate{}, err
	}
	now := time.Now()
	tmpl := &x509.Certificate{
		SerialNumber: serial,
		NotBefore:    now.Add(-time.Hour),
		NotAfter:     now.Add(time.Hour),
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, tmpl, key.PublicKey(), key)
	if err != nil {
		return tls.Certificate{}, err
	}
	return tls.Certificate{Certificate: [][]byte{der}, PrivateKey: key}, nil
}

// serveMLDSA serves the echo over plain quic-go and crypto/tls, authenticated by an ML-DSA-65
// certificate, with a Retry before every connection as katzenpost's servers do.
func serveMLDSA(listen string, seed []byte) {
	cert, err := mldsaCertificate(seed)
	if err != nil {
		fatal("ML-DSA-65 certificate: %v", err)
	}
	leaf, err := x509.ParseCertificate(cert.Certificate[0])
	if err != nil {
		fatal("parse certificate: %v", err)
	}
	spki := sha256.Sum256(leaf.RawSubjectPublicKeyInfo)
	addr, err := net.ResolveUDPAddr("udp", listen)
	if err != nil {
		fatal("listen: %v", err)
	}
	udp, err := net.ListenUDP("udp", addr)
	if err != nil {
		fatal("listen: %v", err)
	}
	tr := &quic.Transport{Conn: udp, VerifySourceAddress: func(net.Addr) bool { return true }}
	l, err := tr.Listen(&tls.Config{
		Certificates:     []tls.Certificate{cert},
		NextProtos:       []string{"h3"},
		MinVersion:       tls.VersionTLS13,
		CurvePreferences: []tls.CurveID{tls.X25519MLKEM768},
	}, &quic.Config{})
	if err != nil {
		fatal("listen: %v", err)
	}
	printReady(spki[:])
	for {
		c, err := l.Accept(context.Background())
		if err != nil {
			fatal("accept: %v", err)
		}
		go func() {
			cs := c.ConnectionState().TLS
			logConn(cs)
			for {
				s, err := c.AcceptStream(context.Background())
				if err != nil {
					return
				}
				if err := echo(s, s); err != nil {
					logStreamErr(err)
				}
				s.Close()
			}
		}()
	}
}
