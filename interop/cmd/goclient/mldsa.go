package main

import (
	"bytes"
	"context"
	"crypto/mldsa"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"errors"

	"github.com/quic-go/quic-go"
)

// dialMLDSA dials over plain quic-go and crypto/tls, accepting only an ML-DSA-65 certificate whose
// SubjectPublicKeyInfo hashes to pin.
func dialMLDSA(ctx context.Context, addr string, pin []byte) (*quic.Conn, error) {
	return quic.DialAddr(ctx, addr, &tls.Config{
		InsecureSkipVerify: true,
		NextProtos:         []string{"h3"},
		MinVersion:         tls.VersionTLS13,
		CurvePreferences:   []tls.CurveID{tls.X25519MLKEM768},
		VerifyPeerCertificate: func(raw [][]byte, _ [][]*x509.Certificate) error {
			if len(raw) == 0 {
				return errors.New("no certificate")
			}
			leaf, err := x509.ParseCertificate(raw[0])
			if err != nil {
				return err
			}
			if _, ok := leaf.PublicKey.(*mldsa.PublicKey); !ok {
				return errors.New("not an ML-DSA certificate")
			}
			h := sha256.Sum256(leaf.RawSubjectPublicKeyInfo)
			if !bytes.Equal(h[:], pin) {
				return errors.New("pin mismatch")
			}
			return nil
		},
	}, &quic.Config{})
}
