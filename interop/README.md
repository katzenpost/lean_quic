# QUIC interop harness

Echo tests between Go and Lean QUIC peers, using katzenpost's own QUIC
settings. The Go peers import `github.com/katzenpost/katzenpost/quic/common`
and `github.com/quic-go/quic-go` v0.63.0 directly:

- `goserver` loads its key with `common.ReadStaticKey` (the Ed25519 seed
  file a katzenpost gateway uses), takes its certificate from
  `StaticKey.GetCertificate` (`epochCertificate`) and listens with
  `common.ListenWithEpochKeys(addr, identity, key, nil)`, so it has the
  default `Options`: ALPN `h3`, Go's default curves, Retry on every
  handshake, the `Config()` transport settings and a stateless reset key
  derived from a fresh Ed25519 identity key. The first stream of a
  connection is read and written through `common.QuicConn` from
  `QuicListener.Accept`; later streams use `Conn.AcceptStream`.
- `goclient` dials with `common.DialURL("quic://host:port", ..., pin,
  (*common.Options)(nil).ForClient())`, so it pins the server with
  `verifyQUICKeyHash` and uses the client `dialConfig()`. Its first stream
  is the one `DialURL` opens; later streams use `Conn.OpenStreamSync`.

katzenpost allows one incoming bidirectional stream at a time
(`MaxIncomingStreams: 1`), so `--streams K` opens streams one after another.

## Running

    ./run.sh

needs Go on `PATH` (or `GO=/path/to/go`). It builds `bin/`, then runs
go-client against go-server over UDP loopback for payloads of 0, 1, 1200,
100000 and 3000000 bytes, four streams of 100000 bytes, and the same through
`lossyproxy` with 5% drop and 5% reordering. It prints a summary and exits
non-zero if any run fails. Logs are kept in `.run/`.

Lean peers are added with

    LEAN_SERVER=/path/to/lean-server LEAN_CLIENT=/path/to/lean-client ./run.sh

which adds lean-client to go-server, go-client to lean-server and, when both
are set, lean-client to lean-server.

Other variables: `SIZES`, `TIMEOUT` (seconds per client run, default 60),
`LOSSY=0` to skip the proxy runs, `DROP` and `REORDER` (percent), `SEED`, and
`KEY_UPDATE=N` to have the Lean endpoints update their keys every `N` packets
(`--key-update N`), and `REBIND=N` to have the proxy move to a new
server-facing port after `N` client datagrams, closing the old one, as a NAT
rebinding would (`--rebind-after N`).

## CLI contract

Server: `--listen 127.0.0.1:PORT --seed HEX64`. The seed is the 32-byte
Ed25519 private key seed. On startup the server prints to stdout, in order,

    SPKI-SHA256 <64 hex digits>
    READY

where the hash is sha256 of the leaf certificate's DER SubjectPublicKeyInfo.
It echoes every bidirectional stream and closes its send side after the
peer's FIN, until killed. `goserver` also logs
`conn group=<curve> alpn=<proto> suite=<cipher suite>` to stderr per
connection and takes `--cert-out FILE` to save the certificate DER.

Client: `--connect host:port --pin HEX64 --payload-size N --streams K`
(defaults N=100000, K=1). Each stream carries N bytes where byte i is
i mod 251; the client closes its send side, reads to EOF and compares. It
fails with a non-zero exit and a message on stderr if the pin does not match,
the group is not X25519MLKEM768 or the echo differs, and otherwise prints

    OK bytes=<N*K> group=X25519MLKEM768 suite=<cipher suite>

The Lean client appends ` keyupdates=<count>`, and both Lean endpoints take
`--key-update N` to start a key update every N packets.

## lossyproxy

    lossyproxy --listen ADDR --upstream ADDR --drop-percent P \
        --reorder-percent R --seed S [--reorder-delay 10ms] [--rebind-after N]

prints `READY`, relays datagrams, drops P% and delays R% behind later ones in
both directions. On SIGTERM it prints
`relayed=… dropped=… reordered=… retry=…` to stderr, where `retry` counts
QUIC v1 Retry packets from the server.
