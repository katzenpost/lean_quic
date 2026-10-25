# lean_quic

*QUIC version 1 in Lean 4, post-quantum.*

This library has not been audited by any third party.

QUIC (RFC 9000, 9001, 9002) over [lean_tls](https://github.com/katzenpost/lean_tls)'s TLS 1.3
handshake, negotiating the X25519MLKEM768 hybrid key exchange. The connection is a pure value:
`recv` gives it a datagram, `poll` asks for the next one to send, `onTimeout` reports a passed
deadline, and the time is always an argument. The only IO is `LeanQUIC.UDP`, a driver over
Lean's own `Std.Async.UDP`.

## Modules

* `VarInt`, `Packet`, `Frame`, `TransportParams`: the wire format and packet protection.
  `Packet.openPayload_sealPayload` carries the AEAD's correctness over to packets and
  `Packet.applyMask_applyMask` shows header protection undoes itself.
* `Recovery`: loss detection and NewReno congestion control (RFC 9002), with the congestion
  window's lower bound as a proof field of its state.
* `Buffers`: stream and CRYPTO reassembly and retransmission, its interval sets carrying their
  sortedness as proofs.
* `Connection`: the connection state machine. Stream data is accepted only once TLS has produced
  its evidence that the peer is authenticated.
* `UDP`, `Cmd/EchoServer`, `Cmd/EchoClient`: the driver and the interop executables.

## Tests

```bash
make test       # RFC 9000/9001 vectors, recovery, buffers, in-process transfers
make interop    # against quic-go through katzenpost's own QUIC transport, see interop/
```

* `LeanQUIC.Tests.Vectors`: RFC 9001 Appendix A byte for byte (Initial keys, client and server
  Initial packets, Retry, ChaCha20-Poly1305 short header) and RFC 9000's varint and packet number
  examples. `testdata/rfc9001_appendix_a.json` is extracted from the RFC text by
  `scripts/extract_rfc9001.py`.
* `LeanQUIC.Tests.Loopback`: a client and a server connection in process through a simulated
  network with loss, reordering and duplication, transferring up to 3 MB.
