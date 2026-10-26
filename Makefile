.PHONY: build test interop

build:
	lake build LeanQUIC LeanQUIC.Tests.Vectors LeanQUIC.Tests.Recovery LeanQUIC.Tests.Buffers \
	  LeanQUIC.Tests.Loopback quic_echo_server quic_echo_client example_server example_client example_sansio

test: build
	lake exe LeanQUIC.Tests.Vectors
	lake exe LeanQUIC.Tests.Recovery
	lake exe LeanQUIC.Tests.Buffers
	lake exe LeanQUIC.Tests.Loopback
	lake exe example_sansio

interop: build
	cd interop && LEAN_SERVER=$(CURDIR)/.lake/build/bin/quic_echo_server \
	  LEAN_CLIENT=$(CURDIR)/.lake/build/bin/quic_echo_client ./run.sh
