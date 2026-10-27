.PHONY: build test axioms interop bench

build:
	lake build LeanQUIC LeanQUIC.Tests.Vectors LeanQUIC.Tests.Recovery LeanQUIC.Tests.Buffers \
	  LeanQUIC.Tests.Loopback quic_echo_server quic_echo_client example_server example_client example_sansio

test: build
	lake exe LeanQUIC.Tests.Vectors
	lake exe LeanQUIC.Tests.Recovery
	lake exe LeanQUIC.Tests.Buffers
	lake exe LeanQUIC.Tests.Loopback
	lake exe example_sansio

axioms: build
	./scripts/check-axioms.sh

interop: build
	cd interop && LEAN_SERVER=$(CURDIR)/.lake/build/bin/quic_echo_server \
	  LEAN_CLIENT=$(CURDIR)/.lake/build/bin/quic_echo_client ./run.sh

# Extra LeanBench flags, e.g. `make bench BENCH_ARGS='--match "poll" --samples 5'`.
BENCH_ARGS ?=

# The benchmarks are their own Lake project in bench/, so the library does not depend on LeanBench.
bench:
	cd bench && lake -q --log-level=error exe lean_quic-bench $(BENCH_ARGS)
