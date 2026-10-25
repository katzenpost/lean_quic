#!/usr/bin/env bash
# Runs the QUIC echo interop matrix. See README.md.
set -u

here=$(cd "$(dirname "$0")" && pwd)
GO=${GO:-go}
SEED=${SEED:-000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f}
SIZES=${SIZES:-"0 1 1200 100000 3000000"}
TIMEOUT=${TIMEOUT:-60}
LOSSY=${LOSSY:-1}
DROP=${DROP:-5}
REORDER=${REORDER:-5}
LEAN_SERVER=${LEAN_SERVER:-}
LEAN_CLIENT=${LEAN_CLIENT:-}

export QUIC_GO_DISABLE_RECEIVE_BUFFER_WARNING=true

mkdir -p "$here/.run"
work=$(mktemp -d "$here/.run/XXXXXX")
(cd "$here" && "$GO" build -o bin/ ./cmd/...) || { echo "build failed" >&2; exit 2; }

pids=()
cleanup() {
	for p in "${pids[@]}"; do kill "$p" 2>/dev/null; done
	wait 2>/dev/null
}
trap cleanup EXIT

free_port() {
	local p
	while :; do
		p=$((20000 + RANDOM % 40000))
		[ -z "$(ss -Hlun "sport = :$p" 2>/dev/null)" ] && { echo "$p"; return; }
	done
}

cmd_for() {
	case $1 in
	go-server) echo "$here/bin/goserver" ;;
	go-client) echo "$here/bin/goclient" ;;
	lean-server) echo "$LEAN_SERVER" ;;
	lean-client) echo "$LEAN_CLIENT" ;;
	esac
}

# spawn LOG CMD ARGS... starts CMD in the background and sets $spawned.
spawn() {
	local log=$1 cmd=$2
	shift 2
	bash -c "exec $cmd \"\$@\"" "$cmd" "$@" >"$log.out" 2>"$log.err" &
	spawned=$!
	pids+=("$spawned")
}

await_ready() {
	local log=$1 pid=$2 i
	for i in $(seq 100); do
		grep -qx READY "$log.out" 2>/dev/null && return 0
		kill -0 "$pid" 2>/dev/null || return 1
		sleep 0.1
	done
	return 1
}

stop() {
	kill "$1" 2>/dev/null
	wait "$1" 2>/dev/null
}

results=()
failed=0
n=0

# run CLIENT SERVER SIZE STREAMS LOSSY
run() {
	local client=$1 server=$2 size=$3 streams=$4 lossy=$5
	n=$((n + 1))
	local log="$work/$n-$client-$server-$size-$streams-$lossy"
	local sport port result detail start elapsed spid ppid=
	sport=$(free_port)
	port=$sport
	start=$(date +%s.%N)
	spawn "$log.server" "$(cmd_for "$server")" --listen "127.0.0.1:$sport" --seed "$SEED"
	spid=$spawned
	if ! await_ready "$log.server" "$spid"; then
		result=FAIL detail="server not ready"
	else
		local pin
		pin=$(awk '$1 == "SPKI-SHA256" {print $2; exit}' "$log.server.out")
		if [ "$lossy" = yes ]; then
			port=$(free_port)
			spawn "$log.proxy" "$here/bin/lossyproxy" --listen "127.0.0.1:$port" --upstream "127.0.0.1:$sport" \
				--drop-percent "$DROP" --reorder-percent "$REORDER" --seed "$n"
			ppid=$spawned
			await_ready "$log.proxy" "$ppid" || detail="proxy not ready"
		fi
		local ccmd
		ccmd=$(cmd_for "$client")
		timeout "$TIMEOUT" bash -c "exec $ccmd \"\$@\"" "$ccmd" --connect "127.0.0.1:$port" --pin "$pin" \
			--payload-size "$size" --streams "$streams" >"$log.client.out" 2>"$log.client.err"
		local rc=$?
		local want="OK bytes=$((size * streams)) group=X25519MLKEM768 suite="
		if [ $rc -eq 124 ]; then
			result=FAIL detail="timeout ${TIMEOUT}s"
		elif [ $rc -ne 0 ]; then
			result=FAIL detail="client exit $rc: $(tail -n1 "$log.client.err")"
		elif ! grep -q "^$want" "$log.client.out"; then
			result=FAIL detail="bad output: $(head -n1 "$log.client.out")"
		elif [ "$server" = go-server ] && ! grep -q "^conn group=X25519MLKEM768 alpn=h3 suite=" "$log.server.err"; then
			result=FAIL detail="server did not log the handshake"
		else
			result=PASS detail=$(head -n1 "$log.client.out" | sed 's/.*suite=/suite=/')
		fi
	fi
	if [ -n "$ppid" ]; then
		stop "$ppid"
		[ "$result" = PASS ] && detail="$detail $(tail -n1 "$log.proxy.err")"
	fi
	stop "$spid"
	elapsed=$(awk -v a="$start" -v b="$(date +%s.%N)" 'BEGIN {print b - a}')
	[ "$result" = PASS ] || failed=$((failed + 1))
	results+=("$(printf '%-12s %-12s %8s %3s %-5s %-4s %6.2fs  %s' "$client" "$server" "$size" "$streams" "$lossy" "$result" "$elapsed" "$detail")")
	echo "${results[-1]}"
}

pairs=("go-client go-server")
[ -n "$LEAN_CLIENT" ] && pairs+=("lean-client go-server")
[ -n "$LEAN_SERVER" ] && pairs+=("go-client lean-server")
[ -n "$LEAN_CLIENT" ] && [ -n "$LEAN_SERVER" ] && pairs+=("lean-client lean-server")

for pair in "${pairs[@]}"; do
	set -- $pair
	for size in $SIZES; do
		run "$1" "$2" "$size" 1 no
	done
	run "$1" "$2" 100000 4 no
	if [ "$LOSSY" = 1 ]; then
		run "$1" "$2" 100000 1 yes
		run "$1" "$2" 3000000 1 yes
		run "$1" "$2" 100000 4 yes
	fi
done

echo
echo "Summary ($work)"
printf '%-12s %-12s %8s %3s %-5s %-4s %7s  %s\n' client server bytes K lossy res time detail
printf '%s\n' "${results[@]}"
echo "$((n - failed))/$n passed"
[ "$failed" -eq 0 ]
