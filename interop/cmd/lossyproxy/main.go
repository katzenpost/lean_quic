// Command lossyproxy relays UDP datagrams between QUIC peers, dropping and
// reordering a share of them.
package main

import (
	"flag"
	"fmt"
	"math/rand/v2"
	"net"
	"os"
	"os/signal"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

type proxy struct {
	mu      sync.Mutex
	rng     *rand.Rand
	drop    float64
	reorder float64
	delay   time.Duration
	dropped atomic.Int64
	held    atomic.Int64
	relayed atomic.Int64
	retries atomic.Int64
}

func (p *proxy) roll() (drop, hold bool) {
	p.mu.Lock()
	defer p.mu.Unlock()
	return p.rng.Float64()*100 < p.drop, p.rng.Float64()*100 < p.reorder
}

// forward sends b with conn, possibly dropping it or delaying it past later packets.
func (p *proxy) forward(b []byte, send func([]byte)) {
	drop, hold := p.roll()
	switch {
	case drop:
		p.dropped.Add(1)
	case hold:
		p.held.Add(1)
		c := append([]byte(nil), b...)
		time.AfterFunc(p.delay, func() { send(c) })
	default:
		p.relayed.Add(1)
		send(b)
	}
}

func main() {
	listen := flag.String("listen", "127.0.0.1:4434", "UDP address facing the client")
	upstream := flag.String("upstream", "127.0.0.1:4433", "UDP address of the server")
	dropPct := flag.Float64("drop-percent", 0, "percentage of datagrams dropped")
	reorderPct := flag.Float64("reorder-percent", 0, "percentage of datagrams delayed behind later ones")
	delay := flag.Duration("reorder-delay", 10*time.Millisecond, "delay of a reordered datagram")
	seed := flag.Uint64("seed", 1, "PRNG seed")
	flag.Parse()

	p := &proxy{rng: rand.New(rand.NewPCG(*seed, *seed^0x9e3779b97f4a7c15)), drop: *dropPct, reorder: *reorderPct, delay: *delay}
	laddr, err := net.ResolveUDPAddr("udp", *listen)
	if err != nil {
		fatal(err)
	}
	uaddr, err := net.ResolveUDPAddr("udp", *upstream)
	if err != nil {
		fatal(err)
	}
	front, err := net.ListenUDP("udp", laddr)
	if err != nil {
		fatal(err)
	}
	fmt.Println("READY")
	os.Stdout.Sync()

	var mu sync.Mutex
	backs := map[string]*net.UDPConn{}
	buf := make([]byte, 65535)
	go report(p)
	for {
		n, client, err := front.ReadFromUDP(buf)
		if err != nil {
			fatal(err)
		}
		mu.Lock()
		back, ok := backs[client.String()]
		if !ok {
			if back, err = net.DialUDP("udp", nil, uaddr); err != nil {
				mu.Unlock()
				fatal(err)
			}
			backs[client.String()] = back
			go func(back *net.UDPConn, client *net.UDPAddr) {
				b := make([]byte, 65535)
				for {
					n, err := back.Read(b)
					if err != nil {
						return
					}
					if isRetry(b[:n]) {
						p.retries.Add(1)
					}
					p.forward(b[:n], func(d []byte) { front.WriteToUDP(d, client) })
				}
			}(back, client)
		}
		mu.Unlock()
		p.forward(buf[:n], func(d []byte) { back.Write(d) })
	}
}

// isRetry reports whether d is a QUIC v1 Retry packet.
func isRetry(d []byte) bool {
	return len(d) >= 5 && d[0]&0xb0 == 0xb0 && d[1] == 0 && d[2] == 0 && d[3] == 0 && d[4] == 1
}

func report(p *proxy) {
	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGTERM, syscall.SIGINT)
	<-sig
	fmt.Fprintf(os.Stderr, "relayed=%d dropped=%d reordered=%d retry=%d\n", p.relayed.Load(), p.dropped.Load(), p.held.Load(), p.retries.Load())
	os.Exit(0)
}

func fatal(err error) {
	fmt.Fprintln(os.Stderr, "lossyproxy:", err)
	os.Exit(1)
}
