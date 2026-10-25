"""Extract the RFC 9001 Appendix A packet protection samples into named hex values.

Usage: python3 -I scripts/extract_rfc9001.py rfc9001.txt > testdata/rfc9001_appendix_a.json
"""
import json, re, sys

text = open(sys.argv[1]).read()
a = text[text.rindex("Appendix A.  Sample Packet Protection"):text.rindex("Appendix B.  AEAD Algorithm Analysis")]
a = "\n".join(l for l in a.splitlines() if not l.startswith("RFC 9001") and not l.startswith("Thomson")
              and "\f" not in l)

def hexrun(after, stop=None):
    """The hex digits in the lines following `after`, up to the first line that is not hex."""
    i = a.index(after) + len(after)
    out = ""
    for line in a[i:].splitlines()[1:]:
        t = line.strip()
        if not t:
            if out:
                break
            continue
        if not re.fullmatch(r"[0-9a-f ]+", t):
            break
        out += t.replace(" ", "")
    return out

def value(name, section):
    """`name = ... = hex` or `name = hex`, with continuation lines, inside `section`."""
    s = a[a.index(section):]
    m = re.search(r"\n\s*" + re.escape(name) + r"\s*(?:\n\s*)?=(?:[^=\n]*\n\s*=)?\s*([0-9a-f]+(?:\n\s+[0-9a-f]+)*)", s)
    return re.sub(r"\s", "", m.group(1))

v = {
    "dcid": "8394c8f03e515708",
    "initial_secret": value("initial_secret", "A.1.  Keys"),
    "client_initial_secret": value("client_initial_secret", "A.1.  Keys"),
    "client_key": value("key", "The secrets for protecting client packets"),
    "client_iv": value("iv ", "The secrets for protecting client packets"),
    "client_hp": value("hp ", "The secrets for protecting client packets"),
    "server_initial_secret": value("server_initial_secret", "A.1.  Keys"),
    "server_key": value("key", "The secrets for protecting server packets"),
    "server_iv": value("iv ", "The secrets for protecting server packets"),
    "server_hp": value("hp ", "The secrets for protecting server packets"),
    "client_crypto_frame": hexrun("plus enough PADDING\n   frames to make a 1162-byte payload:"),
    "client_header": hexrun("a packet number of 2:"),
    "client_packet": hexrun("The resulting protected packet is:"),
    "server_payload": hexrun("a CRYPTO frame, and no PADDING frames:"),
    "server_header": hexrun("for a packet number of 1:"),
    "server_packet": hexrun("The final protected packet is then:"),
    "retry_packet": hexrun("value is not included in the final Retry packet:"),
    "chacha_secret": value("secret", "A.5.  ChaCha20-Poly1305"),
    "chacha_key": value("key", "A.5.  ChaCha20-Poly1305"),
    "chacha_iv": value("iv ", "A.5.  ChaCha20-Poly1305"),
    "chacha_hp": value("hp ", "A.5.  ChaCha20-Poly1305"),
    "chacha_ku": value("ku ", "A.5.  ChaCha20-Poly1305"),
    "chacha_unprotected_header": re.search(r"unprotected header = ([0-9a-f]+)", a).group(1),
    "chacha_packet": re.search(r"packet = ([0-9a-f]+)", a).group(1),
}
for k, x in v.items():
    assert x and len(x) % 2 == 0 and re.fullmatch("[0-9a-f]+", x), k
assert len(v["client_packet"]) == 2 * 1200, len(v["client_packet"])
json.dump({"source": "RFC 9001 Appendix A", "chacha_pn": 654360564, "vectors": v}, sys.stdout, indent=1)
print()
