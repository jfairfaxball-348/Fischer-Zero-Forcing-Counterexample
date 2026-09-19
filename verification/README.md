# Independent verification

`check_fischer_h.py` is intentionally independent of the Lean kernel and of third-party graph libraries.

Run:

```bash
python3 verification/check_fischer_h.py
```

Expected final line:

```
Z(H): 11
```

The script reconstructs the published graph from the source construction, decodes the graph6 string independently, and parses the edge list actually present in `FischerGraph.lean`. It refuses to continue unless all three agree, then reproduces the finite structural, independence and zero-forcing checks described in `docs/VERIFICATION_PROTOCOL.md`.

This script is an audit aid, not a substitute for the final kernel-checked Lean proof.
