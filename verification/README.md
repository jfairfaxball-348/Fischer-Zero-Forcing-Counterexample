# Independent verification

`check_fischer_h.py` is intentionally independent of the Lean development and of third-party graph libraries.

Run:

```bash
python3 verification/check_fischer_h.py
```

Expected final line:

```
Z(H): 11
```

The script reconstructs the published graph twice — once from the source construction and once from the graph6 string — and refuses to continue unless the edge sets agree. It then reproduces the finite structural, independence and zero-forcing checks described in `docs/VERIFICATION_PROTOCOL.md`.

This script is an audit aid, not a substitute for the final kernel-checked Lean proof.
