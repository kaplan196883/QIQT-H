# Reproduction log

The whole point of QIQT-H is that you don't have to trust the author — you can rebuild every
proof yourself and read the machine-generated [claim card](https://qiqt.org/claim-card). This file
is the public log of independent reproductions.

**If you reproduce the build, please add a line** (open a PR editing this file, or open an issue) with:
the **commit hash** you built, your **OS / CPU / RAM**, the approximate **wall-clock time**, and the
**verdict** (the `verify/out/claim_card.md` overall verdict + the trusted-base line). Anything from
"it built and the audit passed" to a full log is welcome — including *failed* or *surprising* results.

How to reproduce (either path):

```bash
git clone https://github.com/kaplan196883/QIQT-H && cd QIQT-H
cat verify/verify.sh          # read it first
bash verify/verify.sh         # → verify/out/claim_card.md   (reuses the pinned Mathlib build)
# — or, fully from source in a pinned container —
docker build -t qiqt-verify -f verify/Dockerfile . && docker run --rm qiqt-verify
```

What a reproduction certifies (and what it cannot): it establishes that, in the build **on your
machine**, the Lean kernel accepts each capstone theorem and its complete transitive dependency set is
only the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no project
axiom. It does **not** certify that the Lean statements faithfully model the physics (the adequacy
judgment, left to the reader via the rendered statement) or that the labelled physical inputs hold in
nature. See [`verify/README.md`](verify/README.md).

---

## Reproductions

| Date | Reporter | Commit | Environment | Wall-clock | Verdict |
|------|----------|--------|-------------|-----------|---------|
| _(none yet — be the first)_ | | | | | |
