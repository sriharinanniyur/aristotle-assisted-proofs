# Lean proofs of Karatsuba and Toom-Cook multiplication

Lean 4 correctness proofs of the Karatsuba and Toom-Cook algorithms, assisted by Aristotle and GPT-5.

This repository is an archive of our early work; we have covered several more multiplication/division algorithms since, and we have also updated the proofs of the two algorithms covered in this repo. See [here](https://github.com/sriharinanniyur/verified_mul_dcv) for a development repo containing our latest work.

Algorithms covered:
- Karatsuba's algorithm
- Toom-Cook algorithm with integer evaluation points

To build, clone the repo and `cd` into it, then type `lake build`.

v1.0 archived tree: https://github.com/sriharinanniyur/lean-multiplication/tree/e5080be36736f2e3ea3061ed32c35930700aff4c.

All proofs co-authored-by: Aristotle (Harmonic) aristotle-harmonic@harmonic.fun @Aristotle-Harmonic
