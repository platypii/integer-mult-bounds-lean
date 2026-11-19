#!/usr/bin/env python3
"""Check that translating degree-seven polynomials by 2 gives prefix pivots for PR589."""
import gzip
import hashlib
import json
from math import comb, gcd
from pathlib import Path

from generate_pr589_moves import SHA256

WORD = (Path(__file__).resolve().parents[1] / "integer-mult-bounds/research/"
        "e8-bit-p111-tuned/tune/bitE8mut-p111-tuned.json.gz")


def pivots(rows):
    """Return the pivot columns over the rationals by fraction-free row elimination."""
    basis = {}
    for row in rows:
        v = list(row)
        for j in range(len(v)):
            if not v[j]:
                continue
            if j not in basis:
                basis[j] = v
                break
            b = basis[j]
            v = [b[j] * x - v[j] * y for x, y in zip(v, b)]
            divisor = gcd(*v)
            if divisor:
                v = [x // divisor for x in v]
    return set(basis)


def translate(row):
    return [sum(row[k] * comb(k, j) * 2 ** (k - j) for k in range(j, 8))
            for j in range(8)]


def main():
    raw = WORD.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA256
    word = json.loads(gzip.decompress(raw))
    lines = word["lines"]
    shifted = [translate(row) for row in lines]
    ranks = []
    for i, frame in enumerate(word["frames"]):
        rank = len(pivots(lines[j] for j in frame))
        assert pivots(shifted[j] for j in frame) == set(range(rank)), i
        ranks.append(rank)

    labels = [set(frame) for frame in word["frames"]]
    refs = word["start"].copy()
    moves = 0
    # The scatter COPY windows have a separate rank bill. This is the phase replay
    # in generate_pr589_moves.py, whose scatter boundary preserves the phase refs.
    for section in "DABC":
        for frame, target, sources in word[section]:
            for register in [target, *sources]:
                old = refs[register]
                assert labels[old] <= labels[frame] or labels[frame] <= labels[old]
                moves += ranks[old] != ranks[frame]
                refs[register] = frame
    assert (len(ranks), moves) == (636, 2911)
    print(f"Verified prefix pivots for {len(ranks)} labels and consecutive pivots for {moves} positive-rank phase MOVEs.")


if __name__ == "__main__":
    main()
