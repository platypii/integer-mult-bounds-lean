#!/usr/bin/env python3
"""Check one basis for the original PR589 orthogonal MOVE and COPY projectors.

Uses SymPy for exact rational linear algebra. In the reversed address layout,
GoodForm.good_move requires the first r leading principal minors of a rank-r
projector to be units. Check them in the same basis for the entire pinned word.
"""
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path

from sympy import Matrix, zeros

from generate_pr589_moves import SHA256

WORD = (Path(__file__).resolve().parents[1] / "integer-mult-bounds/research/"
        "e8-bit-p111-tuned/tune/bitE8mut-p111-tuned.json.gz")


def frame_projector(lines, indices):
    """Return the dimension and dot-product orthogonal projector of the frame."""
    if not indices:
        return 0, zeros(8)
    rows = Matrix([lines[i] for i in indices])
    pivots = rows.T.rref()[1]
    basis = rows[list(pivots), :]
    return len(pivots), basis.T * (basis * basis.T).inv() * basis


def scheduled_pairs(word, dimensions):
    frames = list(map(set, word["frames"]))
    refs = word["start"].copy()
    pairs = Counter()
    first = {}
    last = {}
    for section in "DABC":
        if section == "B":
            retained = [refs[i] for i in word["ret"]]
            assert len(retained) == 9 and all(dimensions[f] == 7 for f in retained)
            pairs.update((0, f) for f in retained)
        for frame, target, sources in word[section]:
            for i in [target, *sources]:
                first.setdefault(i, frame)
                last[i] = frame
                old = refs[i]
                assert frames[old] <= frames[frame] or frames[frame] <= frames[old]
                if dimensions[old] != dimensions[frame]:
                    pairs[tuple(sorted((old, frame), key=dimensions.__getitem__))] += 1
                refs[i] = frame
    assert all(first[t] == 2 + t == word["start"][t] for t in range(111))
    assert all(last[111 + t] == 525 + t for t in range(111))
    assert refs == word["final"] and sum(pairs.values()) == 2911 + 9
    return pairs


def main():
    raw = WORD.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA256
    word = json.loads(gzip.decompress(raw))
    basis = Matrix(8, 8, lambda i, j: (3 + i) ** j)
    inverse = basis.inv()
    dimensions, original = zip(*(frame_projector(word["lines"], f) for f in word["frames"]))
    projected = [basis * p * inverse for p in original]
    pairs = scheduled_pairs(word, dimensions)
    max_bits = 0
    for lo, hi in pairs:
        difference = projected[hi] - projected[lo]
        for k in range(1, dimensions[hi] - dimensions[lo] + 1):
            minor = difference[:k, :k].det(method="domain-ge")
            assert minor != 0, (lo, hi, k)
            max_bits = max(max_bits, abs(int(minor.p)).bit_length(), int(minor.q).bit_length())
    print(f"{sum(pairs.values())} occurrences, {len(pairs)} distinct frame pairs. "
          f"Every required leading minor is nonzero. Maximum numerator or denominator: "
          f"{max_bits} bits.")


if __name__ == "__main__":
    main()
