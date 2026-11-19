#!/usr/bin/env python3
"""Check that translating degree-seven polynomials by 2 gives prefix pivots for PR589."""
import gzip
import hashlib
import json
from fractions import Fraction
from math import comb, gcd, lcm
from pathlib import Path

from generate_pr589_moves import SHA256
from generate_pr589_copy_ranks import inverse

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


def graph_rows(rows, rank):
    """Recover the prefix graph [I | A] by reducing the integral generators."""
    rows = [list(map(Fraction, row)) for row in rows]
    for j in range(rank):
        pivot = next(i for i in range(j, len(rows)) if rows[i][j])
        rows[j], rows[pivot] = rows[pivot], rows[j]
        rows[j] = [x / rows[j][j] for x in rows[j]]
        for i, row in enumerate(rows):
            if i != j and row[j]:
                rows[i] = [x - row[j] * y for x, y in zip(row, rows[j])]
    assert all(not any(row) for row in rows[rank:])
    return rows[:rank]


def translate(row):
    return [sum(row[k] * comb(k, j) * 2 ** (k - j) for k in range(j, 8))
            for j in range(8)]


def main():
    raw = WORD.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA256
    word = json.loads(gzip.decompress(raw))
    lines = word["lines"]
    shifted = [translate(row) for row in lines]
    max_entry = max(abs(x) for row in shifted for x in row)
    ranks = []
    max_denominator = 1
    max_relation_denominator = 1
    relations = 0
    for i, frame in enumerate(word["frames"]):
        rank = len(pivots(lines[j] for j in frame))
        assert pivots(shifted[j] for j in frame) == set(range(rank)), i
        graph = graph_rows((shifted[j] for j in frame), rank)
        basis = []
        for j in frame:
            row = shifted[j]
            if len(pivots([*basis, row])) > len(basis):
                basis.append(row)
        assert len(basis) == rank
        dual = inverse([row[:rank] for row in basis]) if rank else []
        for j in frame:
            row = shifted[j]
            coefficients = [sum(x * y for x, y in zip(row[:rank], column)) for column in zip(*dual)]
            den = lcm(*(x.denominator for x in coefficients))
            weights = [int(den * x) for x in coefficients]
            assert all(den * row[k] == sum(a * b[k] for a, b in zip(weights, basis)) for k in range(8))
            max_relation_denominator = max(max_relation_denominator, den)
            relations += 1
        max_denominator = max([max_denominator] + [x.denominator for row in graph for x in row])
        ranks.append(rank)

    labels = [set(frame) for frame in word["frames"]]
    refs = word["start"].copy()
    moves = 0
    # The scatter COPY windows have a separate rank bill. This is the phase replay
    # in generate_pr589_moves.py, whose scatter boundary preserves the phase refs.
    for section in "DABC":
        if section == "B":
            copy_frames = [refs[source] for source in word["ret"]]
            assert copy_frames == list(range(510, 519))
            assert all(ranks[f] == 7 for f in copy_frames)
            adds = [(111 + t, k) for t, indices in enumerate(word["scatter"]) for k in indices]
            assert len(adds) == 527
            assert all(refs[t] == 0 and 0 <= k < len(copy_frames) for t, k in adds)
            assert ranks[0] == 0
        for frame, target, sources in word[section]:
            for register in [target, *sources]:
                old = refs[register]
                assert labels[old] <= labels[frame] or labels[frame] <= labels[old]
                moves += ranks[old] != ranks[frame]
                refs[register] = frame
    assert (len(ranks), moves) == (636, 2911)
    assert max_relation_denominator <= 2 ** 100
    print(f"Verified {relations} integral generator relations; maximum denominator: {max_relation_denominator}.")
    print("Verified nine rank-seven COPY prefixes and 527 zero-frame ADD targets.")
    print(f"Maximum translated entry magnitude: {max_entry}. Maximum graph denominator: {max_denominator}.")
    print(f"Verified prefix pivots for {len(ranks)} labels and consecutive pivots for {moves} positive-rank phase MOVEs.")


if __name__ == "__main__":
    main()
