#!/usr/bin/env python3
"""Emit integral dual rows for the higher-dimensional translated PR589 prefix minors."""
import gzip
import hashlib
import json
from math import comb, lcm
from pathlib import Path

from generate_pr589_copy_ranks import inverse, rref, vec
from generate_pr589_scalar import SHA256
from generate_pr589_moves import rank

ROOT = Path(__file__).resolve().parents[1]
WORD = ROOT / "integer-mult-bounds/research/e8-bit-p111-tuned/tune/bitE8mut-p111-tuned.json.gz"
OUT = ROOT / "IntegerMultBounds/MathlibTM2/M6/PrefixWitnesses"


def main():
    raw = WORD.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA256
    word = json.loads(gzip.decompress(raw))
    OUT.mkdir(exist_ok=True)
    size = 20
    blocks = []
    for label in range(266, len(word["frames"])):
        if (label - 266) % size == 0:
            start = label
            chunks = [header(["PrefixCertificate"])]
            blocks.append(start)
        d = rank(word["lines"], word["frames"][label])
        indices = []
        rows = []
        for line in word["frames"][label]:
            v = word["lines"][line]
            row = [sum(v[k] * comb(k, j) * 2 ** (k-j) for k in range(j, 8)) for j in range(d)]
            if len(rref([*rows, row])[1]) > len(rows):
                indices.append(line)
                rows.append(row)
        assert len(rows) == d
        dual = []
        for row in inverse(rows):
            scale = lcm(*(x.denominator for x in row))
            dual.append(vec([x * scale for x in row]))
        chunks.append(f"def prefix{label} : PrefixCertificate {d} :=\n"
                      f"  ⟨{vec(indices)}, ![" + ",\n    ".join(dual) + "]⟩\n\n"
                      f"theorem prefix{label}_checked : prefix{label}.Checked {label} := by\n"
                      "  decide +kernel\n\n")
        if (label - start + 1 == size or label + 1 == len(word["frames"])):
            chunks.append(f"theorem block{start} (i : ℕ) (lo : {start} ≤ i) (hi : i ≤ {label}) :\n"
                          "    HasPrefixWitness i (Geometry.Dimensions.value i) := by\n"
                          "  interval_cases i\n")
            for i in range(start, label + 1):
                chunks.append(f"  · exact PrefixCertificate.witness (by decide) prefix{i}_checked\n")
            (OUT / f"Block{start}.lean").write_text("".join(chunks) + END)
    chunks = [header(["PrefixWitness", *[f"PrefixWitnesses.Block{i}" for i in blocks]])]
    chunks.append("theorem prefix_witness (i : ℕ) (live : i < 636) :\n"
                  "    HasPrefixWitness i (Geometry.Dimensions.value i) := by\n"
                  "  by_cases low : i < 266\n"
                  "  · by_cases full : i = 1\n"
                  "    · subst i\n"
                  "      exact full_prefix_witness 1 live (by decide)\n"
                  "    · have dims : ∀ j : Fin 266, j.val ≠ 1 → Geometry.Dimensions.value j.val ≤ 2 := by decide +kernel\n"
                  "      exact small_prefix_witness i live rfl (dims ⟨i, low⟩ full)\n")
    for start in blocks[:-1]:
        chunks.append(f"  by_cases h{start} : i < {start + size}\n"
                      f"  · exact block{start} i (by omega) (by omega)\n")
    chunks.append(f"  exact block{blocks[-1]} i (by omega) (by omega)\n")
    (OUT / "All.lean").write_text("".join(chunks) + END)


END = "\nend IntegerMultBounds.MathlibTM2.M6\n"


def header(modules):
    imports = "".join(f"public import IntegerMultBounds.MathlibTM2.M6.{m}\n" for m in modules)
    return ("module\n\n" + imports +
            "public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.Data\n\n"
            "/-! Generated from the pinned PR589 word by generate_pr589_prefix_witnesses.py. -/\n"
            "@[expose] public section\nnamespace IntegerMultBounds.MathlibTM2.M6\n\n"
            "open IntegerMultBounds.Networks.Certificates.PR589\n\n")


if __name__ == "__main__":
    main()
