#!/usr/bin/env python3
"""The S6 retune: the cost chain at the stage-2 PR97 exponent.

The supplier seam points at the stage-2 supplier (`M8/Stage2Machine/Total`, the reversed family on
PR97 design-B frames inside the F L F wrapper). This sets the cost chain's exponent and saving:

* `Parameters.tau = 1 - 123899714039/10^15` (`Stage2Machine.Total.tau`, `Bound.tau₂_eq`);
* `CompactInterim.lam = 1 - 12389971/10^11`, `lam' = 1 - 12389970/10^11`, `kappa = 4223103985/2^46`;
* `Cost.Total.tot_kappa_eq`: `totKappa = 3840891135209/(10^15 * 2^38)`;
* the stated saving of `mulInTime` and its callers, and their documentation.

The binding margin is the layer margin `ε (1-λ')`, rounded down to `2^-46`. Every replacement
must match exactly once, so the script fails loudly on a changed upstream text.

usage: retune.py [--dry-run]
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DRY = '--dry-run' in sys.argv

KAPPA_OLD, KAPPA_NEW = '3299646951', '4223103985'

EDITS = {
    'IntegerMultBounds/Parameters.lean': [
        ('def tau : ℝ := 1 - 96806834039 / 10 ^ 15', 'def tau : ℝ := 1 - 123899714039 / 10 ^ 15'),
    ],
    'IntegerMultBounds/MathlibTM2/Cost/CompactInterimParameters.lean': [
        ('def lam : ℝ := 1-9680683/(10^11:ℝ)', 'def lam : ℝ := 1-12389971/(10^11:ℝ)'),
        ("def lam' : ℝ := 1-9680682/(10^11:ℝ)", "def lam' : ℝ := 1-12389970/(10^11:ℝ)"),
        ('about `2^-14.38`.', 'about `2^-14.02`.'),
        ('def kappa : ℝ := 3299646951/(2^46:ℝ)', 'def kappa : ℝ := 4223103985/(2^46:ℝ)'),
    ],
    'IntegerMultBounds/MathlibTM2/Cost/Total.lean': [
        ('Exponents: `τ = 1 - 96806834039/10¹⁵`', 'Exponents: `τ = 1 - 123899714039/10¹⁵`'),
        ('κ = ε c (1 - τ) = 259 / (10¹¹ · 2³³)', 'κ = ε c (1 - τ) = 3840891135209 / (10¹⁵ · 2³⁸)'),
        ('theorem tot_kappa_eq : totKappa = 3001011855209 / (10 ^ 15 * 2 ^ 38) := by',
         'theorem tot_kappa_eq : totKappa = 3840891135209 / (10 ^ 15 * 2 ^ 38) := by'),
    ],
    'IntegerMultBounds/MathlibTM2/Theorem.lean': [
        ("`ε (1-λ')` rounded down, with `ε = 31/64` and `1-λ' = 9680682 · 10^-11` just below\n"
         "`1-τ = 96806834039 · 10^-15`, about `2^-14.38`.",
         "`ε (1-λ')` rounded down, with `ε = 31/64` and `1-λ' = 12389970 · 10^-11` just below\n"
         "`1-τ = 123899714039 · 10^-15`, about `2^-14.02`."),
    ],
    'IntegerMultBounds/Machine/BinaryRadixEqualShared.lean': [
        ('τ₂ = 1 - 96806834039/10¹⁵', 'τ₂ = 1 - 123899714039/10¹⁵'),
    ],
}

# Files whose every saving literal is the saving of the cost chain.
KAPPA_FILES = [
    'IntegerMultBounds/MathlibTM2/Theorem.lean',
    'IntegerMultBounds/MathlibTM2/Fast/CompactFinalR.lean',
    'IntegerMultBounds/MathlibTM2/Fast/CompactMainDispatch.lean',
    'IntegerMultBounds/MathlibTM2/DFT/DFTCheck.lean',
    'CompletedProofCheck.lean',
]

changes = {}
for rel, pairs in EDITS.items():
    p = ROOT / rel
    t = p.read_text()
    for old, new in pairs:
        n = t.count(old)
        if n != 1 and t.count(new) == 1:
            continue  # already applied
        if n != 1:
            sys.exit(f'{rel}: expected one occurrence of {old!r}, found {n}')
        t = t.replace(old, new)
    changes[p] = t
for rel in KAPPA_FILES:
    p = ROOT / rel
    t = changes.get(p, p.read_text())
    t = t.replace(f'{KAPPA_OLD} / 2 ^ 46', f'{KAPPA_NEW} / 2 ^ 46').replace(f'{KAPPA_OLD}/2^46', f'{KAPPA_NEW}/2^46')
    t = t.replace(f'{KAPPA_OLD} · 2^-46', f'{KAPPA_NEW} · 2^-46')
    changes[p] = t

for p, t in changes.items():
    old = p.read_text()
    n = sum(1 for a, b in zip(old.split('\n'), t.split('\n')) if a != b)
    print(f'{p.relative_to(ROOT)}: {n} lines')
    if not DRY and old != t:
        p.write_text(t)
left = [str(p.relative_to(ROOT)) for p, t in changes.items() if KAPPA_OLD in t]
if left:
    print(f'{KAPPA_OLD} remains in:', ', '.join(left))
print('dry run' if DRY else 'applied')
