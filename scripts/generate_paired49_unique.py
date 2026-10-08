#!/usr/bin/env python3
"""Generate a sorted-mask witness; Lean verifies ordering, coverage and uniqueness."""
from __future__ import annotations
import argparse
from pathlib import Path
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, default=Path('integer-mult-bounds/scripts'))
    parser.add_argument('--output', type=Path, default=Path('IntegerMultBounds/Networks/Certificates/Paired49'))
    args = parser.parse_args()
    sys.path.insert(0, str(args.upstream.resolve()))
    from paired_exclusion_circuit import PairedExclusionCircuit
    circuit = PairedExclusionCircuit(49)
    masks = [circuit.support[old] for old in sorted(circuit.active)]
    order = sorted(range(len(masks)), key=masks.__getitem__)
    ns = 'IntegerMultBounds.Networks.Certificates.Paired49'
    lines = [f'import {ns}.Checked', 'import IntegerMultBounds.Networks.MaskUnique', '',
             '/-! Untrusted sorted mask positions, checked in the ordinary kernel.\n'
             'Regenerate with scripts/generate_paired49_unique.py. -/', '',
             f'namespace {ns}', 'open MaskDAG MaskUnique', '']
    chunks = []
    previous = '0'
    for start in range(0, len(order), 128):
        name = f'uniqueChunk{len(chunks):03d}'
        ids = order[start:start+128]
        next_value = f'mask{ids[-1]:05d}.toNat'
        chunks.append(name)
        lines += [f'def {name} : List (Row 1176) := [',
                  ',\n'.join(f'  ({i}, mask{i:05d})' for i in ids), ']', '',
                  f'theorem {name}_checked : checkSorted bank.lookup 10989 ({previous}) {name} = true := by',
                  '  decide +kernel', '',
                  f'theorem {name}_last : lastValue ({previous}) {name} = {next_value} := by rfl',
                  f'theorem {name}_length : {name}.length = {len(ids)} := by rfl', '']
        previous = next_value
    def right_append(names):
        result = names[-1]
        for name in reversed(names[:-1]):
            result = name + ' ++ (' + result + ')'
        return result
    lines += ['attribute [local irreducible] MaskUnique.checkSorted ' + ' '.join(chunks), '', 'def uniqueRows : List (Row 1176) :=', '  ' + right_append(chunks), '',
              'theorem uniqueRows_checked : checkSorted bank.lookup 10989 0 uniqueRows = true := by',
              '  unfold uniqueRows']
    previous = "0"
    for k, name in enumerate(chunks[:-1]):
        rest = right_append(chunks[k+1:])
        lines += [f'  refine checkSorted_append_of bank.lookup 10989 ({previous}) {name} ({rest}) {name}_checked ?_',
                  f'  rw [{name}_last]']
        previous = f'mask{order[(k+1)*128-1]:05d}.toNat'
    lines += [f'  exact {chunks[-1]}_checked', '',
              'theorem uniqueRows_length : uniqueRows.length = 10989 := by',
              '  simp only [uniqueRows, List.length_append, ' + ', '.join(c+'_length' for c in chunks) + ']', '',
              'theorem bank_injective : ∀ i < 10989, ∀ j < 10989, bank.lookup i = bank.lookup j → i = j :=',
              '  checked_bank_injective bank.lookup 10989 uniqueRows uniqueRows_checked uniqueRows_length', '',
              'theorem masks_nodup (accepted : checkChunk bank.lookup 0 entries = true)',
              '    (hlen : entries.length = 10989) : (entries.map Entry.mask).Nodup := by',
              '  apply entries_masks_nodup bank.lookup entries accepted',
              '  simpa only [hlen] using bank_injective', '',
              'theorem supports_nodup (accepted : checkChunk bank.lookup 0 entries = true)',
              '    (hlen : entries.length = 10989) :',
              '    ((entries.map Entry.toNode).map DisjointCircuit.Node.support).Nodup := by',
              '  apply entries_supports_nodup bank.lookup entries accepted',
              '  simpa only [hlen] using bank_injective', '',
              'theorem masks_nodup_certified : (entries.map Entry.mask).Nodup :=',
              '  masks_nodup entries_checked entries_length', '',
              'theorem supports_nodup_certified :',
              '    ((entries.map Entry.toNode).map DisjointCircuit.Node.support).Nodup :=',
              '  supports_nodup entries_checked entries_length', '',
              f'end {ns}', '']
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'Unique.lean').write_text('\n'.join(lines))


if __name__ == '__main__':
    main()
