#!/usr/bin/env python3
"""Emit untrusted duplicate witnesses for fifty copies of the paired circuit.

Lean checks every local addition ID and every lifted common/covered-vertex
signature equality. Sorted row keys are checked to certify distinct witnesses.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import sys


def pair(a: int, b: int) -> int:
    return b*b+a if a < b else a*a+a+b


def key(row: tuple[int, int, int, int]) -> int:
    c, left, d, right = row
    return pair(c, pair(left, pair(d, right)))


def bit_lift(c: int, mask: int) -> int:
    return (mask & ((1 << c)-1)) | ((mask >> c) << (c+1)) | (1 << c)


def appended(names: list[str]) -> str:
    result = names[-1]
    for name in reversed(names[:-1]):
        result = f'{name} ++ ({result})'
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, default=Path('integer-mult-bounds/scripts'))
    parser.add_argument('--output', type=Path, default=Path('IntegerMultBounds/Networks/Certificates/Shared50'))
    parser.add_argument('--chunk-size', type=int, default=128)
    args = parser.parse_args()
    if args.chunk_size <= 0:
        parser.error('chunk size must be positive')
    sys.path.insert(0, str(args.upstream.resolve()))
    from paired_exclusion_circuit import PairedExclusionCircuit
    circuit = PairedExclusionCircuit(49)
    active = sorted(circuit.active)
    pair_inputs = [(a,b) for a in range(49) for b in range(a+1,49)]
    cores, unions = {}, {}
    for old in active:
        parents = circuit.args[old]
        if parents is None:
            a,b = pair_inputs[old-1]
            cores[old] = unions[old] = (1<<a)|(1<<b)
        else:
            a,b = parents
            cores[old] = cores[a] & cores[b]
            unions[old] = unions[a] | unions[b]
    seen = {}
    rows = []
    for common in range(50):
        for index, old in enumerate(active):
            if circuit.args[old] is None or cores[old] == 0:
                continue
            signature = (bit_lift(common,cores[old]),bit_lift(common,unions[old]))
            if signature in seen:
                earlier, left = seen[signature]
                assert earlier < common
                rows.append((earlier,left,common,index))
            else:
                seen[signature] = (common,index)
    rows.sort(key=key)
    assert len(rows) == 40256
    assert len(set(rows)) == len(rows)
    assert all(key(a) < key(b) for a,b in zip(rows,rows[1:]))
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    ns = 'IntegerMultBounds.Networks.Certificates.Shared50'
    paired = 'IntegerMultBounds.Networks.Certificates.Paired49'
    header = ('/-! Generated untrusted duplicate witnesses. Lean checks IDs, signature equality and uniqueness.\n'
              'Regenerate with scripts/generate_shared50_witnesses.py. -/\n')
    chunks = [(lo,min(lo+args.chunk_size,len(rows))) for lo in range(0,len(rows),args.chunk_size)]
    lines = [f'import {paired}.SignaturesData', 'import IntegerMultBounds.Networks.SharedPointWitnessCheck',
             '',header,f'namespace {ns}', 'open SharedPointWitnessCheck', 'set_option maxRecDepth 8192', '',
             '/-- The actual local addition interval; its classification is checked separately. -/',
             'def isAddition (i : ℕ) : Bool := decide (1176 ≤ i ∧ i < 10989)', '']
    lines += [f'def point{i:02d} : Fin 50 := ⟨{i}, by decide⟩' for i in range(50)] + ['']
    for n,(lo,hi) in enumerate(chunks):
        lines += [f'def chunk{n:03d} : List (Witness 49) := [',
                  ',\n'.join(f'  ((point{c:02d}, {a}), (point{d:02d}, {b}))' for c,a,d,b in rows[lo:hi]),']\n']
    lines += ['def rows : List (Witness 49) :=\n  '+appended([f'chunk{n:03d}' for n in range(len(chunks))]), '',
              f'end {ns}', '']
    (out/'Data.lean').write_text('\n'.join(lines))
    for n,(lo,hi) in enumerate(chunks):
        previous = 'none' if lo == 0 else f'(some {key(rows[lo-1])})'
        lines = [f'import {ns}.Data']
        if n >= 4:
            lines.append(f'import {ns}.Chunk{n-4:03d}')
        lines += ['',header,f'namespace {ns}', 'open SharedPointWitnessCheck',
                  'set_option maxRecDepth 8192', '',
                  f'theorem chunk{n:03d}_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup',
                  f'    {previous} chunk{n:03d} = true := by', '  decide +kernel', '',
                  f'theorem chunk{n:03d}_last : lastKey {previous} chunk{n:03d} = some {key(rows[hi-1])} := by',
                  '  decide +kernel', '',
                  f'theorem chunk{n:03d}_length : chunk{n:03d}.length = {hi-lo} := by rfl', '',
                  f'end {ns}', '']
        (out/f'Chunk{n:03d}.lean').write_text('\n'.join(lines))
    lines = [f'import {ns}.Chunk{n:03d}' for n in range(len(chunks))]
    lines += ['',header,f'namespace {ns}', 'open SharedPointWitnessCheck',
              'set_option maxRecDepth 32768', 'set_option maxHeartbeats 4000000', '',
              'attribute [local irreducible] Paired49.signatureCoreBank Paired49.signatureUnionBank isAddition',
              'attribute [local irreducible] ' + ' '.join(f'chunk{n:03d}' for n in range(len(chunks))), '',
              'theorem rows_checked : checkFrom isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup none rows = true := by',
              '  unfold rows']
    for n,(lo,_) in enumerate(chunks[:-1]):
        previous = 'none' if lo == 0 else f'(some {key(rows[lo-1])})'
        rest = appended([f'chunk{k:03d}' for k in range(n+1,len(chunks))])
        lines += [f'  refine checkFrom_append_of isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup {previous}',
                  f'    chunk{n:03d} ({rest}) chunk{n:03d}_checked ?_', f'  rw [chunk{n:03d}_last]']
    lines += [f'  exact chunk{len(chunks)-1:03d}_checked', '',
              'theorem rows_length : rows.length = 40256 := by', '  unfold rows',
              '  simp only [List.length_append, ' + ', '.join(f'chunk{n:03d}_length' for n in range(len(chunks))) + ']', '',
              'theorem rows_nodup : rows.Nodup :=',
              '  checkFrom_nodup isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup none rows rows_checked', '',
              'def witnesses := rows.toFinset', '',
              'theorem witnesses_card : witnesses.card = 40256 := by',
              '  rw [witnesses, List.toFinset_card_of_nodup rows_nodup, rows_length]', '',
              f'end {ns}', '']
    (out/'Checked.lean').write_text('\n'.join(lines))
    # Classification chunks align with the independently generated paired DAG.
    local_chunks = [(lo,min(lo+128,len(active))) for lo in range(0,len(active),128)]
    lines = [f'import {paired}.Data', 'import IntegerMultBounds.Networks.SharedPointWitnessCheck', '',header,f'namespace {ns}', 'open SharedPointWitnessCheck',
             'set_option maxRecDepth 8192', 'set_option maxHeartbeats 2000000', '']
    for n,(lo,_) in enumerate(local_chunks):
        lines += [f'theorem kind{n:03d}_checked : checkKinds 1176 {lo} Paired49.chunk{n:03d} = true := by',
                  '  decide +kernel', '']
    lines += ['theorem kinds_checked : checkKinds 1176 0 Paired49.entries = true := by',
              '  unfold Paired49.entries', '  simp only [List.append_assoc]']
    for n,(lo,_) in enumerate(local_chunks[:-1]):
        rest = appended([f'Paired49.chunk{k:03d}' for k in range(n+1,len(local_chunks))])
        lines += [f'  refine checkKinds_append_of 1176 {lo} Paired49.chunk{n:03d} ({rest}) kind{n:03d}_checked ?_',
                  f'  change checkKinds 1176 {local_chunks[n+1][0]} ({rest}) = true']
    lines += [f'  exact kind{len(local_chunks)-1:03d}_checked', '', f'end {ns}', '']
    (out/'Kinds.lean').write_text('\n'.join(lines))
    print(f'Emitted {len(rows)} strictly sorted duplicate witnesses in {len(chunks)} chunks.')


if __name__ == '__main__':
    main()
