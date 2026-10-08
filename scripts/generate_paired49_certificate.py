#!/usr/bin/env python3
"""Emit untrusted circuit data with separately kernel-checked Lean certificates.

Requires the reference checkout's paired_exclusion_circuit.py. Python output is
never evidence of correctness: Lean checks each mask, dependency and output.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, default=Path('integer-mult-bounds/scripts'))
    parser.add_argument('--output', type=Path, default=Path('IntegerMultBounds/Networks/Certificates/Paired49'))
    parser.add_argument('--chunk-size', type=int, default=128)
    args = parser.parse_args()
    if args.chunk_size <= 0:
        parser.error('chunk size must be positive')
    sys.path.insert(0, str(args.upstream.resolve()))
    from paired_exclusion_circuit import PairedExclusionCircuit
    circuit = PairedExclusionCircuit(49)
    active = sorted(circuit.active)
    index = {old: new for new, old in enumerate(active)}
    width = len(circuit.inputs)
    rows = []
    for old in active:
        parents = circuit.args[old]
        kind = (f'.input ⟨{old - 1}, by decide⟩' if parents is None else
                f'.add {index[parents[0]]} {index[parents[1]]}')
        rows.append((kind, circuit.support[old]))
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    namespace = 'IntegerMultBounds.Networks.Certificates.Paired49'
    header = ('/-! Generated untrusted mask data. Checked by the accompanying Lean proofs.\n'
              'Regenerate with scripts/generate_paired49_certificate.py. -/\n')
    lines = ['import IntegerMultBounds.Networks.MaskDAG', '', header,
             f'namespace {namespace}', 'open MaskDAG', '',
             'set_option maxRecDepth 4096', 'set_option exponentiation.threshold 2000', '']
    for i, (_, mask) in enumerate(rows):
        lines.append(f'def mask{i:05d} : BitVec {width} := BitVec.ofNat {width} {mask}')
    lines.append('')
    def tree(lo: int, hi: int) -> str:
        if lo == hi:
            return '.empty'
        if hi == lo + 1:
            return f'(.leaf mask{lo:05d})'
        mid = (lo + hi) // 2
        return f'(.branch {mid-lo}\n{tree(lo,mid)}\n{tree(mid,hi)})'
    blocks = []
    for start in range(0, len(rows), args.chunk_size):
        stop = min(start + args.chunk_size, len(rows))
        name = f'bankBlock{len(blocks):03d}'
        blocks.append((name, stop-start))
        lines.append(f'def {name} : Bank {width} :=\n{tree(start,stop)}\n')
    def upper_tree(lo: int, hi: int) -> str:
        if hi == lo + 1:
            return blocks[lo][0]
        mid = (lo+hi)//2
        pivot = sum(size for _,size in blocks[lo:mid])
        return f'(.branch {pivot} {upper_tree(lo,mid)} {upper_tree(mid,hi)})'
    lines.append(f'def bank : Bank {width} :=\n{upper_tree(0,len(blocks))}\n')
    chunks = []
    for start in range(0, len(rows), args.chunk_size):
        number = len(chunks)
        chunk = f'chunk{number:03d}'
        stop = min(start + args.chunk_size, len(rows))
        chunks.append((chunk, start, stop))
        lines.append(f'def {chunk} : List (Entry {width}) := [')
        lines.append(',\n'.join(f'  ⟨{rows[i][0]}, mask{i:05d}⟩' for i in range(start,stop)))
        lines.append(']\n')
    lines.append('def entries : List (Entry 1176) :=\n  ' + ' ++\n  '.join(c[0] for c in chunks))
    lines.append('\ndef outputs : List ((ℕ × ℕ) × ℕ) := [')
    lines.append(',\n'.join(f'  (({p[0]}, {p[1]}), {index[ref]})' for p,ref in sorted(circuit.outputs.items())))
    lines.append(']\n')
    lines.append(f'end {namespace}\n')
    (out/'Data.lean').write_text('\n'.join(lines))
    for number, (chunk,start,stop) in enumerate(chunks):
        imports = f'import {namespace}.Data\n'
        if number >= 4:
            # Keep a fresh Lake build to four concurrent certificate chains.
            imports += f'import {namespace}.Chunk{number-4:03d}\n'
        proof = (imports + f'\n{header}\nnamespace {namespace}\n'
                 'open MaskDAG\nset_option maxRecDepth 4096\n'
                 'set_option exponentiation.threshold 2000\n\n'
                 f'theorem {chunk}_checked : checkChunk bank.lookup {start} {chunk} = true := by\n'
                 '  decide +kernel\n\n'
                 f'theorem {chunk}_length : {chunk}.length = {stop-start} := by rfl\n\n'
                 f'theorem {chunk}_additions : {chunk}.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = {sum(1 for k,_ in rows[start:stop] if k.startswith(".add"))} := by decide +kernel\n\n'
                 f'end {namespace}\n')
        (out/f'Chunk{number:03d}.lean').write_text(proof)
    checked = [f'import {namespace}.Chunk{n:03d}' for n in range(len(chunks))]
    checked.extend(['', header, f'namespace {namespace}', 'open MaskDAG',
                    'set_option maxRecDepth 32768', 'set_option exponentiation.threshold 2000',
                    'attribute [local irreducible] MaskDAG.checkChunk', '',
                    'theorem entries_checked : checkChunk bank.lookup 0 entries = true := by',
                    '  unfold entries', '  simp only [List.append_assoc]'])
    for number, (chunk,start,_) in enumerate(chunks[:-1]):
        names = [c[0] for c in chunks[number+1:]]
        rest = ' ++ ('.join(names) + ')' * (len(names)-1)
        checked.extend([f'  refine checkChunk_append_of bank.lookup {start} {chunk} ({rest}) {chunk}_checked ?_',
                        f'  change checkChunk bank.lookup {chunks[number+1][1]} ({rest}) = true'])
    checked.extend([f'  exact {chunks[-1][0]}_checked', '',
                    f'theorem entries_length : entries.length = {len(rows)} := by',
                    '  decide +kernel',
                    '',
                    'theorem addition_count : entries.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true) = 9813 := by',
                    '  decide +kernel',
                    '',
                    'theorem dag_valid : DisjointCircuit.Valid (entries.map Entry.toNode) :=',
                    '  checkChunk_valid bank.lookup entries entries_checked', '',
                    f'end {namespace}', ''])
    (out/'Checked.lean').write_text('\n'.join(checked))
    print(f'Emitted {len(rows)} nodes, {len(circuit.outputs)} outputs, {len(chunks)} check chunks.')


if __name__ == '__main__':
    main()
