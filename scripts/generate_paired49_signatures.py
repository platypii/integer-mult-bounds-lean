#!/usr/bin/env python3
"""Generate untrusted vertex summaries, checked against each literal DAG row.

The upstream circuit is used only to emit data. Lean independently checks the
pair source endpoints, each core intersection and vertex union, and bank rows.
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
        parser.error('chunk size must be positive and match the existing Data chunks')
    sys.path.insert(0, str(args.upstream.resolve()))
    from paired_exclusion_circuit import PairedExclusionCircuit
    circuit = PairedExclusionCircuit(49)
    active = sorted(circuit.active)
    pair_inputs = [(a, b) for a in range(49) for b in range(a + 1, 49)]
    cores, unions = {}, {}
    for old in active:
        parents = circuit.args[old]
        if parents is None:
            a, b = pair_inputs[old - 1]
            cores[old] = unions[old] = (1 << a) | (1 << b)
        else:
            left, right = parents
            cores[old] = cores[left] & cores[right]
            unions[old] = unions[left] | unions[right]
    summaries = [(cores[old], unions[old]) for old in active]
    namespace = 'IntegerMultBounds.Networks.Certificates.Paired49'
    header = ('/-! Generated untrusted endpoint signatures. Checked by accompanying Lean proofs.\n'
              'Regenerate with scripts/generate_paired49_signatures.py. -/\n')
    lines = [f'import {namespace}.Data', 'import IntegerMultBounds.Networks.MaskSignature',
             'import IntegerMultBounds.Networks.PairMask', '', header, f'namespace {namespace}',
             'open MaskDAG MaskSignature', 'set_option maxRecDepth 4096', '',
             '/-- Actual source endpoints in the canonical pair-input order. -/',
             'def signatureSource (i : Fin 1176) : BitVec 49 :=',
             '  PairMask.bit 49 (PairMask.pairAt49 i).1 ||| PairMask.bit 49 (PairMask.pairAt49 i).2', '',
             '/-- The endpoint set is specified independently of mask arithmetic. -/',
             'def signaturePayload (i : Fin 1176) : Finset (Fin 49) :=',
             '  Finset.univ.filter (fun v => v.val = (PairMask.pairAt49 i).1 ∨ v.val = (PairMask.pairAt49 i).2)', '',
             'theorem signatureSource_decode (i : Fin 1176) : decode (signatureSource i) = signaturePayload i := by',
             '  rw [signatureSource, decode_or]', '  ext v',
             '  simp only [Finset.mem_union, PairMask.mem_bit, signaturePayload, Finset.mem_filter, Finset.mem_univ, true_and]', '']
    for i, (core, union) in enumerate(summaries):
        lines += [f'def signatureCore{i:05d} : BitVec 49 := BitVec.ofNat 49 {core}',
                  f'def signatureUnion{i:05d} : BitVec 49 := BitVec.ofNat 49 {union}']
    chunks = [(start, min(start + args.chunk_size, len(active)))
              for start in range(0, len(active), args.chunk_size)]
    def tree(prefix: str, lo: int, hi: int) -> str:
        if lo == hi:
            return '.empty'
        if hi == lo + 1:
            return f'(.leaf {prefix}{lo:05d})'
        mid = (lo + hi) // 2
        return f'(.branch {mid-lo}\n{tree(prefix,lo,mid)}\n{tree(prefix,mid,hi)})'
    for field in ['Core', 'Union']:
        for n, (lo, hi) in enumerate(chunks):
            lines.append(f'def signature{field}Block{n:03d} : Bank 49 :=\n{tree("signature"+field,lo,hi)}\n')
        def upper(lo: int, hi: int) -> str:
            if hi == lo + 1:
                return f'signature{field}Block{lo:03d}'
            mid = (lo + hi) // 2
            pivot = sum(end - start for start, end in chunks[lo:mid])
            return f'(.branch {pivot} {upper(lo,mid)} {upper(mid,hi)})'
        lines.append(f'def signature{field}Bank : Bank 49 :=\n{upper(0,len(chunks))}\n')
    for n, (lo, hi) in enumerate(chunks):
        lines += [f'def signatures{n:03d} : List (Signature 49) := [',
                  ',\n'.join(f'  ⟨signatureCore{i:05d}, signatureUnion{i:05d}⟩' for i in range(lo,hi)), ']\n']
    lines += ['def signatures : List (Signature 49) :=\n  ' + ' ++\n  '.join(f'signatures{n:03d}' for n in range(len(chunks))),
              '', f'end {namespace}', '']
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'SignaturesData.lean').write_text('\n'.join(lines))
    empty_pred = '(fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core == 0)'
    nonempty_pred = '(fun row => match row.1.kind with | .input _ => false | .add _ _ => row.2.core != 0)'
    for n, (lo, hi) in enumerate(chunks):
        empty_count = sum(circuit.args[old] is not None and cores[old] == 0 for old in active[lo:hi])
        nonempty_count = sum(circuit.args[old] is not None and cores[old] != 0 for old in active[lo:hi])
        lines = [f'import {namespace}.SignaturesData']
        if n >= 4:
            lines.append(f'import {namespace}.SignaturesChunk{n-4:03d}')
        lines += ['', header, f'namespace {namespace}', 'open MaskSignature',
                  'set_option maxRecDepth 4096', '',
                  f'theorem signatures{n:03d}_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup {lo}',
                  f'    chunk{n:03d} signatures{n:03d} = true := by', '  decide +kernel', '',
                  f'theorem signatures{n:03d}_length : signatures{n:03d}.length = {hi-lo} := by rfl', '',
                  f'theorem signatures{n:03d}_empty_core_additions : (chunk{n:03d}.zip signatures{n:03d}).countP {empty_pred} = {empty_count} := by',
                  '  decide +kernel', '',
                  f'theorem signatures{n:03d}_nonempty_core_additions : (chunk{n:03d}.zip signatures{n:03d}).countP {nonempty_pred} = {nonempty_count} := by',
                  '  decide +kernel', '',
                  f'end {namespace}', '']
        (args.output / f'SignaturesChunk{n:03d}.lean').write_text('\n'.join(lines))
    lines = [f'import {namespace}.SignaturesChunk{n:03d}' for n in range(len(chunks))]
    lines += ['', header, f'namespace {namespace}', 'open MaskSignature', 'set_option maxRecDepth 32768', 'set_option maxHeartbeats 2000000', '',
              'theorem signatures_checked : checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup 0',
              '    entries signatures = true := by', '  unfold entries signatures', '  simp only [List.append_assoc]']
    for n, (lo, _) in enumerate(chunks[:-1]):
        rest = ' ++ '.join(f'chunk{k:03d}' for k in range(n+1, len(chunks)))
        restS = ' ++ '.join(f'signatures{k:03d}' for k in range(n+1, len(chunks)))
        lines += [f'  refine checkChunk_append_of signatureSource signatureCoreBank.lookup signatureUnionBank.lookup {lo}',
                  f'    chunk{n:03d} ({rest}) signatures{n:03d} ({restS}) signatures{n:03d}_checked ?_',
                  f'  change checkChunk signatureSource signatureCoreBank.lookup signatureUnionBank.lookup {chunks[n+1][0]}',
                  f'    ({rest}) ({restS}) = true']
    lines += [f'  exact signatures{len(chunks)-1:03d}_checked', '',
              '/-- Every actual node has the exact common and covered endpoint sets. -/',
              'theorem signatures_correct (hv : MaskDAG.checkChunk bank.lookup 0 entries = true) :',
              '    List.Forall₂ (Correct signaturePayload) entries signatures ∧',
              '      Meaning signaturePayload signatureCoreBank.lookup signatureUnionBank.lookup',
              '        (entries.map (fun e => MaskDAG.decode e.mask)) :=',
              '  checkChunk_correct signaturePayload signatureSource signatureSource_decode bank.lookup',
              '    signatureCoreBank.lookup signatureUnionBank.lookup entries signatures hv signatures_checked', '',
              'theorem signature_banks_correct (hv : MaskDAG.checkChunk bank.lookup 0 entries = true)',
              '    (i : ℕ) (hi : i < entries.length) :',
              '    (signatureCoreBank.lookup i).map MaskDAG.decode = (bank.lookup i).map (fun m => core signaturePayload (MaskDAG.decode m)) ∧',
              '      (signatureUnionBank.lookup i).map MaskDAG.decode = (bank.lookup i).map (fun m => union signaturePayload (MaskDAG.decode m)) :=',
              '  bank_correct signaturePayload signatureSource signatureSource_decode bank.lookup',
              '    signatureCoreBank.lookup signatureUnionBank.lookup entries signatures hv signatures_checked i hi', '',
              ]
    for name, pred, total in [('empty', empty_pred, 4389), ('nonempty', nonempty_pred, 5424)]:
        lines += [f'theorem {name}_core_addition_count : (entries.zip signatures).countP {pred} = {total} := by',
                  '  unfold entries signatures', '  simp only [List.append_assoc]']
        for n in range(len(chunks)-1):
            lines.append(f'  rw [List.zip_append (show chunk{n:03d}.length = signatures{n:03d}.length from rfl)]')
        lines.append('  simp only [List.countP_append]')
        lines.append('  decide +kernel')
        lines += ['']
    lines += [f'end {namespace}', '']
    (args.output / 'Signatures.lean').write_text('\n'.join(lines))
    additions = [old for old in active if circuit.args[old] is not None]
    empty = sum(cores[old] == 0 for old in additions)
    singleton = sum(cores[old].bit_count() == 1 for old in additions)
    print(f'Emitted {len(active)} signatures in {len(chunks)} chunks; additions: empty core {empty}, singleton core {singleton}.')


if __name__ == '__main__':
    main()
