#!/usr/bin/env python3
"""Generate untrusted output data and ordinary-kernel proofs for Paired49.

The reference program selects data; all masks, output references and keys are
checked in Lean. No Python assertion or digest is a proof premise.
"""
from __future__ import annotations
import argparse
from itertools import combinations
from pathlib import Path
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, default=Path('integer-mult-bounds/scripts'))
    parser.add_argument('--output', type=Path, default=Path('IntegerMultBounds/Networks/Certificates/Paired49'))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    ns = 'IntegerMultBounds.Networks.Certificates.Paired49'
    pairs = list(combinations(range(49), 2))
    lines = ['import IntegerMultBounds.Networks.PairMask', '',
             '/-! Literal incident masks, checked against the canonical pair enumeration.\n'
             'Regenerate with scripts/generate_paired49_outputs.py. -/', '',
             f'namespace {ns}', 'open PairMask', '']
    for a in range(49):
        mask = sum(1 << i for i, pair in enumerate(pairs) if a in pair)
        lines += [f'def incidentMask{a:03d} : BitVec 1176 := BitVec.ofNat 1176 {mask}',
                  f'theorem incidentMask{a:03d}_checked : incident49 {a} = incidentMask{a:03d} := by',
                  '  decide +kernel', '']
    lines += ['def incidentMask : ℕ → BitVec 1176']
    lines += [f'  | {a} => incidentMask{a:03d}' for a in range(49)]
    lines += ['  | _ => 0', '',
              'theorem incidentMask_correct (a : ℕ) (ha : a < 49) : incidentMask a = incident49 a := by',
              '  interval_cases a']
    lines += [f'  · exact incidentMask{a:03d}_checked.symm' for a in range(49)]
    lines += ['', f'end {ns}', '']
    (args.output / 'Incidents.lean').write_text('\n'.join(lines))

    sys.path.insert(0, str(args.upstream.resolve()))
    from paired_exclusion_circuit import PairedExclusionCircuit
    circuit = PairedExclusionCircuit(49)
    reindex = {old: new for new, old in enumerate(sorted(circuit.active))}
    outputs = [(pair, reindex[ref]) for pair, ref in sorted(circuit.outputs.items())]
    lines = [f'import {ns}.Data', f'import {ns}.Incidents', '',
             '/-! Exact output checks for the 9813-addition local witness.\n'
             'Acceptance of the node certificate is the sole remaining premise.\n'
             'Regenerate with scripts/generate_paired49_outputs.py. -/', '',
             f'namespace {ns}', 'open MaskDAG PairMask DisjointCircuit', '',
             'def checkOutput (entry : (ℕ × ℕ) × ℕ) : Bool :=',
             '  decide (entry.1.1 < 49 ∧ entry.1.2 < 49 ∧ entry.2 < 10989) &&',
             '    decide (bank.lookup entry.2 = some (~~~incidentMask entry.1.1 &&& ~~~incidentMask entry.1.2))', '']
    chunks = []
    for start in range(0, len(outputs), 128):
        name = f'outputChunk{len(chunks):03d}'
        chunks.append(name)
        lines += [f'def {name} : List ((ℕ × ℕ) × ℕ) := [',
                  ',\n'.join(f'  (({pair[0]}, {pair[1]}), {ref})' for pair, ref in outputs[start:start+128]),
                  ']', '', f'theorem {name}_checked : {name}.all checkOutput = true := by',
                  '  decide +kernel', '']
    lines += ['theorem outputs_eq_chunks : outputs =', '  ' + ' ++\n  '.join(chunks) + ' := by',
              '  decide +kernel', '',
              'theorem outputs_checked : outputs.all checkOutput = true := by',
              '  rw [outputs_eq_chunks]',
              '  simp only [List.all_append, ' + ', '.join(c+'_checked' for c in chunks) + ', Bool.and_self]', '',
              'theorem output_keys : outputs.map Prod.fst = PairedCircuit.pairs (List.range 49) := by',
              '  decide +kernel', '',
              'theorem output_count : outputs.length = 1176 := by decide +kernel', '',
              'theorem entries_length_for_outputs : entries.length = 10989 := by decide +kernel', '',
              'theorem output_spec (entry : (ℕ × ℕ) × ℕ) (he : entry ∈ outputs) :',
              '    entry.2 < 10989 ∧ bank.lookup entry.2 = some (exclusion49 entry.1.1 entry.1.2) := by',
              '  have hc := List.all_eq_true.mp outputs_checked entry he',
              '  obtain ⟨hb, hm⟩ := Bool.and_eq_true_iff.mp hc',
              '  have hb\' : entry.1.1 < 49 ∧ entry.1.2 < 49 ∧ entry.2 < 10989 := of_decide_eq_true hb',
              '  refine ⟨hb\'.2.2, ?_⟩',
              '  have hm\' := of_decide_eq_true hm',
              '  rw [incidentMask_correct _ hb\'.1, incidentMask_correct _ hb\'.2.1] at hm\'',
              '  exact hm\'', '',
              '/-- Every designated output of the accepted finite witness is the exact',
              'canonical pair-exclusion sum over any commutative additive monoid. -/',
              'theorem accepted_output_semantics {A : Type*} [AddCommMonoid A]',
              '    (input : ℕ × ℕ → A) (accepted : checkChunk bank.lookup 0 entries = true)',
              '    (entry : (ℕ × ℕ) × ℕ) (he : entry ∈ outputs) :',
              '    (DisjointCircuit.eval (fun i => input (pairAt49 i)) (entries.map Entry.toNode))[entry.2]? =',
              '      some (supportSum input ((PairedCircuit.pairs (List.range 49)).toFinset.filter',
              '        (fun p => p.1 ∉ [entry.1.1, entry.1.2] ∧ p.2 ∉ [entry.1.1, entry.1.2]))) := by',
              '  obtain ⟨hi, hm⟩ := output_spec entry he',
              '  have hi\' : entry.2 < entries.length := by rw [entries_length_for_outputs]; exact hi',
              '  rw [checkChunk_eval_get _ bank.lookup entries accepted entry.2 hi\', hm, Option.map_some]',
              '  exact congrArg some (exclusion_sum input 49 entry.1.1 entry.1.2)', '',
              f'end {ns}', '']
    (args.output / 'Outputs.lean').write_text('\n'.join(lines))


if __name__ == '__main__':
    main()
