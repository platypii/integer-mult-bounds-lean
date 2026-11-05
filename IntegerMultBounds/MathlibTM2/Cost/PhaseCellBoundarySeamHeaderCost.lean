module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamLoadedReady
import Mathlib.Tactic.Ring

/-! Price the seam loader from its eleven-word contract, independently of the
caller state and numerical archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s p width W D N : ℕ}

def boundaryCropHeaderVolume (p s width : ℕ) : ℕ :=
  (List.ofFn (fun slot : Fin 3 => coreLength s width (boundaryCropIndex s width slot)*(2*p+13))).sum

def boundarySeamHeaderVolume (p s width W D N : ℕ) : ℕ :=
  N+s+W+(2*p+13)+4*D+boundaryCropHeaderVolume p s width

theorem boundarySeamHeaderVolume_eq (seedValue : Fin 117 → ℕ)
    (words : Fin 11 → List (Fin (A+4)))
    (h : BoundarySeamHeaderWords (s := s) p width W D N seedValue words) :
    (List.ofFn (fun i => (words i).length)).sum = boundarySeamHeaderVolume p s width W D N := by
  have hseed (j : Fin 3) : (words (boundarySeamSeedMaster j)).length = D := by
    rw [h.seeds,length_binSyms]
  norm_num [boundarySeamHeaderVolume,boundaryCropHeaderVolume,List.ofFn_succ,List.ofFn_zero,List.sum_cons,List.sum_nil,Fin.succ]
  rw [h.clock,h.line,h.wide,h.word,h.ruler,
    show (words 4).length = D from hseed 0,
    show (words 5).length = D from hseed 1,
    show (words 6).length = D from hseed 2,
    show (words 8).length = _ from h.crops 0,
    show (words 9).length = _ from h.crops 1,
    show (words 10).length = _ from h.crops 2]
  ring

theorem boundarySeamHeaderLoadCost_eq (seedValue : Fin 117 → ℕ)
    (words : Fin 11 → List (Fin (A+4)))
    (h : BoundarySeamHeaderWords (s := s) p width W D N seedValue words) :
    (List.ofFn (fun i => 6*(words i).length+6)).sum+1 =
      6*boundarySeamHeaderVolume p s width W D N+67 := by
  rw [← boundarySeamHeaderVolume_eq seedValue words h]
  simp only [List.sum_ofFn,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

theorem boundarySeamMasterCopyCosts_eq {T : ℕ} (source destination : Fin T)
    (masters : Fin 11 → Fin T) (S : Stacks (T+PackedTranspose.tapeCount) A)
    (seedValue : Fin 117 → ℕ)
    (h : BoundarySeamHeaderWords (s := s) p width W D N seedValue
      (fun i => S.R (Fin.castAdd PackedTranspose.tapeCount (masters i)))) :
    let pairs := boundarySeamMasterCopies source destination masters
    ((pairs.map (fun pair => 6*(S.R pair.1).length+6)).sum+1 =
      6*boundarySeamHeaderVolume p s width W D N+67) ∧
    (2*(pairs.map (fun pair => (S.R pair.1).length)).sum+2*pairs.length+1 =
      2*boundarySeamHeaderVolume p s width W D N+23) := by
  dsimp only
  constructor
  · simpa only [boundarySeamMasterCopies,List.map_ofFn,Function.comp_def] using
      boundarySeamHeaderLoadCost_eq seedValue _ h
  · simp only [boundarySeamMasterCopies,List.map_ofFn,Function.comp_def,List.length_ofFn]
    rw [boundarySeamHeaderVolume_eq seedValue _ h]

theorem boundarySeamHeaderVolume_le (p s width W D N : ℕ) :
    boundarySeamHeaderVolume p s width W D N ≤ N+s+W+(2*p+13)+4*D+3*s*(2*p+13) := by
  have hc (slot : Fin 3) : coreLength s width (boundaryCropIndex s width slot) ≤ s :=
    (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have hm (slot : Fin 3) := Nat.mul_le_mul_right (2*p+13) (hc slot)
  dsimp only [boundarySeamHeaderVolume,boundaryCropHeaderVolume]
  norm_num [List.ofFn_succ,List.ofFn_zero,List.sum_cons,List.sum_nil,Fin.succ]
  have h₀ := hm 0
  have h₁ := hm 1
  have h₂ := hm 2
  simp only [Nat.mul_assoc]
  omega

end IntegerMultBounds.MathlibTM2.Cost
