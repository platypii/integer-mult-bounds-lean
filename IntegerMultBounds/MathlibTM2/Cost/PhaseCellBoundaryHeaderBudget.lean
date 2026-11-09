module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBoundaryHeaderLoad
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith

/-! Boundary header copying and eventual retirement fit ambient source traffic.
Only ordinary master lengths and the binary-ruler width enter the bound. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A s : ℕ}

def boundaryHeaderVolume (words : Fin 11 → List (Fin (A+4))) : ℕ :=
  ((List.ofFn words).map List.length).sum

theorem boundarySeamHeaderVolume_le_traffic {p width W D N : ℕ}
    {seedValue : Fin 117 → ℕ} {words : Fin 11 → List (Fin (A+4))}
    (h : BoundarySeamHeaderWords (s := s) p width W D N seedValue words)
    (cD : ℕ) (hs : 1 ≤ s) (hN : 1 ≤ N) (hW : 2*p+13 ≤ W) (hD : D ≤ cD*p) :
    boundaryHeaderVolume words ≤ 11*((cD+1)*(N*(s*W))) := by
  let traffic := N*(s*W)
  have hWone : 1 ≤ W := by omega
  have hline : s ≤ traffic := (Nat.le_mul_of_pos_right s hWone).trans (Nat.le_mul_of_pos_left _ hN)
  have hwide : W ≤ traffic := (Nat.le_mul_of_pos_left W hs).trans (Nat.le_mul_of_pos_left _ hN)
  have hclock : N ≤ traffic := Nat.le_mul_of_pos_right N (Nat.mul_le_mul hs hWone)
  have hword : 2*p+13 ≤ traffic := hW.trans hwide
  have hp : p ≤ traffic := by omega
  have hscale : traffic ≤ (cD+1)*traffic := Nat.le_mul_of_pos_left _ (by omega)
  have hruler : D ≤ (cD+1)*traffic := by nlinarith only [hD,Nat.mul_le_mul_left cD hp]
  have hseeds (j : Fin 3) : (words (boundarySeamSeedMaster j)).length ≤ (cD+1)*traffic := by
    rw [h.seeds,length_binSyms]
    exact hruler
  have hcrops (slot : Fin 3) : (words (boundarySeamCropMaster slot)).length ≤ (cD+1)*traffic := by
    rw [h.crops]
    have hcore : coreLength s width (boundaryCropIndex s width slot) ≤ s :=
      (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
    exact ((Nat.mul_le_mul hcore hW).trans (Nat.le_mul_of_pos_left _ hN)).trans hscale
  have hbound (i : Fin 11) : (words i).length ≤ (cD+1)*traffic := by
    fin_cases i
    · exact h.clock.le.trans (hclock.trans hscale)
    · exact h.line.le.trans (hline.trans hscale)
    · exact h.wide.le.trans (hwide.trans hscale)
    · exact h.word.le.trans (hword.trans hscale)
    · exact hseeds 0
    · exact hseeds 1
    · exact hseeds 2
    · exact h.ruler.le.trans hruler
    · exact hcrops 0
    · exact hcrops 1
    · exact hcrops 2
  have hb := List.sum_le_length_nsmul ((List.ofFn words).map List.length) ((cD+1)*traffic) (by
    intro n hn
    obtain ⟨word,hw,rfl⟩ := List.mem_map.mp hn
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hbound i)
  simpa only [boundaryHeaderVolume,List.length_map,List.length_ofFn,Nat.nsmul_eq_mul] using hb

theorem boundaryHeaderLifecycleCosts_le (volume traffic cD : ℕ)
    (hvolume : volume ≤ 11*((cD+1)*traffic)) (htraffic : 1 ≤ traffic) :
    (6*volume+67)+(2*volume+23) ≤ (300+150*cD)*traffic ∧
      2*(6*volume+67) ≤ (300+150*cD)*traffic := by
  constructor <;> nlinarith only [hvolume,htraffic]

theorem placedBoundaryHeaderLoad_exec_within_traffic {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (e : Fin 117 → Fin T) (he : Function.Injective e)
    (masters : Fin 11 → Fin T)
    (hsep : ∀ i, ∀ r ∈ List.ofFn boundarySeamMasterRole++[27,28], masters i ≠ e r)
    (p width W D N cD : ℕ) (seedValue : Fin 117 → ℕ)
    (hs : 1 ≤ s) (hN : 1 ≤ N) (hW : 2*p+13 ≤ W) (hD : D ≤ cD*p)
    (v : HS T Q A U) (S : Stacks T A)
    (hwords : BoundarySeamHeaderWords (s := s) p width W D N seedValue (fun i => S.R (masters i)))
    (hblank : ∀ i, i.val < 63 → i ≠ 95 → i ≠ 96 → S.R (e i) = []) (depth : ℕ) :
    let F : Stacks T A := {S with R := copyWordHeadersR S.R (placedBoundaryHeaderPairs e masters) S.R}
    let headers := List.ofFn (fun i => e (boundarySeamMasterRole i))
    let clearCost := 2*(headers.map (fun i => (F.R i).length)).sum+23
    ∃ v' n, v'.user = v.user ∧ n+clearCost ≤ (300+150*cD)*(N*(s*W)) ∧
      BoundarySeamReady (s := s) p width W D N boundarySeamCropCount seedValue (embStk e F) ∧
      (∀ i, (∀ j, e (boundarySeamMasterRole j) ≠ i) → F.R i = S.R i) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (300+150*cD)*(N*(s*W))) depth (placedBoundaryHeaderLoad e masters)
        (Host.mk v S) n (Host.mk v' F) := by
  dsimp only
  obtain ⟨v',hu,ready,hget,hframe,hex⟩ := placedBoundaryHeaderLoad_exec_within body e he masters hsep
    p width W D N seedValue v S hwords hblank depth
  have hcost : ((placedBoundaryHeaderPairs e masters).map (fun r => 6*(S.R r.1).length+6)).sum+1 =
      6*boundaryHeaderVolume (fun i => S.R (masters i))+67 := by
    simp only [placedBoundaryHeaderPairs,List.map_ofFn,boundaryHeaderVolume,Function.comp_def,List.sum_ofFn,
      Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      Nat.nsmul_eq_mul]
  have hgetR (i : Fin 11) : copyWordHeadersR S.R (placedBoundaryHeaderPairs e masters) S.R
      (e (boundarySeamMasterRole i)) = S.R (masters i) := hget i
  have hclear : 2*((List.ofFn (fun i => e (boundarySeamMasterRole i))).map
      (fun i => (({S with R := copyWordHeadersR S.R (placedBoundaryHeaderPairs e masters) S.R} : Stacks T A).R i).length)).sum+23 =
      2*boundaryHeaderVolume (fun i => S.R (masters i))+23 := by
    simp only [List.map_ofFn,boundaryHeaderVolume,Function.comp_def,hgetR]
  have hvol := boundarySeamHeaderVolume_le_traffic hwords cD hs hN hW hD
  have htraffic : 1 ≤ N*(s*W) := Nat.mul_le_mul hN (Nat.mul_le_mul hs (show 1 ≤ W by omega))
  obtain ⟨ht,hspace⟩ := boundaryHeaderLifecycleCosts_le _ _ cD hvol htraffic
  refine ⟨v',((placedBoundaryHeaderPairs e masters).map (fun r => 6*(S.R r.1).length+6)).sum+1,hu,?_,ready,hframe,?_⟩
  · rw [hcost,hclear]
    exact ht
  · rw [hcost] at hex ⊢
    exact hex.mono (by intro z state hz; omega)

end IntegerMultBounds.MathlibTM2.Cost
