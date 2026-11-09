module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolveHaloInteriorStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloKeyWorkspaceBound

import Mathlib.Tactic.Ring

/-! Generated halo keys use the manuscript's common cell-length bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem generatedHaloKeysWorkspace_le_uniform
    (J R K p l s t u target rhsExp V a b : ℕ)
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) :
    let band := PhaseCellBand.width p u
    haloLengthKeyLoopWorkspace J R K p l s t u target rhsExp V a b
      (haloLengthKeys s t band a b) ≤
      haloKeySharedSetup J R K p l s t u target rhsExp ((s/(t-s)+1)-2*band)+
        haloKeyAuxWorkspace R K p l s t u target rhsExp V := by
  apply haloLengthKeyLoopWorkspace_le_uniform
    J R K p l s t u target rhsExp V a b _ _ ha hb
  intro L hL
  have hc : L ∈ haloLengthCandidates s t (PhaseCellBand.width p u) a b :=
    List.mem_dedup.mp (List.mem_filter.mp hL).1
  have h := haloLengthCandidates_uniform hst (PhaseCellBand.width p u) a b hc
  have hdiv := Nat.div_le_self s (t-s)
  have hband := PhaseCellBand.width_pos p u
  exact ⟨by omega,h⟩

theorem solveHaloInteriorWorkspace_le_uniform_keys
    (J R K p l s t u target rhsExp a b : ℕ)
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) :
    let P := 2^15*p
    let N := executionStagePrecision p l target rhsExp+1
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let V := weightWorkspaceWidth P q w t u
    solveHaloInteriorWorkspace J R K p l s t u target rhsExp a b ≤
      18*initializeHaloLengthKeysCost P N q l s t u band a b+
        (haloKeySharedSetup J R K p l s t u target rhsExp ((s/(t-s)+1)-2*band)+
          haloKeyAuxWorkspace R K p l s t u target rhsExp V) := by
  unfold solveHaloInteriorWorkspace
  dsimp only
  exact Nat.add_le_add_left (generatedHaloKeysWorkspace_le_uniform
    J R K p l s t u target rhsExp _ a b hst ha hb) _

theorem initializeHaloLengthKeysCost_le_volume (P N q l s t u band a b : ℕ) :
    let V := weightWorkspaceWidth P q (2*q+8) t u
    initializeHaloLengthKeysCost P N q l s t u band a b ≤
      200*tblC V V+10000*(P+N+q+l+s+t+u+band+a+b+1)*(V+q+1) := by
  have hcount := haloLengthKeys_length_le s t band a b
  have hvolume := Nat.mul_le_mul_right (weightWorkspaceWidth P q (2*q+8) t u) hcount
  dsimp only
  unfold initializeHaloLengthKeysCost installHaloGroupHeadersCost installGroupHeadersCost
    prepareHaloLengthKeysCost preparedHaloLengthCandidatesCost haloHeadersCost weightWidthCost
  dsimp only
  ring_nf at hvolume ⊢
  omega

theorem solveHaloInteriorWorkspace_le_components
    (J R K p l s t u target rhsExp a b : ℕ)
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) :
    let P := 2^15*p
    let N := executionStagePrecision p l target rhsExp+1
    let q := executionPrecision p l target rhsExp
    let band := PhaseCellBand.width p u
    let V := weightWorkspaceWidth P q (2*q+8) t u
    solveHaloInteriorWorkspace J R K p l s t u target rhsExp a b ≤
      18*(200*tblC V V+10000*(P+N+q+l+s+t+u+band+a+b+1)*(V+q+1))+
        (haloKeySharedSetup J R K p l s t u target rhsExp ((s/(t-s)+1)-2*band)+
          haloKeyAuxWorkspace R K p l s t u target rhsExp V) := by
  unfold solveHaloInteriorWorkspace
  dsimp only
  have hwidth : executionWidth p l target rhsExp = 2*executionPrecision p l target rhsExp+8 := by
    simp only [executionWidth,executionPrecision]
    omega
  rw [hwidth]
  exact Nat.add_le_add (Nat.mul_le_mul_left 18 (initializeHaloLengthKeysCost_le_volume _ _ _ _ _ _ _ _ _ _))
    (generatedHaloKeysWorkspace_le_uniform J R K p l s t u target rhsExp _ a b hst ha hb)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
