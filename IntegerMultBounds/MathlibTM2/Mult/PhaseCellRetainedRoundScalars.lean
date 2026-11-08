module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRetainedRound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundDimensions

/-! Install the rounding view from retained p and q, independently of solver geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem prepareRetainedRoundScalars_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    {B p q : ℕ} (wl : List (Fin (A+4))) (hwl : wl.length = B) (st : TblSt 25 A)
    (hp : st.val 0 = p) (hq : st.val 18 = q)
    (hselectionRoom : 8*(p+2) < 2^B) (hwidthRoom : 2*q+8 < 2^B)
    (hfit : ∀ i, st.val i < 2^B)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho B wl [] st)) :
    ∃ v' F m z, v'.user = v.user ∧ m ≤ (4*Nat.size (4*p)+31)*tblC B 0 ∧
      Exec body (tblCompile rg tblPrepareRetainedRound) (mk v S) m (mk v' F) ∧
      tblHolds rg F (tblRho B wl [] z) ∧
      tblHolds (rg ∘ TblR.rename inverseRoundVariables) F
        (tblRho B wl [] (z.restrict inverseRoundVariables)) ∧
      (z.restrict inverseRoundVariables).val = ![2*q+8,q,p,inverseNormalizationShift p,p+8,0,0,0] ∧
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.acc = st.acc ∧ (∀ i, z.val i < 2^B) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, (∀ r, rg r ≠ i) → F.R i = S.R i) := by
  have hc := tblPrepareRetainedRound_do (e := 0) st hp hq hselectionRoom hwidthRoom hfit
  obtain ⟨z,⟨hkeep,hqZ,hw,hmag,hshift,h15,h16,h17,hacc,hfitZ⟩,hrun⟩ :=
    hc.host (body := body) hrg wl [] hwl rfl (Nat.zero_le B) hfit
  obtain ⟨v',F,m,hu,hm,hexec,hh,hframe⟩ := hrun v S hS
  refine ⟨v',F,m,z,hu,by simpa only [List.length_nil] using hm,hexec,hh,?_,?_,
    hkeep,hacc,hfitZ,hframe⟩
  · exact tblHolds_restrict inverseRoundVariables rg B wl [] z F hh
  · funext i
    fin_cases i
    · exact hw
    · exact hqZ
    · exact (hkeep 0).trans hp
    · exact hshift
    · exact hmag
    · exact h15
    · exact h16
    · exact h17

/-- The cyclic solver uses this precision at target+1; its cardinality is arbitrary. -/
theorem cyclicRound_dimensions (p u l target rowCount : ℕ) :
    let q := executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 rowCount) 2) 2
    p ≤ q ∧ 1 ≤ 2*q+8 ∧ q-p+inverseNormalizationShift p+(2*p+13) ≤ 2*q+8 := by
  dsimp only
  rw [show executionPrecision p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 rowCount) 2) 2 =
      4*inverseExecutionExponent p l target rowCount (PhaseCellBand.width p u) by
    rw [inverseExecutionExponent_eq]; rfl]
  have h := inverse_round_dimensions p l target rowCount (PhaseCellBand.width p u)
    (inverseNormalizationShift p) (inverseNormalizationShift_le p)
  dsimp only at h
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
