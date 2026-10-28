module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareInverseRoundExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedInverseRound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClearInverseScalars

/-! Closed final normalization in the inverse's existing 303-register workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

def inverseRoundBatch : Pr P 303 Q A U :=
  .seq (tblCompile familyInverseScalarReg tblPrepareInverseRound)
    (.seq (generatedFinalRound inverseRoundScalarReg inverseRoundPorts 132 4 5 6 7 8)
      (tblCompile familyInverseScalarReg tblClearInverseScalars))

noncomputable def inverseRoundBatchCost (W p u l target s t a b count : ℕ) [NeZero s] : ℕ :=
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  (inverseScalarAtoms p s t u a b+4*Nat.size (4*p)+52)*tblC W 0+
    16*(8*E+8)+44*W+38+count*(14*(8*E+8)+23)

theorem inverseRoundBatch_exec (hA : 4 ≤ A) {W p u l target s t a b : ℕ} [NeZero s]
    (wl : List (Fin (A+4))) (hwl : wl.length = W) (st : TblSt 25 A)
    (h0 : st.val 0 = p) (h1 : st.val 1 = u) (h2 : st.val 2 = l) (h3 : st.val 3 = target)
    (h4 : st.val 4 = s) (h5 : st.val 5 = t) (h6 : st.val 6 = a) (h7 : st.val 7 = b)
    (hzero : ∀ i : Fin 25, 8 ≤ i.val → st.val i = 0)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W) (hfit : ∀ i, st.val i < 2^W)
    (xs : List GaussianInt) (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds familyInverseScalarReg S (tblRho W wl [] st))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8] : List (Fin 303)), S.R r = []) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let q := 4*E
    let j := inverseNormalizationShift p
    S.R 132 = cstream A w xs →
    ∃ v' n, v'.user = v.user ∧ n ≤ inverseRoundBatchCost W p u l target s t a b xs.length ∧
      Exec body inverseRoundBatch (mk v S) n
        (mk v' {S with R := (Function.update S.R 132 (cstream A (2*p+13) (xs.map (finalRoundWord w q p j))))}) := by
  dsimp only
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let w := 8*E+8
  let q := 4*E
  let j := inverseNormalizationShift p
  intro hsrc
  obtain ⟨v₁,S₁,n₁,z,hu₁,hn₁,he₁,hh₁,hview,hval,hkeep,hacc,hfitZ,hi₁,ho₁,hL₁,hcore⟩ :=
    prepareInverseRound_exec (body := body) wl hwl st h0 h1 h2 h3 h4 h5 h6 h7 hst haS hbS hbandS
      hbandRoom hgeometryRoom hprecisionRoom hfit v S hS
  have hv (i : Fin 8) := congrFun hval i
  have hdim := inverse_round_dimensions p l target
    (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u) j (inverseNormalizationShift_le p)
  have hwroom : w < 2^W := by
    have hh := hv 0
    change z.val 20 = w at hh
    rw [←hh]
    exact hfitZ 20
  have hsmall (r : Fin 303) (hr : r ∈ ([0,1,2,3,4,5,6,7,8] : List (Fin 303))) : S₁.R r = [] := by
    have hlo : r.val < 224 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    let k : Fin 263 := ⟨r.val,by omega⟩
    have hk : familyInverseCoreReg k = r := by apply Fin.ext; simp [familyInverseCoreReg,k,hlo]
    rw [←hk,hcore,hk]
    exact hblank r hr
  have hsource₁ : S₁.R 132 = cstream A w xs := (hcore 132).trans hsrc
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := placedInverseRound_exec (body := body)
    (w := w) (q := q) (p := p) (j := j) (E := p+8) hA wl hwl
    (z.restrict inverseRoundVariables) hval hdim.1 (by dsimp [w]; omega) hdim.2.2 hwroom
    (fun i => hfitZ (inverseRoundVariables i)) xs v₁ S₁ hview hsource₁ hsmall
  let output := cstream A (p+(p+8)+5) (xs.map (finalRoundWord w q p j))
  let S₂ : Stacks 303 A := {S₁ with R := Function.update S₁.R 132 output}
  have hneq (r : TblR 25) : familyInverseScalarReg r ≠ (132 : Fin 303) := familyInverseScalarReg_core r 132
  have hh₂ : tblHolds familyInverseScalarReg S₂ (tblRho W wl [] z) := by
    intro r
    simpa only [S₂,Function.update_of_ne (hneq r)] using hh₁ r
  have hc := tblClearInverseScalars_do (W := W) (e := 0) z st
    (fun i hi => hkeep ⟨i.val,hi⟩) hzero hacc
  obtain ⟨initial,heq,hrun⟩ := hc.host (body := body) familyInverseScalarReg_injective wl [] hwl rfl (Nat.zero_le W) hfitZ
  subst initial
  obtain ⟨v₃,S₃,n₃,hu₃,hn₃,he₃,hh₃,hframe₃⟩ := hrun v₂ S₂ hh₂
  have hoff₁ (r : Fin 303) (hr : ∀ k, familyInverseScalarReg k ≠ r) : S₁.R r = S.R r := by
    rcases familyInverseCallerReg_cover r with ⟨i,rfl⟩ | ⟨k,hk⟩
    · exact hcore i
    · exact False.elim (hr k hk)
  have hfinal : S₃ = {S with R := Function.update S.R 132 output} := by
    apply Stacks.ext
    · exact hframe₃.1.trans hi₁
    · exact hframe₃.2.1.trans ho₁
    · exact hframe₃.2.2.1.trans hL₁
    funext r
    by_cases hr : ∃ k, familyInverseScalarReg k = r
    · obtain ⟨k,rfl⟩ := hr
      change S₃.R (familyInverseScalarReg k) = Function.update S.R 132 output (familyInverseScalarReg k)
      rw [Function.update_of_ne (hneq k)]
      exact (hh₃ k).trans (hS k).symm
    · have hoff : ∀ k, familyInverseScalarReg k ≠ r := by simpa using hr
      rw [hframe₃.2.2.2 r hoff]
      by_cases he : r = 132
      · subst r
        change Function.update S₁.R 132 output 132 = Function.update S.R 132 output 132
        simp only [Function.update_self]
      · change Function.update S₁.R 132 output r = Function.update S.R 132 output r
        rw [Function.update_of_ne he,Function.update_of_ne he,hoff₁ r hoff]
  have he := (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk v₃) hfinal)
  have hout : p+(p+8)+5 = 2*p+13 := by omega
  refine ⟨v₃,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,?_⟩
  · simp only [List.length_nil] at hn₃
    dsimp [inverseRoundBatchCost]
    dsimp [w,E] at hn₂
    nlinarith only [hn₁,hn₂,hn₃]
  · simpa only [output,hout,inverseRoundBatch,w,q,j,E] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
