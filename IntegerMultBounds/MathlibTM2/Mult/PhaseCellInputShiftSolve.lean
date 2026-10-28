module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDerivedInputShiftBatch
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDerivedInverseRoundBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseBatchCaller

/-! Compose exact input conversion and restoration around a solver, including its stock certificate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

def inputShiftSolve (solve : Pr P 303 Q A U) : Pr P 303 Q A U :=
  .seq (inputShiftBatch false) (.seq solve (inputShiftBatch true))

theorem inputShiftSolve_exec_trace (hA : 4 ≤ A) {p u l target s t a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (wl : List (Fin (A+4))) (hwl : wl.length = inverseCallerWordWidth p u l target s t)
    (xs : List GaussianInt) (hxs : ∀ z ∈ xs, ‖value p z‖ ≤ 1)
    (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds familyInverseScalarReg S
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10] : List (Fin 303)), S.R r = [])
    (solve : Pr P 303 Q A U) (bound stockBound : ℕ) (post : List (Fin (A+4)) → Prop) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let d := 4*E-p-1
    let shifted := {S with R := Function.update S.R 110 (cstream A w (xs.map (fun z => (2 : GaussianInt)^d*z)))}
    S.R 110 = cstream A w xs →
    (∀ v₁ : HS 303 Q A U, ∃ v₂ n output, v₂.user = v₁.user ∧ n ≤ bound ∧
      Exec body solve (mk v₁ shifted) n (mk v₂ {shifted with R := Function.update shifted.R 132 output}) ∧ post output ∧
      ∀ C, mnProgPush solve ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₁ shifted)+depth+(C+1)*stockBound)
          depth solve (mk v₁ shifted) n (mk v₂ {shifted with R := Function.update shifted.R 132 output})) →
    ∃ v' n output, v'.user = v.user ∧
      n ≤ 2*inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length+bound ∧
      Exec body (inputShiftSolve solve) (mk v S) n
        (mk v' {S with R := Function.update S.R 132 output}) ∧ post output ∧
      ∀ C, mnProgPush (inputShiftSolve solve) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(2*inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length+stockBound))
          depth (inputShiftSolve solve) (mk v S) n (mk v' {S with R := Function.update S.R 132 output}) := by
  dsimp only
  intro hsrc hsolve
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  let w := 8*E+8
  let d := 4*E-p-1
  let shifted : Stacks 303 A := {S with R := Function.update S.R 110 (cstream A w (xs.map (fun z => (2 : GaussianInt)^d*z)))}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := inputShiftBatch_derived_exec (body := body) hA false
    hst ha hb hband wl hwl xs hxs v S hS hblank hsrc
  obtain ⟨v₂,n₂,output,hu₂,hn₂,he₂,hpost,htrace⟩ := hsolve v₁
  let solved : Stacks 303 A := {shifted with R := Function.update shifted.R 132 output}
  have hscalar : tblHolds familyInverseScalarReg solved
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)) := by
    intro r
    have h110 : familyInverseScalarReg r ≠ (110 : Fin 303) := familyInverseScalarReg_core r 110
    have h132 : familyInverseScalarReg r ≠ (132 : Fin 303) := familyInverseScalarReg_core r 132
    simpa only [solved,shifted,Function.update_of_ne h110,Function.update_of_ne h132] using hS r
  have hsmall : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10] : List (Fin 303)), solved.R r = [] := by
    intro r hr
    have hne : r ≠ (110 : Fin 303) ∧ r ≠ (132 : Fin 303) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa only [solved,shifted,Function.update_of_ne hne.1,Function.update_of_ne hne.2] using hblank r hr
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := inputShiftBatch_derived_exec (body := body) hA true
    hst ha hb hband wl hwl xs hxs v₂ solved hscalar hsmall (by
      simp only [solved,shifted,inputShiftSource,ite_true,Function.update_of_ne (by decide : (110 : Fin 303) ≠ 132),Function.update_self]
      rfl)
  have hfinal : {solved with R := Function.update solved.R 110 (cstream A w xs)} =
      {S with R := Function.update S.R 132 output} := by
    apply Stacks.ext <;> try rfl
    funext r
    by_cases h110 : r = 110
    · subst r
      simp only [Function.update_self,Function.update_of_ne (by decide : (110 : Fin 303) ≠ 132),hsrc]
      rfl
    · simp only [solved,shifted,Function.update_of_ne h110]
      by_cases h132 : r = 132
      · subst r; simp only [Function.update_self]
      · simp only [Function.update_of_ne h132,Function.update_of_ne h110]
  have he := (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk v₃) hfinal)
  refine ⟨v₃,n₁+(n₂+n₃),output,hu₃.trans (hu₂.trans hu₁),by omega,he,hpost,?_⟩
  intro C hpush hb depth
  have ht := mn_lifecycle_exec_within he₁ hn₁ htrace he₃ hn₃ C hpush hb depth
  have hcost : inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length+
      stockBound+inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length =
      2*inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length+stockBound := by omega
  simp only [inputShiftResult,ite_true] at ht
  have hf := hfinal
  dsimp only [w,E] at hf
  rw [hf] at ht
  simpa only [inputShiftSolve,hcost] using ht


theorem inputShiftSolve_exec (hA : 4 ≤ A) {p u l target s t a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (wl : List (Fin (A+4))) (hwl : wl.length = inverseCallerWordWidth p u l target s t)
    (xs : List GaussianInt) (hxs : ∀ z ∈ xs, ‖value p z‖ ≤ 1)
    (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds familyInverseScalarReg S
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10] : List (Fin 303)), S.R r = [])
    (solve : Pr P 303 Q A U) (bound : ℕ) (post : List (Fin (A+4)) → Prop) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let d := 4*E-p-1
    let shifted := {S with R := Function.update S.R 110 (cstream A w (xs.map (fun z => (2 : GaussianInt)^d*z)))}
    S.R 110 = cstream A w xs →
    (∀ v₁ : HS 303 Q A U, ∃ v₂ n output, v₂.user = v₁.user ∧ n ≤ bound ∧
      Exec body solve (mk v₁ shifted) n (mk v₂ {shifted with R := Function.update shifted.R 132 output}) ∧ post output) →
    ∃ v' n output, v'.user = v.user ∧
      n ≤ 2*inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length+bound ∧
      Exec body (inputShiftSolve solve) (mk v S) n
        (mk v' {S with R := Function.update S.R 132 output}) ∧ post output := by
  dsimp only
  intro hsrc hsolve
  obtain ⟨v',n,output,hu',hn,he,hpost,_⟩ := inputShiftSolve_exec_trace (body := body) hA
    hst ha hb hband wl hwl xs hxs v S hS hblank solve bound bound post hsrc (by
      intro v₁
      obtain ⟨v₂,n,output,hu₂,hn₂,he₂,hpost⟩ := hsolve v₁
      exact ⟨v₂,n,output,hu₂,hn₂,he₂,hpost,mn_bounded_exec_certify he₂ hn₂⟩)
  exact ⟨v',n,output,hu',hn,he,hpost⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
