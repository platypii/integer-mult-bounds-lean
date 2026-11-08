module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryInteriorCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireAmbientSource
public import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.SchurRecoveryError
public import IntegerMultBounds.NLogN.SchurPerturbSolve
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Execute boundary coupling and the second interior pass with the shared first-pass precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def recoveryInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq retireAmbientSource (.seq (restoredCouplingPass hQ true) (initializedInterior hR hQ))

def recoveryInteriorCost (p l s t u target rhsExp boundaryExp countExp a b : ℕ) : ℕ :=
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp
  retireAmbientSourceCost q s+(restoredCouplingPassCost true (2^15*p) q s t u (PhaseCellBand.width p u) a b+
    initializedInteriorCost p l s t u target (recoveryRhsExponent p rhsExp boundaryExp countExp) a b)

theorem recoveryInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp boundaryExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C B : ZMod s → GaussianInt) (x : ZMod s → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ‖value (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (C i)‖ ≤ (2 : ℝ)^boundaryExp)
    (hxB : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |(value (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (C i)).re-x i| ≤ ε)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x
      (fun i => (value (executionPrecision p l
        (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (residual tail sourceTail : List (Fin (A+4)))
    (hresidual : residual.length = s*executionWidth p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (residual++(cstream A (executionWidth p l
        (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail)) S)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hsource : S.R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) :
    let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    let cExp := recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u)
    let R := couplingRowField (2^15*p) q t u band a b true C B
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ recoveryInteriorCost p l s t u target rhsExp boundaryExp (couplingCountExponent p u) a b ∧
      Exec (embTab groupReg body) (recoveryInterior hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 110 (cstream A w (chirpLine s R)++(cstream A w (chirpLine s B)++tail)))
          132 (cstream A w (chirpLine s D)++S.R 132))}) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^cExp) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target cExp) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun i => (value q (D i)).re) x
        (1/(2 : ℝ)^target+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
          (2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε)) ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (SchurDominance.glue (haloInterior s t band a b)
          (fun i => (value q (D i)).re) (fun i => (value q (C i)).re)) x
        (max (1/(2 : ℝ)^target+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
          (2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε)) ε) ∧
      ∀ i, |(value q (R i)).re-((value q (B i)).re-
        SchurDominance.couple (realMatrix s t p u) (haloBoundary s t band a b) x i)| ≤
          (2*band+1)*(2/(2 : ℝ)^q)+(2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε := by
  dsimp only
  let countExp := couplingCountExponent p u
  have hcount := couplingCountExponent_spec p u
  have hmass := couplingOffsets_mass_le_two hst hα p u hp hwidth hαu hθ hgap hbudget
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp
  let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp
  let band := PhaseCellBand.width p u
  let cExp := recoveryRhsExponent p rhsExp boundaryExp countExp
  let R := couplingRowField (2^15*p) q t u band a b true C B
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hθ0 : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) hθ
  let : NeZero t := ⟨by omega⟩
  have hdom := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hwq : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  let original := cstream A w (chirpLine s B)++tail
  let S₀ : Stacks 144 A := {S with R := Function.update S.R 110 original}
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀⟩ := retireAmbientSource_exec (body := embTab groupReg body)
    q s residual original v S
    (by simpa [groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies]))
    (by simpa [groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies]))
    hready.source (by simpa only [hwq] using hresidual)
    (hready.blank 94 (by decide) (by decide) (by decide))
    (hready.fresh 131 (by simp)) (hready.fresh 134 (by simp)) (hready.fresh 135 (by simp))
  have hready₀ : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp+1)
      q l s t u band 0 0 original S₀ := hready.update_source original
  obtain ⟨v₂,n₂,D,xI,hu₂,hn₂,he₂,hRnorm,hDnorm,hxI,hDerror⟩ := recoveryInteriorCore_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad C B hB hC
    v₀ S₀ tail sourceTail hready₀ (by simpa [S₀] using haMaster) (by simpa [S₀] using hbMaster)
    (by simpa [S₀] using hsource) (by simpa [S₀] using h127) (by simpa [S₀] using h138)
    (by simpa [S₀] using h143)
  have hRerror := couplingRowField_error (A := A) true hA hp0 hst hαu hθ0 hgap hbudget
    (recovery_coupling_width p l target rhsExp boundaryExp countExp) C B x
    (fun i => (value q (B i)).re) 2 ε 0 hε hcount hB hC hxB hmass (by intro i; simp [q])
  have hcore : PhaseCellInterface.ErrorOn (haloInterior s t band a b)
      (fun i => (value q (D i)).re) x
      (1/(2 : ℝ)^target+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
        (2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε)) := by
    have hDerror' : PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun i => (value q (D i)).re) xI (1/(2 : ℝ)^target) := by
      exact hDerror
    have hfull : SchurDominance.Solves (realMatrix s t p u)
        (haloInterior s t band a b ∪ haloBoundary s t band a b) x (fun i => (value q (B i)).re) := by
      rw [haloInterior_union_boundary]
      exact hx
    let E := (2*band+1)*(2/(2 : ℝ)^q)+
      (2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε
    have hRerror' : ∀ i ∈ haloInterior s t band a b,
        |(value q (R i)).re-((value q (B i)).re-
          SchurDominance.couple (realMatrix s t p u) (haloBoundary s t band a b) x i)| ≤ E := by
      intro i hi
      simpa only [Bool.true_eq_false,ite_true,add_zero] using hRerror i
    have herror := SchurDominance.recovery_solves_error _ _ _
      (haloInterior_disjoint_boundary s t band a b) _ hμ
      (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) hdom)
      x (fun i => (value q (B i)).re) xI (fun i => (value q (R i)).re) hfull hxI E hRerror'
    intro i hi
    have hh := herror i hi
    rw [div_div_eq_mul_div,div_one] at hh
    have hd := hDerror' i hi
    rw [Real.norm_eq_abs] at hd ⊢
    have ht := abs_add_le ((value q (D i)).re-xI i) (xI i-x i)
    dsimp only [E] at hh
    rw [sub_add_sub_cancel] at ht
    nlinarith only [hh,hd,ht]

  refine ⟨v₂,n₀+n₂,D,hu₂.trans hu₀,Nat.add_le_add hn₀ hn₂,
    (Exec.seq he₀ he₂).cast rfl ?_,hRnorm,?_,hcore,?_,?_⟩
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk110 : k = 110 <;> by_cases hk132 : k = 132 <;>
      simp [S₀,original,hk110,hk132,w,countExp]

  · exact hDnorm
  · rw [← haloInterior_union_boundary s t band a b]
    exact hcore.union_ite (by
      intro i hi
      simpa only [Real.norm_eq_abs] using hxB i hi)
  · simpa only [Bool.true_eq_false,ite_true,add_zero] using hRerror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
