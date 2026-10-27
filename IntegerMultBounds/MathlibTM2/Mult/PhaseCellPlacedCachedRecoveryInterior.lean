module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRecoveryInteriorOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedRestoredCouplingPass
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

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 256 Q A U}

noncomputable def placedCachedRecoveryInterior (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 256 Q A U :=
  .seq placedAmbientSourceRetire (.seq (placedCachedRestoredCouplingPass recovery hQ true) (placedInitializedInterior hR hQ))

def placedCachedRecoveryInteriorCost (p l s t u target rhsExp boundaryExp countExp a b : ℕ) [NeZero s] : ℕ :=
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp
  retireAmbientSourceCost q s+(placedCachedRestoredCouplingPassCost true (2^15*p) q s t u (PhaseCellBand.width p u) a b
    (couplingCoefficientPage (2^15*p) q s t u (PhaseCellBand.width p u) a b s).length+
    initializedInteriorCost p l s t u target (recoveryRhsExponent p rhsExp boundaryExp countExp) a b)

theorem placedCachedRecoveryInterior_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 256 Q A U) (S : Stacks 256 A) (residual tail sourceTail pageTail : List (Fin (A+4)))
    (hresidual : residual.length = s*executionWidth p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (residual++(cstream A (executionWidth p l
        (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail)) (embStk couplingSourceReg S))
    (haMaster : ((embStk couplingSourceReg S).R 141).length = a) (hbMaster : ((embStk couplingSourceReg S).R 142).length = b)
    (hsource : (embStk couplingSourceReg S).R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : (embStk couplingSourceReg S).R 127 = []) (h138 : (embStk couplingSourceReg S).R 138 = []) (h143 : (embStk couplingSourceReg S).R 143 = [])
    (hcache : CouplingPageCacheReady recovery (2^15*p)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      s t u (PhaseCellBand.width p u) a b pageTail S) :
    let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    let cExp := recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u)
    let R := couplingRowField (2^15*p) q t u band a b true C B
    ∃ v' n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧ n ≤ placedCachedRecoveryInteriorCost p l s t u target rhsExp boundaryExp (couplingCountExponent p u) a b ∧
      Exec body (placedCachedRecoveryInterior recovery hR hQ) (mk v S) n
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
  obtain ⟨hq,hstage,hw⟩ := recovery_execution_sizes p l target rhsExp boundaryExp countExp
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hθ0 : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity) hθ
  let : NeZero t := ⟨by omega⟩
  have hdom := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hAI := SchurDominance.dominates_mono _ Finset.univ (haloInterior s t band a b) _
    (Finset.subset_univ _) hdom
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  obtain ⟨xI,hxI⟩ := SchurDominance.solves_exists _ (haloInterior s t band a b) _ hμ hAI
    (fun i => (value q (R i)).re)
  have hwq : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  let original := cstream A w (chirpLine s B)++tail
  let S₀ : Stacks 256 A := {S with R := Function.update S.R 110 original}
  have hqS : (S.R 119).length = q := by
    change ((embStk couplingSourceReg S).R 119).length = q
    simpa [groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hsS : (S.R 121).length = s := by
    change ((embStk couplingSourceReg S).R 121).length = s
    simpa [groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hproj₀ : embStk couplingSourceReg S₀ = {embStk couplingSourceReg S with R :=
      (Function.update (embStk couplingSourceReg S).R 110 original)} :=
    embStk_updateR_inner couplingSourceReg couplingSourceReg_injective S 110 original
  obtain ⟨v₀,n₀,hu₀,hn₀,he₀⟩ := placedAmbientSourceRetire_exec (body := body)
    q s residual original v S
    hqS hsS
    hready.source (by simpa only [hwq] using hresidual)
    (hready.blank 94 (by decide) (by decide) (by decide))
    (hready.fresh 131 (by simp)) (hready.fresh 134 (by simp)) (hready.fresh 135 (by simp))
  have hready₀ : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp+1)
      q l s t u band 0 0 original (embStk couplingSourceReg S₀) := by
    rw [hproj₀]; exact hready.update_source original
  have hreadyq : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp+1)
      q l s t u band 0 0 (cstream A (2*q+8) (chirpLine s B)++tail) (embStk couplingSourceReg S₀) := by
    rw [hwq]
    exact hready₀
  have hsourceq : S₀.R 132 = cstream A (2*q+8) (chirpLine s C)++sourceTail := by
    rw [hwq]
    change (embStk couplingSourceReg S₀).R 132 = _
    rw [hproj₀]; simpa using hsource
  have hcache₀ : CouplingPageCacheReady recovery (2^15*p) q (2*q+8) s t u band a b pageTail S₀ := by
    rw [hwq]
    apply hcache.of_frame
    intro i
    have hi := couplingCachePort_ge recovery i
    have hne : couplingCachePort recovery i ≠ (110 : Fin 256) := by
      intro h; have := congrArg Fin.val h; omega
    simp [S₀,hne]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hready₁,hRnorm,hRerror⟩ := placedCachedRestoredCouplingPass_spec (body := body)
    (q := q) (N := executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp+1)
    (l := l)
    recovery hQ hA hp0 hst hαu hθ0 hgap hbudget (recovery_coupling_width p l target rhsExp boundaryExp countExp)
    has hbs hband rfl C B x (fun i => (value q (B i)).re) 2 ε 0 hε hcount hB hC hxB hmass
    (by intro i; simp) tail sourceTail pageTail v₀ S₀ hreadyq
    (by rw [hproj₀]; simpa using haMaster)
    (by rw [hproj₀]; simpa using hbMaster) hsourceq
    (by rw [hproj₀]; simpa using h143) hcache₀
  simp only [hwq] at he₁ hready₁
  let S₁ : Stacks 256 A := {S₀ with R := Function.update S₀.R 110 (cstream A w (chirpLine s R)++S₀.R 110)}
  have hproj₁ : embStk couplingSourceReg S₁ = {embStk couplingSourceReg S₀ with R :=
      (Function.update (embStk couplingSourceReg S₀).R 110 (cstream A w (chirpLine s R)++S₀.R 110))} :=
    embStk_updateR_inner couplingSourceReg couplingSourceReg_injective S₀ 110 _
  have hready₁' : LengthKeyReady (2^15*p) (executionStagePrecision p l target cExp+1)
      (executionPrecision p l target cExp) l s t u band 0 0
      (cstream A (executionWidth p l target cExp) (chirpLine s R)++S₀.R 110) (embStk couplingSourceReg S₁) := by
    simpa only [S₁,R,q,w,band,cExp,hq,hstage,hw] using hready₁
  obtain ⟨v₂,n₂,D,hu₂,hn₂,hlen,he₂,hDnorm,hDerror⟩ := placedInitializedInterior_spec (body := body)
    hR hQ hA hp0 hst hu hαu hθ0 hgap hbudget hband has hbs hpad R
    (by simpa only [R,q,band,cExp,hq,recoveryRhsExponent] using hRnorm) xI
    (by simpa only [R,q,band,cExp,hq] using hxI) v₁ S₁ (S₀.R 110)
    (by rw [hproj₁,hproj₀]; simpa using h127) (by rw [hproj₁,hproj₀]; simpa using h138)
    (by rw [hproj₁,hproj₀]; simpa using haMaster) (by rw [hproj₁,hproj₀]; simpa using hbMaster) hready₁'
  have hcore : PhaseCellInterface.ErrorOn (haloInterior s t band a b)
      (fun i => (value q (D i)).re) x
      (1/(2 : ℝ)^target+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
        (2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε)) := by
    have hDerror' : PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (fun i => (value q (D i)).re) xI (1/(2 : ℝ)^target) := by
      simpa only [q,cExp,hq] using hDerror
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

  refine ⟨v₂,n₀+(n₁+n₂),D,hu₂.trans (hu₁.trans hu₀),Nat.add_le_add hn₀ (Nat.add_le_add hn₁ hn₂),
    (Exec.seq he₀ (Exec.seq he₁ he₂)).cast rfl ?_,hRnorm,?_,hcore,?_,?_⟩
  · apply congrArg (mk v₂)
    have hw' : executionWidth p l target cExp = w := hw.symm
    simp only [S₁,hw']
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk110 : k = 110 <;> by_cases hk132 : k = 132 <;>
      simp [S₀,original,hk110,hk132,q,w,R,band,countExp]

  · simpa only [q,cExp,hq,countExp] using hDnorm
  · rw [← haloInterior_union_boundary s t band a b]
    exact hcore.union_ite (by
      intro i hi
      simpa only [Real.norm_eq_abs] using hxB i hi)
  · simpa only [Bool.true_eq_false,ite_true,add_zero] using hRerror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
