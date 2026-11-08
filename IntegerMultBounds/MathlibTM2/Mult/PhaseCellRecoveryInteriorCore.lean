module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireAmbientSource
public import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.SchurRecoveryError
public import IntegerMultBounds.NLogN.SchurPerturbSolve
public import IntegerMultBounds.NLogN.PhaseCellCouplingMass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Execute the recovery coupling and interior solve independently of the surrounding principal system. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def recoveryInteriorCore (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (restoredCouplingPass hQ true) (initializedInterior hR hQ)

def recoveryInteriorCoreCost (p l s t u target rhsExp boundaryExp countExp a b : ℕ) : ℕ :=
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp
  restoredCouplingPassCost true (2^15*p) q s t u (PhaseCellBand.width p u) a b+
    initializedInteriorCost p l s t u target (recoveryRhsExponent p rhsExp boundaryExp countExp) a b

theorem recoveryInteriorCore_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp boundaryExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ‖value (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (C i)‖ ≤ (2 : ℝ)^boundaryExp)
    (v : HS 144 Q A U) (S : Stacks 144 A) (tail sourceTail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l
        (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (chirpLine s B)++tail) S)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hsource : S.R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) :
    let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let cExp := recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u)
    let R := couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b true C B
    ∃ v' n, ∃ D : ZMod s → GaussianInt, ∃ xI : ZMod s → ℝ,
      v'.user = v.user ∧ n ≤ recoveryInteriorCoreCost p l s t u target rhsExp boundaryExp (couplingCountExponent p u) a b ∧
      Exec (embTab groupReg body) (recoveryInteriorCore hR hQ) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R 110 (cstream A w (chirpLine s R)++S.R 110))
          132 (cstream A w (chirpLine s D)++S.R 132))}) ∧
      (∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^cExp) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target cExp) ∧
      SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) xI
        (fun i => (value q (R i)).re) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t (PhaseCellBand.width p u) a b)
        (fun i => (value q (D i)).re) xI (1/(2 : ℝ)^target) := by
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
  have hreadyq : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp+1)
      q l s t u band 0 0 (cstream A (2*q+8) (chirpLine s B)++tail) S := by
    rw [hwq]
    exact hready
  have hsourceq : S.R 132 = cstream A (2*q+8) (chirpLine s C)++sourceTail := by
    rw [hwq]
    exact hsource
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hready₁,hRnorm,hRerror⟩ := restoredCouplingPass_spec (body := body)
    (q := q) (N := executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp+1)
    (l := l)
    hQ hA hp0 hst hαu hθ0 hgap hbudget (recovery_coupling_width p l target rhsExp boundaryExp countExp)
    has hbs hband rfl C B (fun i => (value q (C i)).re) (fun i => (value q (B i)).re) 2 0 0 (by positivity) hcount hB hC (by intro i hi; simp) hmass
    (by intro i; simp) tail sourceTail v S hreadyq (by simpa [] using haMaster)
    (by simpa [] using hbMaster) hsourceq (by simpa [] using h143)
  simp only [hwq] at he₁ hready₁
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 110 (cstream A w (chirpLine s R)++S.R 110)}
  have hready₁' : LengthKeyReady (2^15*p) (executionStagePrecision p l target cExp+1)
      (executionPrecision p l target cExp) l s t u band 0 0
      (cstream A (executionWidth p l target cExp) (chirpLine s R)++S.R 110) S₁ := by
    simpa only [S₁,R,q,w,band,cExp,hq,hstage,hw] using hready₁
  obtain ⟨v₂,n₂,D,hu₂,hn₂,hlen,he₂,hDnorm,hDerror⟩ := initializedInterior_spec (body := body)
    hR hQ hA hp0 hst hu hαu hθ0 hgap hbudget hband has hbs hpad R
    (by simpa only [R,q,band,cExp,hq,recoveryRhsExponent] using hRnorm) xI
    (by simpa only [R,q,band,cExp,hq] using hxI) v₁ S₁ (S.R 110)
    (by simpa [S₁] using h127) (by simpa [S₁] using h138)
    (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster) hready₁'
  refine ⟨v₂,n₁+n₂,D,xI,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁ he₂).cast rfl ?_,hRnorm,?_,hxI,?_⟩
  · apply congrArg (mk v₂)
    have hw' : executionWidth p l target cExp = w := hw.symm
    simp only [S₁,hw']
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk110 : k = 110 <;> by_cases hk132 : k = 132 <;>
      simp [hk110,hk132,q,w,R,band,countExp]
  · simpa only [q,cExp,hq,countExp] using hDnorm
  · simpa only [q,cExp,hq,countExp] using hDerror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
