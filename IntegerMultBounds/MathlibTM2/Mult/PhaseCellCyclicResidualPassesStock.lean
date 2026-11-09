module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualPasses
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowedSchurResidualStock

/-! Both guarded residual intervals retain their executed resources. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def cyclicResidualPassesWorkspace
    (J ringPush batchPush rowPush p l s t u target rhsExp a n : ℕ) : ℕ :=
  windowedSchurResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u target rhsExp a (a+min n (s-a))+
  windowedSchurResidualWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J ringPush batchPush rowPush p l s t u target rhsExp 0 (n-min n (s-a))

theorem cyclicResidualPasses_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a n : ℕ} [NeZero s] {alpha d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (halpha : 0 < alpha) (hst : s < t) (hu : 1 ≤ u)
    (hsquare : alpha^2 = (u : ℝ)) (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : alpha^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a < s) (hn : n ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (J ringPush batchPush : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ ringPush)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ batchPush)
    (rowPush : ℕ) (hrowPush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ rowPush)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail : List (Fin (A+4)))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ [(127 : Fin 148),138,141,142,143,147], S.R k = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg S)) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    ∃ v' m, ∃ C D : ZMod s → GaussianInt, ∃ R T : (ZMod s → ℝ) → ZMod s → ℝ,
      let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
      let S' : Stacks 148 A := {S with R := Function.update S.R 132 output}
      (∀ rhs, SchurDominance.Solves (realMatrix s t p u)
        (cyclicPrincipalInterior s t band a n)
        (fun k => if k ∈ haloInterior s t band a (a+min n (s-a)) then R rhs k else T rhs k) rhs) ∧
      v'.user = v.user ∧ m ≤ windowedSchurResidualCost p l s t u target rhsExp a (a+min n (s-a))+
        windowedSchurResidualCost p l s t u target rhsExp 0 (n-min n (s-a)) ∧
      ExecWithin (embTab componentReg (embTab groupReg body))
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          cyclicResidualPassesWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
            J ringPush batchPush rowPush p l s t u target rhsExp a n)
        0 (cyclicResidualPasses hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0 ∧ (D i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
        ‖value q (D i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ cyclicPrincipalBoundary s t band a n,
        |(if i ∈ haloVertices s a (a+min n (s-a)) then (value q (C i)).re else (value q (D i)).re)-
          SchurDominance.residual (realMatrix s t p u) (cyclicPrincipalInterior s t band a n)
            (fun rhs k => if k ∈ haloInterior s t band a (a+min n (s-a)) then R rhs k else T rhs k)
            (fun k => (value q (B k)).re) i| ≤ (1/(2 : ℝ)^(recoveryTarget p target+2))/(8*(p : ℝ))) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
        q l s t u band 0 0 (S.R 110) (embStk componentReg S') := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
  let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
  let band := PhaseCellBand.width p u
  obtain ⟨v₁,m₁,C,R,hRsolve,hv₁,hm₁,he₁,hrealC,hnormC,herrC,hready₁⟩ := windowedSchurResidual_spec_within (body := body) (a := a) (b := a+min n (s-a))
    hR hQ hA 144 145 (by decide) hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha.le (by omega) hpad B hB J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush v S tail
    (hfresh 127 (by simp)) (hfresh 138 (by simp)) (hfresh 143 (by simp)) haSrc hleftEnd
    (hfresh 141 (by simp)) (hfresh 142 (by simp)) hready (hfresh 147 (by simp))
  let F : Stacks 148 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s C)++S.R 132)}
  have hsource : S.R 110 = cstream A w (chirpLine s B)++tail := by simpa [embStk,componentReg,w] using hready.source
  have hreadyF : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      q l s t u band 0 0 (cstream A w (chirpLine s B)++tail) (embStk componentReg F) := by
    simpa only [hsource] using hready₁
  obtain ⟨v₂,m₂,D,T,hT,hv₂,hm₂,he₂,hrealD,hnormD,herrD,hready₂⟩ := windowedSchurResidual_spec_within (body := body) (a := 0) (b := n-min n (s-a))
    hR hQ hA 138 146 (by decide) hp hwidth halpha hst hu hsquare htheta hgap hbudget hband (by omega) (by omega) hpad B hB J ringPush batchPush hpushJ hpushR hpushK rowPush hrowPush v₁ F tail
    (by simpa [F] using hfresh 127 (by simp)) (by simpa [F] using hfresh 138 (by simp))
    (by simpa [F] using hfresh 143 (by simp)) (by simp [F,hfresh 138 (by simp)])
    (by simpa [F] using hrightEnd) (by simpa [F] using hfresh 141 (by simp))
    (by simpa [F] using hfresh 142 (by simp)) hreadyF (by simpa [F] using hfresh 147 (by simp))
  refine ⟨v₂,m₁+m₂,C,D,R,T,cyclicPrincipalInterior_solver p u a n ha hn R T hRsolve hT,
    hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,?_,fun i => ⟨hrealC i,hrealD i⟩,
    fun i => ⟨hnormC i,hnormD i⟩,?_,?_⟩
  · have ht := (mn_seq_within_add he₁ he₂).mono (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        cyclicResidualPassesWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
          J ringPush batchPush rowPush p l s t u target rhsExp a n) (by
      intro d z hz
      unfold cyclicResidualPassesWorkspace
      exact hz)
    exact ht.cast rfl (by simp only [F,w,Function.update_self,Function.update_idem])
  · have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    apply cyclicPrincipal_residual_pieces_error p u a n ha hn R T
      (fun k => (value q (B k)).re) (fun k => (value q (C k)).re) (fun k => (value q (D k)).re)
    all_goals intro i hi
    all_goals apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(p : ℝ))).mpr
    · simpa only [mul_comm] using herrC i hi
    · simpa only [mul_comm] using herrD i hi
  · simpa [F] using hready₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
