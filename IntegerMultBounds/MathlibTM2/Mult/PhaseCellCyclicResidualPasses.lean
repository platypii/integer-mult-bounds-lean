module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowedSchurResidual
public import IntegerMultBounds.NLogN.PhaseCellCyclicResidualPieces

/-! Execute both guarded interior residuals against the same retained RHS. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def cyclicResidualPasses (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  .seq (windowedSchurResidual hR hQ 144 145) (windowedSchurResidual hR hQ 138 146)

def windowedSchurResidualCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  (4*a+4)+((4*b+4)+(releasedSchurResidualCost p l s t u target rhsExp a b+
    archiveResidualPrefixCost (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) s+(2*(a+b)+5)))

theorem cyclicResidualPasses_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a n : ℕ} [NeZero s] {alpha d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (halpha : 0 < alpha) (hst : s < t) (hu : 1 ≤ u)
    (hsquare : alpha^2 = (u : ℝ)) (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : alpha^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a < s) (hn : n ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
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
      Exec (embTab componentReg (embTab groupReg body)) (cyclicResidualPasses hR hQ) (mk v S) m (mk v' S') ∧
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
  obtain ⟨v₁,m₁,C,R,hRsolve,hv₁,hm₁,he₁,hrealC,hnormC,herrC,hready₁⟩ := windowedSchurResidual_spec (body := body) (a := a) (b := a+min n (s-a))
    hR hQ hA 144 145 (by decide) hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha.le (by omega) hpad B hB v S tail
    (hfresh 127 (by simp)) (hfresh 138 (by simp)) (hfresh 143 (by simp)) haSrc hleftEnd
    (hfresh 141 (by simp)) (hfresh 142 (by simp)) hready (hfresh 147 (by simp))
  let F : Stacks 148 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s C)++S.R 132)}
  have hsource : S.R 110 = cstream A w (chirpLine s B)++tail := by simpa [embStk,componentReg,w] using hready.source
  have hreadyF : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      q l s t u band 0 0 (cstream A w (chirpLine s B)++tail) (embStk componentReg F) := by
    simpa only [hsource] using hready₁
  obtain ⟨v₂,m₂,D,T,hT,hv₂,hm₂,he₂,hrealD,hnormD,herrD,hready₂⟩ := windowedSchurResidual_spec (body := body) (a := 0) (b := n-min n (s-a))
    hR hQ hA 138 146 (by decide) hp hwidth halpha hst hu hsquare htheta hgap hbudget hband (by omega) (by omega) hpad B hB v₁ F tail
    (by simpa [F] using hfresh 127 (by simp)) (by simpa [F] using hfresh 138 (by simp))
    (by simpa [F] using hfresh 143 (by simp)) (by simp [F,hfresh 138 (by simp)])
    (by simpa [F] using hrightEnd) (by simpa [F] using hfresh 141 (by simp))
    (by simpa [F] using hfresh 142 (by simp)) hreadyF (by simpa [F] using hfresh 147 (by simp))
  refine ⟨v₂,m₁+m₂,C,D,R,T,cyclicPrincipalInterior_solver p u a n ha hn R T hRsolve hT,
    hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,?_,fun i => ⟨hrealC i,hrealD i⟩,
    fun i => ⟨hnormC i,hnormD i⟩,?_,?_⟩
  · exact (Exec.seq he₁ he₂).cast rfl (by simp only [F,w,Function.update_self,Function.update_idem])
  · have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    apply cyclicPrincipal_residual_pieces_error p u a n ha hn R T
      (fun k => (value q (B k)).re) (fun k => (value q (C k)).re) (fun k => (value q (D k)).re)
    all_goals intro i hi
    all_goals apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(p : ℝ))).mpr
    · simpa only [mul_comm] using herrC i hi
    · simpa only [mul_comm] using herrD i hi
  · simpa [F] using hready₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
