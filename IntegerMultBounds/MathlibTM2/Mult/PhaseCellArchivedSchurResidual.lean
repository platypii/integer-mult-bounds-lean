module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedSchurResidual
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveResidualPrefix

/-! An interval residual pass that retains its RHS for the next physical interval. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def archivedSchurResidual (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  .seq (releasedSchurResidual hR hQ) archiveResidualPrefix

theorem archivedSchurResidual_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp a b : ℕ} [NeZero s] {alpha d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (halpha : 0 < alpha) (hst : s < t) (hu : 1 ≤ u)
    (hsquare : alpha^2 = (u : ℝ)) (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : alpha^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (ha : a ≤ s) (hb : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail : List (Fin (A+4)))
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
      (executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp) (chirpLine s B)++tail) (embStk componentReg S))
    (h147 : S.R 147 = []) :
    let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
    let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
    let band := PhaseCellBand.width p u
    ∃ v' m, ∃ C : ZMod s → GaussianInt, ∃ R : (ZMod s → ℝ) → ZMod s → ℝ,
      let output := cstream A w (chirpLine s C)++S.R 132
      let S' : Stacks 148 A := {S with R := Function.update S.R 132 output}
      (∀ rhs, SchurDominance.Solves (realMatrix s t p u) (haloInterior s t band a b) (R rhs) rhs) ∧
      v'.user = v.user ∧ m ≤ releasedSchurResidualCost p l s t u target rhsExp a b+archiveResidualPrefixCost q s ∧
      Exec (embTab componentReg (embTab groupReg body)) (archivedSchurResidual hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ haloBoundary s t band a b, 8*p*|(value q (C i)).re-
        SchurDominance.residual (realMatrix s t p u) (haloInterior s t band a b) R
          (fun k => (value q (B k)).re) i| ≤ 1/(2 : ℝ)^(recoveryTarget p target+2)) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target rhsExp) rhsExp+1)
        q l s t u band 0 0 (S.R 110) (embStk componentReg S') := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u target rhsExp) rhsExp
  let w := executionWidth p l (initialSchurTarget p u target rhsExp) rhsExp
  let band := PhaseCellBand.width p u
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  obtain ⟨v₁,m₁,D,R,hRsolve,hv₁,hm₁,he₁,hreal,hnorm,herror,_,_⟩ := releasedSchurResidual_spec (body := body)
    hR hQ hA hp hwidth halpha hst hu hsquare htheta hgap hbudget hband ha hb hpad B hB v S tail
    h127 h138 h143 haMaster hbMaster hready h147
  let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let xs := cstream A w (chirpLine s C)
  let F : Stacks 148 A := {S with R := Function.update S.R 110 (xs++S.R 110)}
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue,q] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hfresh : ∀ k ∈ [(94 : Fin 148),131,134,135,147], F.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · simpa [F,embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide)
    · simpa [F,embStk,componentReg] using hready.fresh 131 (by simp)
    · simpa [F,embStk,componentReg] using hready.fresh 134 (by simp)
    · simpa [F,embStk,componentReg] using hready.fresh 135 (by simp)
    · simpa [F] using h147
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := archiveResidualPrefix_exec (body := embTab groupReg body) q s xs (S.R 110)
    (by simp [xs,chirpLine,hw]) v₁ F (by simpa [F] using hq) (by simpa [F] using hs) (by simp [F]) hfresh
  let output := xs++S.R 132
  have hfinal : {F with R := Function.update (Function.update F.R 110 (S.R 110)) 132 (xs++F.R 132)} =
      {S with R := Function.update S.R 132 output} := by
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;>
        simp [F,output,h110,h132]
  refine ⟨v₂,m₁+m₂,C,R,hRsolve,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,
    (Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) hfinal),hreal,hnorm,herror,?_⟩
  have hsource : S.R 110 = cstream A w (chirpLine s B)++tail := by
    simpa [embStk,componentReg,w] using hready.source
  have hproject := componentProject_updateR_inner S (132 : Fin 144) output
  have hc : componentReg (132 : Fin 144) = (132 : Fin 148) := by decide
  rw [hc] at hproject
  rw [hproject,hsource]
  exact hready.update_output output

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
