module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCyclicResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCyclicResidualPhysical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualPhysical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCyclicBoundaryGatherSolve

/-! Generate both physical residuals from one RHS and execute one joint boundary solve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retiredCyclicResidualSolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (generatedCyclicResidualSolve hR hQ) retireCyclicResidualPhysical

theorem retiredCyclicResidualSolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u l s t a n target : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (columns : List (ZMod s → GaussianInt)) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let bits := boundaryTableBits p target 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 24*PhaseCellBand.width p u+1
    let V := publicationGeometryWidth t (PhaseCellBand.width p u)
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    PreparedBoundaryColumns A p bits q w W B columns →
    ∀ (rhs : ZMod s → GaussianInt), (∀ i, ‖value q (rhs i)‖ ≤ (2 : ℝ)^2) →
    ∀ (v : HS 224 Q A U) (S : Stacks 224 A) (tail pageTail : List (Fin (A+4))),
    LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u (PhaseCellBand.width p u) 0 0 (cstream A w (chirpLine s rhs)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))) →
    (∀ i, S.L i = []) → (∀ i : Fin 64, S.R (boundaryFactorMulReg i) = []) →
    BoundarySolveReady (boundaryFactorState S) q w W B.card →
    S.R 223 = [] → S.R 184 = [] → S.R 220 = [] → S.R 221 = [] →
    (S.R 116).length = B.card → (S.R 115).length = V →
    S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail →
    (S.R 144).length = a → (S.R 145).length = a+min n (s-a) →
    (S.R 146).length = n-min n (s-a) →
    (∀ k ∈ [(127 : Fin 224),138,139,141,142,143,147], S.R k = []) →
    (boundaryFactorState S) .vk = [] →
    (boundaryFactorState S) .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten →
    (boundaryFactorState S) .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten →
    (boundaryFactorState S) .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) →
    ∃ v' S' steps, ∃ C D : ZMod s → GaussianInt, ∃ R T : (ZMod s → ℝ) → ZMod s → ℝ,
      let solver := fun rhs k => if k ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a)) then R rhs k else T rhs k
      let selected := fun i : ZMod s => if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i
      let solution := bandSolveVec q W (naturalLineLc q K W B.card AZ)
        (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
        (((List.range B.card).map (fun j => selected (bFoldAt s B j))).map (normalizeBoundaryWord q (q/2-1)))
      (∀ rhs, SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n) (solver rhs) rhs) ∧
      (∀ i, (C i).im = 0 ∧ (D i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) ∧
        ‖value q (D i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ B, |(value q (selected i)).re-SchurDominance.residual (realMatrix s t p u)
        (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n) solver (fun k => (value q (rhs k)).re) i| ≤
          (1/(2 : ℝ)^(recoveryTarget p bits+2))/(8*(p : ℝ))) ∧
      solution.length = B.card ∧ (∀ z ∈ solution, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1) ∧
      BoundaryUnscaleReady q S' ∧
      v'.user = v.user ∧
      steps ≤ (windowedSchurResidualCost p l s t u bits 2 a (a+min n (s-a))+
        windowedSchurResidualCost p l s t u bits 2 0 (n-min n (s-a)))+
        (cyclicBoundaryRhsPrepareCost B q V a (a+min n (s-a))+generatedBoundaryNormalizeCost q B.card+
          4*B.card*w+4*W*w+8+bandLinePassCost w B.card W)+retireCyclicResidualsCost q s ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retiredCyclicResidualSolve hR hQ)
        (mk v S) steps (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      boundaryFactorState S' = Function.update (Function.update (boundaryFactorState S) .vk []) .dout
        (cstream A w solution) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro hprepared rhs hrhs v S tail pageTail hready hleft hmul hsolve h223 h184 h220 h221 hN hV hpage haSrc hleftEnd hrightEnd hfresh hvk hbo hhf hdf
  obtain ⟨v₁,S₁,m₁,C,D,R,T,hsolver,hreal,hnorm,herror,hsolLen,hsolBounds,hUnscale,hv₁,hm₁,he₁,hinp,hout,hL,hlegacy,hstream,hpost⟩ :=
    generatedCyclicResidualSolve_spec (body := body) hR hQ hA axis ha hn columns
      hprepared rhs hrhs v S tail pageTail hready hleft hmul hsolve h223 h184 h220 h221 hN hV hpage
      haSrc hleftEnd hrightEnd hfresh hvk hbo hhf hdf
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hq : (S₁.R 119).length = q := by
    rw [show S₁.R 119 = S.R 119 from hlegacy 119 (by decide)]
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S₁.R 121).length = s := by
    rw [show S₁.R 121 = S.R 121 from hlegacy 121 (by decide)]
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (121,97) (by simp [groupHeaderCopies])
  have hscratch : ∀ k ∈ [(94 : Fin 224),131,134,135,138], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [show S₁.R 94 = S.R 94 from hlegacy 94 (by decide)]
      simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.blank 94 (by decide) (by decide) (by decide)
    · rw [show S₁.R 131 = S.R 131 from hlegacy 131 (by decide)]
      simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 131 (by simp)
    · rw [show S₁.R 134 = S.R 134 from hlegacy 134 (by decide)]
      simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 134 (by simp)
    · rw [show S₁.R 135 = S.R 135 from hlegacy 135 (by decide)]
      simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 135 (by simp)
    · exact (hlegacy 138 (by decide)).trans (hfresh 138 (by simp))
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := retireCyclicResidualPhysical_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    q s (cstream A w (chirpLine s D)) (cstream A w (chirpLine s C)) (S.R 132)
    (by simp [chirpLine,hw]) (by simp [chirpLine,hw]) v₁ S₁ hq hs hstream hscratch
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 132 (S.R 132)}
  refine ⟨v₂,S₂,m₁+m₂,C,D,R,T,hsolver,hreal,hnorm,herror,hsolLen,hsolBounds,hUnscale.update_accumulator (S.R 132),hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,
    Exec.seq he₁ he₂,hinp,hout,hL,?_,?_⟩
  · intro i
    by_cases hi : i = 132
    · subst i; simp [S₂,boundaryFactorLegacyReg]
    have hne : boundaryFactorLegacyReg i ≠ 132 := by
      intro h
      apply hi
      exact Fin.ext (congrArg (fun k : Fin 224 => k.val) h)
    exact (Function.update_of_ne hne (S.R 132) S₁.R).trans (hlegacy i hi)
  · rw [show boundaryFactorState S₂ = boundaryFactorState S₁ from boundaryFactorState_update_accumulator S₁ (S.R 132)]
    exact hpost

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
