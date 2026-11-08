module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPreparedBoundaryColumns
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

noncomputable def generatedCyclicResidualSolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (cyclicResidualPhysical hR hQ) (generatedCyclicBoundaryGatherSolve hQ)

theorem generatedCyclicResidualSolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      (∀ i ∈ B, |(value q (selected i)).re-SchurDominance.residual (realMatrix s t p u)
        (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n) solver (fun k => (value q (rhs k)).re) i| ≤
          (1/(2 : ℝ)^(recoveryTarget p bits+2))/(8*(p : ℝ))) ∧
      v'.user = v.user ∧
      steps ≤ (windowedSchurResidualCost p l s t u bits 2 a (a+min n (s-a))+
        windowedSchurResidualCost p l s t u bits 2 0 (n-min n (s-a)))+
        (cyclicBoundaryRhsPrepareCost B q V a (a+min n (s-a))+generatedBoundaryNormalizeCost q B.card+
          4*B.card*w+4*W*w+8+bandLinePassCost w B.card W) ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (generatedCyclicResidualSolve hR hQ)
        (mk v S) steps (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 132 → S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      S'.R 132 = cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132) ∧
      boundaryFactorState S' = Function.update (Function.update (boundaryFactorState S) .vk []) .dout
        (cstream A w solution) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 24*PhaseCellBand.width p u+1
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  intro hprepared rhs hrhs v S tail pageTail hready hleft hmul hsolve h223 h184 h220 h221 hN hV hpage haSrc hleftEnd hrightEnd hfresh hvk hbo hhf hdf
  obtain ⟨v₁,m₁,C,D,R,T,hsolver,hv₁,hm₁,he₁,hreal,hnorm,herror,hready₁⟩ :=
    cyclicResidualPhysical_spec (body := body) (target := bits) (rhsExp := 2)
      hR hQ hA axis.hp axis.hpacket axis.hα axis.hst axis.hu axis.hαu axis.hθ axis.hgap axis.hbudget axis.hband ha hn axis.hpad
      rhs hrhs v S tail haSrc hleftEnd hrightEnd
      (by intro k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp)) hready
  let output := cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++S.R 132)
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 132 output}
  have hstate : boundaryFactorState S₁ = boundaryFactorState S := by
    funext r
    exact Function.update_of_ne (boundaryFactorReg_off r 132 (by decide)) _ _
  have hq : (S₁.R 119).length = q := by
    simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S₁.R 121).length = s := by
    simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (121,97) (by simp [groupHeaderCopies])
  have hscratch : ∀ k ∈ [(94 : Fin 224),106,134,135,136,137,138,139,140,150], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.blank 94 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.blank 106 (by decide) (by decide) (by decide)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 134 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 135 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 136 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 137 (by simp)
    · simpa [S₁] using hfresh 138 (by simp)
    · simpa [S₁] using hfresh 139 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.fresh 140 (by simp)
    · simpa [S₁,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hready.blank 116 (by decide) (by decide) (by decide)
  have hbound : ∀ i ∈ B, |gv q (if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i).re| ≤
      (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) ∧
      |gv q (if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i).im| ≤
      (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u) := by
    intro i _
    split_ifs
    · exact ⟨by simpa [value,gv] using (Complex.abs_re_le_norm _).trans (hnorm i).1,
        by simpa [value,gv] using (Complex.abs_im_le_norm _).trans (hnorm i).1⟩
    · exact ⟨by simpa [value,gv] using (Complex.abs_re_le_norm _).trans (hnorm i).2,
        by simpa [value,gv] using (Complex.abs_im_le_norm _).trans (hnorm i).2⟩
  have hwide : s+s ≤ 2^V := by
    have hfit := publicationGeometryWidth_fits t (PhaseCellBand.width p u)
    change s+s ≤ 2^(publicationGeometryWidth t (PhaseCellBand.width p u))
    nlinarith only [hfit,axis.hst]
  obtain ⟨v₂,S₂,m₂,hv₂,hm₂,he₂,hinp,hout,hL,hlegacy,hframe,hpost⟩ :=
    generatedCyclicBoundaryGatherSolve_exec
      (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
      hQ hA p u l target 2 B W V a (a+min n (s-a)) columns axis.hp hprepared.length
      hwide ha.le (by omega)
      hprepared.format hprepared.stage C D hbound pageTail (S.R 132) v₁ S₁
      hleft (by
        intro i
        have hne : boundaryFactorMulReg i ≠ 132 := by
          intro h
          have hv := congrArg (fun k : Fin 224 => k.val) h
          change i.val = 132 at hv
          have := i.isLt
          omega
        simpa only [S₁,Function.update_of_ne hne] using hmul i) (by rw [hstate]; exact hsolve)
      hq (by simpa [S₁] using h223) (by simpa [S₁] using h184) (by simpa [S₁] using h220) (by simpa [S₁] using h221)
      (by simpa [S₁] using hN) (by simpa [S₁] using hV) (by simpa [S₁] using hpage)
      hs (by simpa [S₁] using haSrc) (by simpa [S₁] using hleftEnd) (by rfl)
      (by change (boundaryFactorState S₁) .vk = []; rw [hstate]; exact hvk) hscratch (by simpa [hstate] using hbo) (by simpa [hstate] using hhf) (by simpa [hstate] using hdf)
  refine ⟨v₂,S₂,m₁+m₂,C,D,R,T,hsolver,?_,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,
    Exec.seq he₁ he₂,hinp,hout,hL,?_,?_,?_⟩
  · intro i hi
    simpa only [mem_haloVertices,apply_ite] using herror i hi
  · intro i hi
    have hne : boundaryFactorLegacyReg i ≠ 132 := by
      intro h
      apply hi
      exact Fin.ext (congrArg (fun k : Fin 224 => k.val) h)
    exact (hlegacy i).trans (Function.update_of_ne hne output S.R)
  · exact (hlegacy 132).trans (by rfl)
  · simpa only [hstate] using hpost

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
