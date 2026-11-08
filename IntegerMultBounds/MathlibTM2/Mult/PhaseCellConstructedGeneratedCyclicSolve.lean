module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedCyclicFactor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetiredCyclicResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSolveTables

/-! Compute the joint cyclic table and factors, generate residuals, solve and retire them. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem factorLegacyReady_of_frame {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S S' : Stacks 224 A}
    (h : LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (hL : S'.L = S.L)
    (hframe : ∀ i : Fin 154, i ≠ 132 → S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) :
    LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S')))) := by
  apply tableLoopReady_of_frame h
  · funext i
    change S'.L (boundaryFactorLegacyReg i) = S.L (boundaryFactorLegacyReg i)
    rw [hL]
  · intro k _ hk
    exact hframe k hk

noncomputable def constructedGeneratedCyclicSolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (constructedCyclicFactor hR hQ) (retiredCyclicResidualSolve hR hQ)

noncomputable def constructedGeneratedCyclicSolveCost (p u l s t a n target : ℕ) [NeZero s] : ℕ :=
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 24*PhaseCellBand.width p u+1
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  constructedCyclicFactorCost p u l s t a n target 2+
    ((windowedSchurResidualCost p l s t u bits 2 a (a+min n (s-a))+
      windowedSchurResidualCost p l s t u bits 2 0 (n-min n (s-a)))+
      (cyclicBoundaryRhsPrepareCost B q V a (a+min n (s-a))+generatedBoundaryNormalizeCost q B.card+
        4*B.card*w+4*W*w+8+bandLinePassCost w B.card W)+retireCyclicResidualsCost q s)

theorem constructedGeneratedCyclicSolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s)
    (rhs : ZMod s → GaussianInt)
    (hrhs : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (rhs i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (pageTail : List (Fin (A+4)))
    (hrows : (S.R 116).length = (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card)
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)).map
        (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (chirpLine s rhs)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (h141 : S.R 141 = []) (h142 : S.R 142 = [])
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = [])
    (h151 : S.R 151 = []) (h152 : S.R 152 = []) (h153 : S.R 153 = [])
    (hleft : ∀ i : Fin 224, S.L i = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let bits := boundaryTableBits p target 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 24*PhaseCellBand.width p u+1
    let K := factorNewtonSteps p q
    ∃ v' S' steps, ∃ columns : List (ZMod s → GaussianInt), ∃ C D : ZMod s → GaussianInt, ∃ R T : (ZMod s → ℝ) → ZMod s → ℝ,
      let AZ := factorRankIntegerMatrix B W columns
      let solver := fun rhs k => if k ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a)) then R rhs k else T rhs k
      let selected := fun i : ZMod s => if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i
      let solution := bandSolveVec q W (naturalLineLc q K W B.card AZ)
        (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
        (((List.range B.card).map (fun j => selected (bFoldAt s B j))).map (normalizeBoundaryWord q (q/2-1)))
      columns.length = B.card ∧ ColumnFamilyAccurate A q w B
        (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
          (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 (1/(2 : ℝ)^bits) columns ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
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
      steps ≤ constructedGeneratedCyclicSolveCost p u l s t a n target ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (constructedGeneratedCyclicSolve hR hQ)
        (mk v S) steps (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 132 → S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      S'.R 132 = bandTableWords A w B W columns 0++S.R 132 ∧
      S'.R 217 = cstream A w solution ∧
      (boundaryFactorState S') .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
      (boundaryFactorState S') .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
      (boundaryFactorState S') .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 24*PhaseCellBand.width p u+1
  let K := factorNewtonSteps p q
  obtain ⟨v₁,S₁,m₁,columns,hv₁,hm₁,he₁,hlen,hacc,hformat,hprepared,hinp₁,hout₁,hL₁,
    hlegacy₁,hmul,h106,h139',h184,h223,h220,h221,h119,hsolve,hbo,hhf,hdf,hsrc,hm2n,hmwn,hsn,hdout,hvk,hrest⟩ :=
    constructedCyclicFactor_spec (body := body) (rhsExp := 2) hR hQ hA axis has hbs v S
      (cstream A w (chirpLine s rhs)++tail) pageTail hrows hpageWidth hpage hready
      haSrc hleftEnd hrightEnd h141 h142 h0 h139 h127 h138 h143 h147 h151 h152 h153 hleft hnew
  have hkeep (i : Fin 154) (hi : i ≠ 132) : S₁.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i) := by
    by_cases hi140 : i = 140
    · subst i; exact hsrc
    have hh := hlegacy₁ i hi140
    simpa [embStk,hi,hi140] using hh
  have hready₁ := factorLegacyReady_of_frame hready hL₁ hkeep
  obtain ⟨hbo',hhf',hdf'⟩ := boundaryFactor_solve_tables q w K B W columns (boundaryFactorState S₁) hbo hhf hdf
  obtain ⟨v₂,S₂,m₂,C,D,R,T,hsolver,hreal,hnorm,herror,hsolLen,hsolBounds,hUnscale,hv₂,hm₂,he₂,hinp₂,hout₂,hL₂,hlegacy₂,hpost⟩ :=
    retiredCyclicResidualSolve_spec (body := body) hR hQ hA axis has hbs columns hprepared rhs hrhs
      v₁ S₁ tail pageTail hready₁ (by intro i; rw [hL₁]; exact hleft i) hmul hsolve h223 h184 h220 h221
      ((congrArg List.length (hkeep 116 (by decide))).trans hrows)
      ((congrArg List.length (hkeep 115 (by decide))).trans hpageWidth)
      ((hkeep 109 (by decide)).trans hpage)
      ((congrArg List.length (hkeep 144 (by decide))).trans haSrc)
      ((congrArg List.length (hkeep 145 (by decide))).trans hleftEnd)
      ((congrArg List.length (hkeep 146 (by decide))).trans hrightEnd)
      (by intro k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact (hkeep 127 (by decide)).trans h127
          · exact (hkeep 138 (by decide)).trans h138
          · exact h139'
          · exact (hkeep 141 (by decide)).trans h141
          · exact (hkeep 142 (by decide)).trans h142
          · exact (hkeep 143 (by decide)).trans h143
          · exact (hkeep 147 (by decide)).trans h147)
      hvk hbo' hhf' hdf'
  refine ⟨v₂,S₂,m₁+m₂,columns,C,D,R,T,hlen,hacc,hprepared,hsolver,hreal,hnorm,herror,hsolLen,hsolBounds,hUnscale,
    hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂,hinp₂.trans hinp₁,hout₂.trans hout₁,hL₂.trans hL₁,?_,?_,
    congrFun hpost .dout,?_,?_,?_⟩
  · intro i hi
    exact (hlegacy₂ i).trans (hkeep i hi)
  · have hh := hlegacy₁ 132 (by decide)
    exact (hlegacy₂ 132).trans (by simpa [embStk,boundaryFactorLegacyReg] using hh)
  · exact (congrFun hpost .bo).trans hbo'
  · exact (congrFun hpost .hf).trans hhf'
  · exact (congrFun hpost .df).trans hdf'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
