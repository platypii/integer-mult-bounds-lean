module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundarySolutionAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicBoundaryPageReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetiredCyclicResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSolveTables

/-! Generate ordinary cyclic geometry and execute the complete joint factor/solve lifecycle. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def initializedCyclicUnscaledSolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (initializedCyclicSolve hR hQ) (generatedBoundaryUnscale hQ)

noncomputable def initializedCyclicUnscaledSolveCost (R : Regs 154 A) (p u l s t a n target : ℕ) [NeZero s] : ℕ :=
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let q := executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2) 2
  initializedCyclicSolveCost R p u l s t a n target+generatedBoundaryUnscaleCost q B.card

theorem initializedCyclicUnscaledSolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s)
    (rhs : ZMod s → GaussianInt)
    (hrhs : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (rhs i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (chirpLine s rhs)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hnMaster : (S.R 142).length = n)
    (hfresh : ∀ k ∈ [(109 : Fin 224),115,116,144,145,146], S.R k = [])
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
    let V := publicationGeometryWidth t (PhaseCellBand.width p u)
    let K := factorNewtonSteps p q
    ∃ v' S' steps, ∃ columns : List (ZMod s → GaussianInt), ∃ C D : ZMod s → GaussianInt, ∃ R T : (ZMod s → ℝ) → ZMod s → ℝ,
      let E := embStk boundaryFactorLegacyReg S
      let E₁ : Stacks 154 A := {E with R := (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update E.R 141 []) 142 [])
          144 (List.replicate a tick)) 145 (List.replicate (a+min n (s-a)) tick))
          146 (List.replicate (n-min n (s-a)) tick)) 115 (List.replicate V tick))
          116 (List.replicate B.card tick)) 109 (cstream A V ((bFoldOrder s B).map
            (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))))}
      let AZ := factorRankIntegerMatrix B W columns
      let solver := fun rhs k => if k ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a)) then R rhs k else T rhs k
      let selected := fun i : ZMod s => if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i
      let normalized := bandSolveVec q W (naturalLineLc q K W B.card AZ)
        (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
        (((List.range B.card).map (fun j => selected (bFoldAt s B j))).map (normalizeBoundaryWord q (q/2-1)))
      let solution := normalized.map (unscaleBoundaryWord q)
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
      solution.length = B.card ∧ (∀ z ∈ solution, Fits w z) ∧
      (∀ x : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
          (fun k => (value q (rhs k)).re) →
        ∀ i < B.card,
          ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
          ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) ∧
      BoundaryUnscaleReady q S' ∧
      v'.user = v.user ∧
      steps ≤ initializedCyclicUnscaledSolveCost (embStk boundaryFactorLegacyReg S).R p u l s t a n target ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicUnscaledSolve hR hQ)
        (mk v S) steps (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 132 → S'.R (boundaryFactorLegacyReg i) = E₁.R i) ∧
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
  obtain ⟨v₁,S₁,m₁,columns,C,D,R,T,hlen,hacc,hprepared,hsolver,hreal,hnorm,herror,hsolLen,hsolBounds,hUnscale,
    hv₁,hm₁,he₁,hinp,hout,hL,hlegacy,hpacked,hsource,hbo,hhf,hdf⟩ := initializedCyclicSolve_spec (body := body)
      hR hQ hA axis has hbs rhs hrhs v S tail hready haMaster hnMaster hfresh
      h0 h139 h127 h138 h143 h147 h151 h152 h153 hleft hnew
  let selected := fun i : ZMod s => if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i
  let AZ := factorRankIntegerMatrix B W columns
  let normalized := bandSolveVec q W (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
    (naturalLineRcs q K W B.card AZ)
    (((List.range B.card).map (fun j => selected (bFoldAt s B j))).map (normalizeBoundaryWord q (q/2-1)))
  have hbits : 4*p+2*Nat.size B.card+36 ≤ q := factor_execution_bits p u l target 2 B.card
  have hpq : p ≤ q/2 := by omega
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hsrc : S₁.R 217 = cstream A (2*q+8) normalized := by
    change S₁.R 217 = cstream A w normalized at hsource
    rw [hw] at hsource
    exact hsource
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := generatedBoundaryUnscale_ready_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    hQ hA q p hpq normalized hsolBounds v₁ S₁ hUnscale hsrc
  let result := normalized.map (unscaleBoundaryWord q)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 217 (cstream A w result)}
  have he₂' : Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
      (generatedBoundaryUnscale hQ) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₂,result,hw] using he₂
  have hm₂' : m₂ ≤ generatedBoundaryUnscaleCost q B.card := by
    change normalized.length = B.card at hsolLen
    simpa only [hsolLen] using hm₂
  have hresultLen : result.length = B.card := by simpa only [result,List.length_map] using hsolLen
  have hresultFits : ∀ z ∈ result, Fits w z := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    simpa only [hw] using (boundary_unscale_fits q p hpq x (hsolBounds x hx)).2
  have haccuracy (x : ZMod s → ℝ)
      (hx : SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
        (fun k => (value q (rhs k)).re)) :
      ∀ i < B.card,
        ‖value q (result.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
        ‖value q (result.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2 := by
    have h := cyclicBoundary_solution_accuracy A p u l target a n axis has hbs (by omega) columns
      hprepared hacc selected
      (fun b k => if k ∈ haloInterior s t (PhaseCellBand.width p u) a (a+min n (s-a)) then R b k else T b k)
      x (fun k => (value q (rhs k)).re) hsolver hx
      (fun k _ => (Complex.abs_re_le_norm _).trans (hrhs k))
      (by intro k _; dsimp only [selected]; split <;> first | exact (hnorm k).1 | exact (hnorm k).2)
      (by intro k _; dsimp only [selected]; split <;> first | exact (hreal k).1 | exact (hreal k).2)
      herror
    exact h.2
  refine ⟨v₂,S₂,m₁+m₂,columns,C,D,R,T,hlen,hacc,hprepared,hsolver,hreal,hnorm,herror,hresultLen,hresultFits,haccuracy,
    hUnscale.update_solution (cstream A w result),hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂',
    Exec.seq he₁ he₂',hinp,hout,hL,?_,hpacked,by rfl,?_,?_,?_⟩
  · intro i hi
    have hne : boundaryFactorLegacyReg i ≠ 217 := by
      intro h
      have hv := congrArg (fun k : Fin 224 => k.val) h
      change i.val = 217 at hv
      have := i.isLt
      omega
    exact (Function.update_of_ne hne (cstream A w result) S₁.R).trans (hlegacy i hi)
  · exact hbo
  · exact hhf
  · exact hdf

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
