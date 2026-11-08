module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedGeneratedCyclicSolve
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

noncomputable def initializedCyclicSolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (embProg boundaryFactorLegacyReg id prepareCyclicBoundaryPage) (constructedGeneratedCyclicSolve hR hQ)

noncomputable def initializedCyclicSolveCost (R : Regs 154 A) (p u l s t a n target : ℕ) [NeZero s] : ℕ :=
  prepareCyclicBoundaryPageCost R s t (PhaseCellBand.width p u) a n+
    constructedGeneratedCyclicSolveCost p u l s t a n target

theorem initializedCyclicSolve_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
      steps ≤ initializedCyclicSolveCost (embStk boundaryFactorLegacyReg S).R p u l s t a n target ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicSolve hR hQ)
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
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  let E := embStk boundaryFactorLegacyReg S
  have hs : (E.R 121).length = s := by
    simpa [E,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (121,97) (by simp [groupHeaderCopies])
  have ht : (E.R 122).length = t := by
    simpa [E,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (122,98) (by simp [groupHeaderCopies])
  have hb : (E.R 124).length = PhaseCellBand.width p u := by
    simpa [E,embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (124,100) (by simp [groupHeaderCopies])
  have hblank (k : Fin 154) (hk : k.val < 77) : E.R k = [] := by
    let j : Fin 144 := ⟨k.val,by omega⟩
    have hj : j.val = k.val := rfl
    have hj109 : componentReg j ≠ 109 := by intro h; have hv := congrArg Fin.val h; change k.val = 109 at hv; omega
    have hj115 : componentReg j ≠ 115 := by intro h; have hv := congrArg Fin.val h; change k.val = 115 at hv; omega
    have hj116 : componentReg j ≠ 116 := by intro h; have hv := congrArg Fin.val h; change k.val = 116 at hv; omega
    have hmap : boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg (componentReg j))) = boundaryFactorLegacyReg k := by
      apply Fin.ext
      change (boundaryArithmeticReg (componentReg j)).val = k.val
      simp only [boundaryArithmeticReg,hj109,hj115,hj116,ite_false]
      rfl
    have hh := hready.blank j (by omega) (by omega) (by omega)
    change S.R (boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg (componentReg j)))) = [] at hh
    rw [hmap] at hh
    exact hh
  have h106 : E.R 106 = [] := by
    simpa [E,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 106 (by decide) (by decide) (by decide)
  have h108 : E.R 108 = [] := by
    simpa [E,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.blank 108 (by decide) (by decide) (by decide)
  have h135 : E.R 135 = [] := by
    simpa [E,embStk,componentReg,boundaryArithmeticReg,tableReg] using hready.fresh 135 (by simp)
  obtain ⟨vi,m₁,hvi,hm₁,hei,hreadyE⟩ := prepareCyclicBoundaryPage_ready_exec
    (body := embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))
    axis.hst has hbs axis.hband (embDn boundaryFactorLegacyReg v) E hs ht hb haMaster hnMaster
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact h106
        · exact h108
        · exact hfresh 109 (by simp)
        · exact hfresh 115 (by simp)
        · exact hfresh 116 (by simp)
        · exact h135
        · exact h138
        · exact hfresh 144 (by simp)
        · exact hfresh 145 (by simp)
        · exact hfresh 146 (by simp))
    hblank (by intro k; exact hleft _) (cstream A w (chirpLine s rhs)++tail) hready
  let E₁ : Stacks 154 A := {E with R := (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update E.R 141 []) 142 [])
      144 (List.replicate a tick)) 145 (List.replicate (a+min n (s-a)) tick))
      146 (List.replicate (n-min n (s-a)) tick)) 115 (List.replicate V tick))
      116 (List.replicate B.card tick)) 109 (cstream A V ((bFoldOrder s B).map
        (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))))}
  let S₁ := embOvr boundaryFactorLegacyReg E₁.get S
  obtain ⟨v₁,_,hv₁,he₁⟩ := exec_emb_ovr (ι := id)
    (body' := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    boundaryFactorLegacyReg_injective (fun _ => rfl) hei v rfl S rfl
  have hproj : embStk boundaryFactorLegacyReg S₁ = E₁ := embStk_ovr boundaryFactorLegacyReg_injective E₁ S
  have hkeep (i : Fin 154) (hi : i ∉ [109,115,116,141,142,144,145,146]) :
      S₁.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i) := by
    have hh := congrArg (fun X : Stacks 154 A => X.R i) hproj
    have hne : i ≠ 109 ∧ i ≠ 115 ∧ i ≠ 116 ∧ i ≠ 141 ∧ i ≠ 142 ∧ i ≠ 144 ∧ i ≠ 145 ∧ i ≠ 146 := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hi
    rcases hne with ⟨h109,h115,h116,h141,h142,h144,h145,h146⟩
    exact hh.trans (by simp [E₁,E,embStk,h109,h115,h116,h141,h142,h144,h145,h146])
  have hnew₁ : ∀ i : Fin 224, 154 ≤ i.val → S₁.R i = [] := by
    intro i hi
    have hoff : ∀ j : Fin 154, boundaryFactorLegacyReg j ≠ i := by
      intro j h
      have hv := congrArg Fin.val h
      change j.val = i.val at hv
      have := j.isLt
      omega
    exact ((embOvr_off E₁.get S hoff).2).trans (hnew i hi)
  have hL₁ : S₁.L = S.L := by
    change embExt boundaryFactorLegacyReg E₁.L S.L = S.L
    exact embExt_comp (e := boundaryFactorLegacyReg) S.L
  obtain ⟨v₂,S₂,m₂,columns,C,D,R,T,hlen,hacc,hprepared,hsolver,hreal,hnorm,herror,hsolLen,hsolBounds,hUnscale,hv₂,hm₂,he₂,
    hinp,hout,hL,hlegacy,hpacked,hsolution,hbo,hhf,hdf⟩ := constructedGeneratedCyclicSolve_spec (body := body)
      hR hQ hA axis has hbs rhs hrhs v₁ S₁ tail []
      (by have hh := congrArg (fun X : Stacks 154 A => (X.R 116).length) hproj
          simpa [E₁,B,embStk,boundaryFactorLegacyReg] using hh)
      (by have hh := congrArg (fun X : Stacks 154 A => (X.R 115).length) hproj
          simpa [E₁,V,embStk,boundaryFactorLegacyReg] using hh)
      (by have hh := congrArg (fun X : Stacks 154 A => X.R 109) hproj
          simpa [E₁,embStk,boundaryFactorLegacyReg] using hh)
      (by simpa only [hproj] using hreadyE)
      (by have hh := congrArg (fun X : Stacks 154 A => (X.R 144).length) hproj; simpa [E₁,embStk,boundaryFactorLegacyReg] using hh)
      (by have hh := congrArg (fun X : Stacks 154 A => (X.R 145).length) hproj; simpa [E₁,embStk,boundaryFactorLegacyReg] using hh)
      (by have hh := congrArg (fun X : Stacks 154 A => (X.R 146).length) hproj; simpa [E₁,embStk,boundaryFactorLegacyReg] using hh)
      (by have hh := congrArg (fun X : Stacks 154 A => X.R 141) hproj; simpa [E₁,embStk,boundaryFactorLegacyReg] using hh)
      (by have hh := congrArg (fun X : Stacks 154 A => X.R 142) hproj; simpa [E₁,embStk,boundaryFactorLegacyReg] using hh)
      ((hkeep 0 (by simp)).trans h0) ((hkeep 139 (by simp)).trans h139)
      ((hkeep 127 (by simp)).trans h127) ((hkeep 138 (by simp)).trans h138)
      ((hkeep 143 (by simp)).trans h143) ((hkeep 147 (by simp)).trans h147)
      ((hkeep 151 (by simp)).trans h151) ((hkeep 152 (by simp)).trans h152) ((hkeep 153 (by simp)).trans h153)
      (by intro i; rw [hL₁]; exact hleft i) hnew₁
  refine ⟨v₂,S₂,m₁+m₂,columns,C,D,R,T,hlen,hacc,hprepared,hsolver,hreal,hnorm,herror,hsolLen,hsolBounds,hUnscale,
    hv₂.trans (hv₁.trans hvi),Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂,hinp,hout,hL.trans hL₁,?_,?_,hsolution,hbo,hhf,hdf⟩
  · intro i hi
    have hh := congrArg (fun X : Stacks 154 A => X.R i) hproj
    exact (hlegacy i hi).trans hh
  · exact hpacked.trans (congrArg (bandTableWords A w B (24*PhaseCellBand.width p u+1) columns 0 ++ ·)
      (hkeep 132 (by simp)))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
