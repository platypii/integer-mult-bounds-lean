module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicBoundaryField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalCyclicBoundaryRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvedBoundaryField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicUnscaledSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundarySolutionAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicBoundaryPageReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetiredCyclicResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSolveTables

/-! Generate and solve the joint cyclic boundary system, then publish its computed real field. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def initializedCyclicRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (initializedCyclicBoundaryField hR hQ) (physicalCyclicBoundaryRecovery hR hQ)

theorem initializedCyclicRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s)
    (rhs : ZMod s → GaussianInt)
    (hrhs : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (rhs i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (chirpLine s rhs)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hnMaster : (S.R 142).length = n)
    (hfresh : ∀ k ∈ [(109 : Fin 224),115,116,144,145,146], S.R k = [])
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = [])
    (h151 : S.R 151 = []) (h152 : S.R 152 = []) (h153 : S.R 153 = [])
    (hleft : ∀ i : Fin 224, S.L i = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let solveTarget := boundaryRecoveryTarget p target
    let bits := boundaryTableBits p solveTarget 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 24*band+1
    let V := publicationGeometryWidth t band
    ∃ v₀ S₀ m₀ v₁ S₁ m₁ v' S' steps,
      ∃ columns : List (ZMod s → GaussianInt), ∃ solution : List GaussianInt, ∃ D E : ZMod s → GaussianInt,
      solution.length = B.card ∧ (∀ z ∈ solution, Fits w z) ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band 0 0 (cstream A w (chirpLine s rhs)++tail)
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S')))) ∧
      (S'.R 144).length = a ∧ (S'.R 145).length = a+min n (s-a) ∧
      (S'.R 146).length = n-min n (s-a) ∧
      (∀ k ∈ ([(138 : Fin 224),141,142,143]), S'.R k = []) ∧
      m₀ ≤ initializedCyclicUnscaledSolveCost (embStk boundaryFactorLegacyReg S).R p u l s t a n solveTarget ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicUnscaledSolve hR hQ)
        (mk v S) m₀ (mk v₀ S₀) ∧
      m₁ ≤ m₀+solvedBoundaryFieldCost S₀.R s B.card V q ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicBoundaryField hR hQ)
        (mk v S) m₁ (mk v₁ S₁) ∧
      v'.user = v.user ∧
      steps ≤ m₁+archivedWindowedRecoveryCost p l s t u (recoveryTarget p bits) 2 (stableInteriorExponent p 2) a (a+min n (s-a))+
        archivedWindowedRecoveryCost p l s t u (recoveryTarget p bits) 2 (stableInteriorExponent p 2) 0 (n-min n (s-a)) ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicRecovery hR hQ)
        (mk v S) steps (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R 110 = S.R 110 ∧
      S'.R 132 = cstream A w (chirpLine s (boundarySolutionField B solution))++
        (bandTableWords A w B W columns 0++S.R 132) ∧
      S'.R 147 = cstream A w (chirpLine s E)++cstream A w (chirpLine s D) ∧
      ∀ x : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
          (fun i => (value q (rhs i)).re) →
        PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
          (SchurDominance.glue (cyclicPrincipalInterior s t band a n)
            (fun i => if i ∈ haloInterior s t band a (a+min n (s-a)) then (value q (D i)).re else (value q (E i)).re)
            (fun i => (value q (boundarySolutionField B solution i)).re)) x (1/(2 : ℝ)^target) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let solveTarget := boundaryRecoveryTarget p target
  let bits := boundaryTableBits p solveTarget 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨v₀,S₀,m₀,v₁,S₁,m₁,columns,solution,hlen,hfits,hprepared,hready₁,h144,h145,h146,hfresh₁,haccuracy,
    hv₁,hm₀,he₀,hm₁,he₁,hinp,hout,hL,h110,h109,h204,h217,hfield⟩ := initializedCyclicBoundaryField_spec
      (body := body) (target := solveTarget) hR hQ hA axis has hbs rhs hrhs v S tail hready haMaster hnMaster hfresh
      h0 h139 h127 h138 h143 h147 h151 h152 h153 hleft hnew
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := axis.hp; omega)
  obtain ⟨x₀,hx₀⟩ := SchurDominance.solves_exists (realMatrix s t p u) (cyclicPrincipalVertices s a n)
    (1/(8*(p : ℝ))) (by positivity)
    (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) axis.hdom)
    (fun i => (value q (rhs i)).re)
  have hmag : ∀ i < B.card, ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2 :=
    fun i hi => ((haccuracy x₀ hx₀).1 i hi).2
  obtain ⟨v₂,m₂,D,E,hv₂,hm₂,he₂,herror⟩ := physicalCyclicBoundaryRecovery_spec (body := body)
    hR hQ hA axis has hbs target rhs solution hrhs hmag v₁ S₁ tail
    (bandTableWords A w B (24*band+1) columns 0++S.R 132) hready₁ h144 h145 h146
    (fun k hk => hfresh₁ k (List.mem_append_left [147] hk)) hfield
  let F : Stacks 224 A := {S₁ with R := (Function.update S₁.R 147
    (cstream A w (chirpLine s E)++(cstream A w (chirpLine s D)++S₁.R 147)))}
  have hproject : embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg F))) =
      embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S₁))) := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hne : boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg (componentReg k))) ≠ (147 : Fin 224) := by
      intro he
      have hv := congrArg (fun j : Fin 224 => j.val) he
      have hk := k.isLt
      dsimp [boundaryFactorLegacyReg,tableReg,boundaryArithmeticReg,componentReg] at hv
      split_ifs at hv <;> simp_all
      all_goals omega
    simp only [F,embStk,Function.comp_apply,Function.update_of_ne hne]
  have hreadyFinal : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0 (cstream A w (chirpLine s rhs)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg F)))) := by
    rw [hproject]
    exact hready₁
  refine ⟨v₀,S₀,m₀,v₁,S₁,m₁,v₂,F,m₁+m₂,columns,solution,D,E,hlen,hfits,hprepared,hreadyFinal,?_,?_,?_,?_,
    hm₀,he₀,hm₁,he₁,hv₂.trans hv₁,?_,Exec.seq he₁ he₂,hinp,hout,hL,?_,?_,?_,?_⟩
  · simpa [F] using h144
  · simpa [F] using h145
  · simpa [F] using h146
  · intro k hk
    have h147 : k ≠ 147 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    have hc : S₁.R k = [] := hfresh₁ k (List.mem_cons_of_mem 127 (List.mem_append_left [147] hk))
    simpa only [F,Function.update_of_ne h147] using hc
  · have h := Nat.add_le_add_left hm₂ m₁
    simpa only [Nat.add_assoc] using h
  · simpa [F] using h110
  · simpa [F] using hfield
  · simp [F,w,bits,B,band,solveTarget,hfresh₁ 147 (by simp)]
  · intro x hx
    exact herror x hx (fun i hi => ((haccuracy x hx).1 i hi).1)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
