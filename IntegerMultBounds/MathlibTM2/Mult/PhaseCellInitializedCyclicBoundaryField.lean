module

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

noncomputable def initializedCyclicBoundaryField (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (initializedCyclicUnscaledSolve hR hQ) solvedBoundaryField

theorem initializedCyclicBoundaryField_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∃ v₁ S₁ m₁ v' S' steps, ∃ columns : List (ZMod s → GaussianInt), ∃ solution : List GaussianInt,
      solution.length = B.card ∧ (∀ z ∈ solution, Fits w z) ∧
      PreparedBoundaryColumns A p bits q w W B columns ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (chirpLine s rhs)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S')))) ∧
      (∀ x : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
          (fun k => (value q (rhs k)).re) →
        (∀ i < B.card,
          ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
          ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) ∧
        ∀ i ∈ B, |(value q (boundarySolutionField B solution i)).re-x i| ≤ 3/(2 : ℝ)^target) ∧
      v'.user = v.user ∧
      m₁ ≤ initializedCyclicUnscaledSolveCost (embStk boundaryFactorLegacyReg S).R p u l s t a n target ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicUnscaledSolve hR hQ)
        (mk v S) m₁ (mk v₁ S₁) ∧
      steps ≤ m₁+solvedBoundaryFieldCost S₁.R s B.card V q ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicBoundaryField hR hQ)
        (mk v S) steps (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R 110 = S.R 110 ∧ S'.R 109 = [] ∧ S'.R 204 = [] ∧ S'.R 217 = [] ∧
      S'.R 132 = cstream A w (chirpLine s (boundarySolutionField B solution))++
        (bandTableWords A w B W columns 0++S.R 132) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  obtain ⟨v₁,S₁,m₁,columns,C,D,R,T,hlen,hacc,hprepared,hsolver,hreal,hnorm,herror,hsolLen,hsolFits,haccuracy,hUnscale,
    hv₁,hm₁,he₁,hinp,hout,hL,hlegacy,hpacked,hsource,hbo,hhf,hdf⟩ := initializedCyclicUnscaledSolve_spec (body := body)
      hR hQ hA axis has hbs rhs hrhs v S tail hready haMaster hnMaster hfresh
      h0 h139 h127 h138 h143 h147 h151 h152 h153 hleft hnew
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hs : (S₁.R 121).length = s := by
    have hs₀ : (S.R 121).length = s := by
      simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
        hready.masters (121,97) (by simp [groupHeaderCopies])
    have hf := hlegacy 121 (by decide)
    simpa [embStk,boundaryFactorLegacyReg] using (congrArg List.length hf).trans hs₀
  have hV : (S₁.R 115).length = V := by
    have hf := hlegacy 115 (by decide)
    simpa [embStk,boundaryFactorLegacyReg,V] using congrArg List.length hf
  have hN : S₁.R 116 = List.replicate B.card tick := by
    simpa [embStk,boundaryFactorLegacyReg,B] using hlegacy 116 (by decide)
  have hcoords : S₁.R 109 = cstream A V ((bFoldOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) := by
    simpa [embStk,boundaryFactorLegacyReg,V,B] using hlegacy 109 (by decide)
  have hsV : s ≤ 2^V := by
    have hfit := publicationGeometryWidth_fits t (PhaseCellBand.width p u)
    have hst := axis.hst
    have ht : t ≤ (t+1)^2 := by nlinarith
    dsimp only [V]
    omega
  let selected := fun i : ZMod s => if a ≤ i.val ∧ i.val < a+min n (s-a) then C i else D i
  let W := 24*PhaseCellBand.width p u+1
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let solution := (bandSolveVec q W (naturalLineLc q K W B.card AZ)
    (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
    (((List.range B.card).map (fun j => selected (bFoldAt s B j))).map (normalizeBoundaryWord q (q/2-1)))).map
      (unscaleBoundaryWord q)
  have hsrc : S₁.R 217 = cstream A (2*q+8) solution := by
    change S₁.R 217 = cstream A w solution at hsource
    rw [hw] at hsource
    exact hsource
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := solvedBoundaryField_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    (by omega) s B V q hsV _ hsolLen v₁ S₁ hUnscale hs hV hN hcoords hsrc
  let S₂ : Stacks 224 A := {S₁ with R := (Function.update
    (fun i => if i ∈ ([189,191,198,204,217,206,109] : List (Fin 224)) then [] else S₁.R i) 132
      (cstream A w (chirpLine s (boundarySolutionField B solution))++S₁.R 132))}
  have he₂' : Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
      solvedBoundaryField (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₂,hw] using he₂
  have hreadyFinal : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (chirpLine s rhs)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S₂)))) := by
    apply cyclicRecoveryReady_of_frame (S' := embStk boundaryFactorLegacyReg S₂) hready
    · exact congrArg (fun L => L ∘ boundaryFactorLegacyReg) hL
    · intro k hk
      have hne (j : Fin 154) (hj : j ∈ ([109,115,116,132,141,142,144,145,146] : List (Fin 154))) : k ≠ j := by
        intro he
        subst k
        exact hk hj
      have hf := hlegacy k (hne 132 (by simp))
      have hlow : k.val < 154 := k.isLt
      have hval109 : k.val ≠ 109 := fun he => hne 109 (by simp) (Fin.ext he)
      have hval132 : k.val ≠ 132 := fun he => hne 132 (by simp) (Fin.ext he)
      have hfield : S₂.R (boundaryFactorLegacyReg k) = S₁.R (boundaryFactorLegacyReg k) := by
        simp [S₂,boundaryFactorLegacyReg,Fin.ext_iff,hval109,hval132,
          show k.val ≠ 189 by omega,show k.val ≠ 191 by omega,show k.val ≠ 198 by omega,
          show k.val ≠ 204 by omega,show k.val ≠ 217 by omega,show k.val ≠ 206 by omega]
      change S₂.R (boundaryFactorLegacyReg k) = S.R (boundaryFactorLegacyReg k)
      rw [hfield,hf]
      simp only [Function.update_of_ne (hne 109 (by simp)),Function.update_of_ne (hne 115 (by simp)),
        Function.update_of_ne (hne 116 (by simp)),Function.update_of_ne (hne 141 (by simp)),
        Function.update_of_ne (hne 142 (by simp)),Function.update_of_ne (hne 144 (by simp)),
        Function.update_of_ne (hne 145 (by simp)),Function.update_of_ne (hne 146 (by simp))]
      rfl
  refine ⟨v₁,S₁,m₁,v₂,S₂,m₁+m₂,columns,solution,hsolLen,hsolFits,hprepared,hreadyFinal,?_,hv₂.trans hv₁,hm₁,he₁,
    Nat.add_le_add_left hm₂ m₁,Exec.seq he₁ he₂',hinp,hout,hL,?_,by simp [S₂],by simp [S₂],by simp [S₂],?_⟩
  · intro x hx
    exact ⟨haccuracy x hx,boundarySolutionField_error q B solution x _ (fun i hi => (haccuracy x hx i hi).1)⟩
  · have hf := hlegacy 110 (by decide)
    simpa [S₂,embStk,boundaryFactorLegacyReg] using hf
  · change cstream A w (chirpLine s (boundarySolutionField B solution))++S₁.R 132 = _
    rw [hpacked]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
