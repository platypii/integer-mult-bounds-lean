module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryPublished
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalRecoveryPublishedHalo
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRetirementCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Recover a real halo line and restore the entire borrowed boundary workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedBoundaryRecovered (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (retainedBoundaryPublished hR hQ)
    (.seq (physicalRecoveryPublishedHalo hR hQ) (.seq retirePublishedBoundary releaseBoundaryWorkspace))

noncomputable def retainedBoundaryRecoveredCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let solveTarget := boundaryRecoveryTarget p target
  let bits := boundaryTableBits p solveTarget 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  retainedBoundaryPublishedCost p u l s t a b solveTarget+
    recoveryToleranceCost p l s t u bits 2 a b+
    haloBoundaryRetirementCostBound s t band a b w+
    releaseBoundaryWorkspaceCostBound s w (publicationGeometryWidth t band) N
      (boundaryPermanentSizeBound q band N)

theorem retainedBoundaryRecovered_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (chirpLine s F)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let solveTarget := boundaryRecoveryTarget p target
    let bits := boundaryTableBits p solveTarget 2 B.card
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ solution : List GaussianInt,
      let G := boundarySolutionField B solution
      ∀ x : ZMod s → ℝ,
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
      ∃ v' n, ∃ E : ZMod s → GaussianInt,
        let Y := fun i => realPartWord (publicationField t band a b E G i)
        let S' : Stacks 224 A := {S with R := Function.update S.R 132 (cstream A w (chirpLine s Y)++S.R 132)}
        v'.user = v.user ∧ n ≤ retainedBoundaryRecoveredCost p u l s t a b target ∧
        Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
          (embTab componentReg (embTab groupReg body))))) (retainedBoundaryRecovered hR hQ)
          (mk v S) n (mk v' S') ∧
        PhaseCellInterface.ErrorOn (haloVertices s a b)
          (fun i => publishedCellRead q w (0 : ZMod s) (S'.R 132) i) x (1/(2 : ℝ)^target) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let solveTarget := boundaryRecoveryTarget p target
  let bits := boundaryTableBits p solveTarget 2 B.card
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨v₀,S₀,n₀,D,columns,solution,hu₀,
    hn₀,he₀,hcols,hlen,h132,h110,h109',h204,h206,hinp,hout,hL,hframe₀,hready₀,
    ha₀,hb₀,h127₀,h138₀,h143₀,hretire₀,hvolume,hacc⟩ := retainedBoundaryPublished_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad F hF v S tail
    h109 h115 h116 hleft hready haMaster hbMaster h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  let G := boundarySolutionField B solution
  let sourceTail := bandTableWords A w B (12*band+1) columns 0++cstream A w (chirpLine s D)++S.R 132
  refine ⟨solution,?_⟩
  intro x hx
  obtain ⟨herror,hreal,hmag,hfit⟩ := hacc x hx
  have hsource : S.R 110 = cstream A w (chirpLine s F)++tail := hready.source
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hw : 1 ≤ w := by omega
  have hboundary : ∀ i ∈ B, |(value q (G i)).re-x i| ≤ 3/(2 : ℝ)^solveTarget := by
    intro i hi
    have hh := herror i hi
    rw [h132] at hh
    rw [publishedCellRead_encodedField (q := q) (w := w) (by omega : 4 ≤ A) hw G sourceTail hfit i] at hh
    exact hh
  have hresidual : (cstream A w (chirpLine s
      (guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (F i))))).length = s*w := by
    simp [hwq,chirpLine]
  have hready₀' : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u band 0 0
      (cstream A w (chirpLine s (guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (F i))))++
        (cstream A w (chirpLine s F)++tail))
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S₀)))) := by
    rw [← hsource,← h110]
    exact hready₀
  obtain ⟨v₁,n₁,E,hu₁,hn₁,he₁,hfinal⟩ := physicalRecoveryPublishedHalo_at_precision (body := body)
    (target := target) (workingTarget := bits) (rhsExp := 2)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad G F x
    (3/(2 : ℝ)^solveTarget) (by positivity) (boundaryRecovery_workingTarget p target B.card)
    (boundaryRecovery_error_budget p target) hF (fun i _ => hreal i) hboundary hx
    v₀ S₀ _ tail sourceTail hresidual hready₀' ha₀ hb₀ h132 h127₀ h138₀ h143₀
  let R := couplingRowField (2^15*p) q t u band a b true G F
  let Y := fun i => realPartWord (publicationField t band a b E G i)
  let S₁ : Stacks 224 A := {S₀ with R := (Function.update
    (Function.update S₀.R 110 (cstream A w (chirpLine s R)++(cstream A w (chirpLine s F)++tail)))
    132 (cstream A w (chirpLine s Y)++sourceTail))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retirePublishedBoundary_exec_bounded (body := embTab boundaryFactorLegacyReg
    (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    B (12*band+1) w columns hcols (cstream A w (chirpLine s Y)) (cstream A w (chirpLine s D))
    (S.R 132) (by simp [chirpLine]) (by simp [chirpLine]) v₁ S₁
    (by simpa [S₁] using hretire₀.ambient) (by simpa [S₁] using hretire₀.band)
    (by simpa [S₁] using hretire₀.rows) (by simpa [S₁] using hretire₀.width)
    (by simp [S₁,sourceTail,List.append_assoc]) (by
      intro i hi
      have hi110 : i ≠ 110 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hi132 : i ≠ 132 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [S₁,hi110,hi132] using hretire₀.scratch i hi)
  have hn₂' : n₂ ≤ haloBoundaryRetirementCostBound s t band a b w :=
    hn₂.trans (haloBoundary_retirement_cost_le hst band a b w)
  let S₂ : Stacks 224 A := {S₀ with R := (Function.update
    (Function.update S₀.R 110 (cstream A w (chirpLine s R)++(cstream A w (chirpLine s F)++tail)))
    132 (cstream A w (chirpLine s Y)++S.R 132))}
  have he₂' : Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) retirePublishedBoundary (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h132' : i = 132 <;> simp [S₂,S₁,h132']
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseBoundaryWorkspace_exec (body := embTab boundaryFactorLegacyReg
    (embTab tableReg (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))))
    s w (cstream A w (chirpLine s R)) (cstream A w (chirpLine s F)++tail) v₂ S₂
    (by simpa [S₂] using hretire₀.ambient) (by simpa [S₂] using hretire₀.width)
    (by simp [S₂]) (by simp [chirpLine])
    (by simpa [S₂] using hretire₀.scratch 131 (by simp))
    (by simpa [S₂] using hretire₀.scratch 134 (by simp))
    (by simpa [S₂] using hretire₀.scratch 135 (by simp))
  have hn₃' : n₃ ≤ releaseBoundaryWorkspaceCostBound s w (publicationGeometryWidth t band) B.card
      (boundaryPermanentSizeBound q band B.card) :=
    hn₃.trans (releaseBoundaryWorkspaceCost_le S₀ hvolume)
  refine ⟨v₃,n₀+(n₁+(n₂+n₃)),E,hu₃.trans (hu₂.trans (hu₁.trans hu₀)),?_,
    (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂' he₃))).cast rfl ?_,?_⟩
  · have hh := Nat.add_le_add hn₁ (Nat.add_le_add hn₂' hn₃')
    simpa only [retainedBoundaryRecoveredCost,Nat.add_assoc] using Nat.add_le_add hn₀ hh
  · apply congrArg (mk v₃)
    refine Stacks.ext hinp hout hL ?_
    funext i
    by_cases hiOwned : i ∈ boundaryOwnedRegs
    · have hi132 : i ≠ 132 := by
        rw [boundaryOwnedRegs_mem] at hiOwned
        rcases hiOwned with rfl | rfl | hiOwned <;> simp_all [Fin.ext_iff] <;> omega
      have hblank : S.R i = [] := by
        rw [boundaryOwnedRegs_mem] at hiOwned
        rcases hiOwned with rfl | rfl | hi
        · exact h115
        · exact h116
        · exact hnew i hi
      simp [hiOwned,hi132,hblank]
    · have hi115 : i ≠ 115 := by intro h; apply hiOwned; simp [h]
      have hi116 : i ≠ 116 := by intro h; apply hiOwned; simp [h]
      have hi154 : i.val < 154 := by
        by_contra h
        apply hiOwned
        rw [boundaryOwnedRegs_mem]
        exact Or.inr (Or.inr (by omega))
      by_cases hi110 : i = 110
      · subst i; simp [hiOwned,hsource]
      by_cases hi132 : i = 132
      · subst i; simp [hiOwned,S₂]; rfl
      have hf : S₀.R i = S.R i := hframe₀ ⟨i.val,hi154⟩
        (by simpa [Fin.ext_iff] using hi110) (by simpa [Fin.ext_iff] using hi115)
        (by simpa [Fin.ext_iff] using hi116) (by simpa [Fin.ext_iff] using hi132)
      simpa [hiOwned,hi110,hi132,S₂] using hf
  · intro i hi
    have hh := hfinal i hi
    change ‖publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s Y)++S.R 132) i-x i‖ ≤ _
    change ‖publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s Y)++sourceTail) i-x i‖ ≤ _ at hh
    simpa only [publishedCellRead,ZMod.val_zero,Nat.sub_zero,
      cstream_word w (chirpLine s Y) (S.R 132) i.val (by simpa using i.val_lt),
      cstream_word w (chirpLine s Y) sourceTail i.val (by simpa using i.val_lt)] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
