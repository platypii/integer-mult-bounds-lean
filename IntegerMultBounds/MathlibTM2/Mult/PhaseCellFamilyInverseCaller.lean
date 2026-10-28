module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedInverseCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseCoreCall
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseHeadersReady

/-! A raw-scalar inverse caller: generate readiness, execute the retained solver, and release every generated header. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open IntegerMultBounds.MathlibTM2.Fast.Main

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

noncomputable def familyInverseCallerCost (A W p u l target s t : ℕ) [NeZero s] : ℕ :=
  inverseScalarAtoms p s t u 0 s*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
    (generatedClosedFamilyComplexBatchCost A p u l s t 0 s target 1+5)+
    inverseReleaseCost W (inverseMasterValues p u l target s t 0 s)

noncomputable def familyInverseCallerStockCost (A W p u l target s t : ℕ) [NeZero s] : ℕ :=
  (inverseScalarAtoms p s t u 0 s*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s))+
    (1+generatedClosedFamilyComplexBatchStockCost A p u l s t 0 s target 1+4)+
    inverseReleaseCost W (inverseMasterValues p u l target s t 0 s)

theorem familyInverseCaller_sized_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {W p u l target s t : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) 0 s).card
      (PhaseCellBand.width p u) < 2^W)
    (F : ZMod s → GaussianInt)
    (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 303 Q A U) (S : Stacks 303 A) (tail wl : List (Fin (A+4))) (hwl : wl.length = W)
    (hscalar : tblHolds familyInverseScalarReg S (tblRho W wl [] (inverseInputScalars p u l target s t 0 s)))
    (hleft : ∀ i, S.L (familyInverseCoreReg i) = [])
    (hblank : ∀ i, i ≠ 110 → i ≠ 132 → S.R (familyInverseCoreReg i) = [])
    (hsource : S.R 110 = cstream A (executionWidth p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2)
        (chirpLine s F)++tail) :
    let B := haloBoundary s t (PhaseCellBand.width p u) 0 s
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ z : ZMod s → ℂ,
      Matrix.mulVec (fun i j => (realMatrix s t p u i j : ℂ)) z = (fun i => value q (F i)) →
      ∃ v' n, ∃ G : ZMod s → GaussianInt,
        v'.user = v.user ∧ n ≤ familyInverseCallerCost A W p u l target s t ∧
        Exec body
          (familyInverseCaller recovery hR hQ) (mk v S) n
          (mk v' {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)}) ∧
        (∀ i, ‖pairedCellRead q w (cstream A w (chirpLine s G)++S.R 132) i-z i‖ ≤ 1/(2 : ℝ)^target) ∧
        ∀ C, mnProgPush (familyInverseCaller (P := P) (U := U) (A := A) recovery hR hQ) ≤ C →
          (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
          ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
            (C+1)*familyInverseCallerStockCost A W p u l target s t)
            depth (familyInverseCaller recovery hR hQ) (mk v S) n
            (mk v' {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)}) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) 0 s
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let E := inverseExecutionExponent p l target B.card (PhaseCellBand.width p u)
  let initial : TblSt 25 A := inverseInputScalars p u l target s t 0 s
  have hfit : ∀ i, initial.val i < 2^W := by
    have hroom : 2^15*(p+1)+8*E+2*(B.card+1)+4*(PhaseCellBand.width p u+1)+9 < 2^W := hprecisionRoom
    have hEl : 2*l+target ≤ E := by dsimp [E,inverseExecutionExponent]; omega
    have htW : t < 2^W := by nlinarith only [hgeometryRoom,Nat.zero_le (t*t)]
    have hsW : s < 2^W := by omega
    intro i
    fin_cases i <;> simp [initial,inverseInputScalars] <;> omega
  obtain ⟨v₁,S₁,n₁,scalars,hu₁,hn₁,he₁,hh₁,hkeep,hacc,hfit₁,hinp,hout,hL,hheaders,hframe⟩ :=
    installInverseHeaders_exec (body := body) (p := p) (u := u) (l := l) (target := target)
      (s := s) (t := t) (a := 0) (b := s)
      familyInverseScalarReg familyInverseScalarReg_injective
      familyInverseMasterPort familyInverseMasterPort_injective familyInverseScalarReg_master
      wl hwl initial rfl rfl rfl rfl rfl rfl rfl rfl hst (Nat.zero_le s) (le_refl s) hband
      hbandRoom hgeometryRoom hprecisionRoom hfit v S hscalar
  have hmaster (i : Fin 10) : familyInverseMasterPort i =
      familyInverseCoreReg (familyBoundaryReg (sharedPageRecoveryReg (inverseMasterCorePort i))) :=
    (familyInverseCoreReg_legacy (inverseMasterCorePort i)).symm
  have hclean (k : Fin 263)
      (hk : ∀ i, familyBoundaryReg (sharedPageRecoveryReg (inverseMasterCorePort i)) ≠ k)
      (h110 : k ≠ 110) (h132 : k ≠ 132) : S₁.R (familyInverseCoreReg k) = [] := by
    apply (hframe _ (fun r => familyInverseScalarReg_core r k) ?_).trans (hblank k h110 h132)
    intro i he
    exact hk i (familyInverseCoreReg_injective ((hmaster i).symm.trans he))
  have hhead (i : Fin 10) : S₁.R (familyInverseMasterPort i) =
      List.replicate (inverseMasterValues p u l target s t 0 s i) Node.tick := by
    have hb := hblank (familyBoundaryReg (sharedPageRecoveryReg (inverseMasterCorePort i)))
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    simpa only [hmaster,hb,List.append_nil] using hheaders i
  have hlegacyLeft (k : Fin 224) : S₁.L (familyInverseSetupReg (inverseCoreReg k)) = [] := by
    rw [hL,← familyInverseCoreReg_legacy]
    exact hleft _
  have hlegacyClean (k : Fin 224) (hk : ∀ i, inverseMasterCorePort i ≠ k)
      (h110 : k ≠ 110) (h132 : k ≠ 132) :
      S₁.R (familyInverseSetupReg (inverseCoreReg k)) = [] := by
    rw [← familyInverseCoreReg_legacy]
    apply hclean
    · intro i he
      exact hk i (sharedPageRecoveryReg_injective (familyBoundaryReg_injective he))
    · intro he
      exact h110 (sharedPageRecoveryReg_injective (familyBoundaryReg_injective he))
    · intro he
      exact h132 (sharedPageRecoveryReg_injective (familyBoundaryReg_injective he))
  have hsource₁ : S₁.R (familyInverseSetupReg (inverseCoreReg 110)) =
      cstream A w (chirpLine s F)++tail :=
    (hframe _ (fun r => familyInverseScalarReg_core r 110)
      (by intro i; fin_cases i <;> decide)).trans hsource
  have hready := familyInverseHeaders_ready S₁ (cstream A w (chirpLine s F)++tail)
    hlegacyLeft hhead hlegacyClean hsource₁
  have hready' : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
      q l s t u (PhaseCellBand.width p u) 0 0 (cstream A w (chirpLine s F)++tail)
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk familyBoundaryReg (embStk familyInverseCoreReg S₁))))))) := by
    simpa only [q,bits,B,executionPrecision,executionStagePrecision,← inverseExecutionExponent_eq] using hready
  have hnew : ∀ i : Fin 240, 154 ≤ i.val → S₁.R (familyInverseCoreReg (familyBoundaryReg i)) = [] := by
    intro i hi
    apply hclean (familyBoundaryReg i)
    · intro j he
      have hv := congrArg (fun k : Fin 263 => k.val) he
      have hlt : (familyBoundaryReg (sharedPageRecoveryReg (inverseMasterCorePort j))).val < 154 := by fin_cases j <;> decide
      change _ = i.val at hv
      omega
    · intro he
      have hv := congrArg Fin.val he
      change i.val = 110 at hv
      omega
    · intro he
      have hv := congrArg Fin.val he
      change i.val = 132 at hv
      omega
  have hcleanLow : ∀ i ∈ ([109,115,116,0,106,139,127,138,143,147,151,153,152,94,131,134,135,136,140] : List (Fin 240)),
      S₁.R (familyInverseCoreReg (familyBoundaryReg i)) = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hclean _ (by intro j; fin_cases j <;> decide) (by decide) (by decide)
  intro z hz
  obtain ⟨v₂,n₂,G,hu₂,hn₂,he₂,herror,htrace⟩ := familyInverseCoreCall_full_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband hpad F hF v₁ S₁ tail hready'
    (hclean _ (by cases recovery <;> intro j <;> fin_cases j <;> decide) (by cases recovery <;> decide) (by cases recovery <;> decide))
    (hclean _ (by cases recovery <;> intro j <;> fin_cases j <;> decide) (by cases recovery <;> decide) (by cases recovery <;> decide))
    (hclean _ (by cases recovery <;> intro j <;> fin_cases j <;> decide) (by cases recovery <;> decide) (by cases recovery <;> decide))
    (by intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals exact hclean _ (by intro j; fin_cases j <;> decide) (by decide) (by decide))
    (by intro i; change S₁.L _ = []; rw [hL]; exact hleft _)
    (by simpa [familyInverseMasterPort,familyInverseSetupReg,inverseMasterPort,inverseCoreReg,
      familyInverseCoreReg,inverseMasterCorePort,inverseMasterValues,embStk,familyBoundaryReg,familyInverseLegacyReg,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using congrArg List.length (hhead 8))
    (by simpa [familyInverseMasterPort,familyInverseSetupReg,inverseMasterPort,inverseCoreReg,
      familyInverseCoreReg,inverseMasterCorePort,inverseMasterValues,embStk,familyBoundaryReg,familyInverseLegacyReg,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg] using congrArg List.length (hhead 9))
    hcleanLow hnew (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hclean _ (by intro j; fin_cases j <;> decide) (by decide) (by decide))
    (hclean 137 (by intro j; fin_cases j <;> decide) (by decide) (by decide)) z hz
  let output := cstream A w (chirpLine s G)++S₁.R 132
  let S₂ : Stacks 303 A := {S₁ with R := Function.update S₁.R 132 output}
  have hh₂ : tblHolds familyInverseScalarReg S₂ (tblRho W wl [] scalars) := by
    intro r
    have hr132 : familyInverseScalarReg r ≠ 132 := familyInverseScalarReg_core r 132
    simpa only [S₂,Function.update_of_ne hr132] using hh₁ r
  have hmasterLen (i : Fin 10) : (S₂.R (familyInverseMasterPort i)).length =
      inverseMasterValues p u l target s t 0 s i := by
    have h132 : familyInverseMasterPort i ≠ 132 := by fin_cases i <;> decide
    simpa only [S₂,Function.update_of_ne h132,List.length_replicate] using congrArg List.length (hhead i)
  obtain ⟨v₃,S₃,n₃,hu₃,hn₃,he₃,hh₃,hinp₃,hout₃,hL₃,hcore₃⟩ :=
    releaseInverseHeaders_exec (body := body) familyInverseScalarReg familyInverseScalarReg_injective
      familyInverseMasterPort familyInverseMasterPort_injective familyInverseScalarReg_master
      wl hwl scalars initial (inverseMasterValues p u l target s t 0 s)
      (fun i hi => hkeep ⟨i.val,hi⟩)
      (by intro i hi; fin_cases i <;> first | (simp at hi; done) | rfl) hacc hfit₁ v₂ S₂ hh₂ hmasterLen
  have h132 : S₁.R 132 = S.R 132 := hframe 132
    (fun r => familyInverseScalarReg_core r 132) (by intro i; fin_cases i <;> decide)
  have hfinal : S₃ = {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)} := by
    refine Stacks.ext (hinp₃.trans hinp) (hout₃.trans hout) (hL₃.trans hL) ?_
    funext k
    rcases familyInverseCallerReg_cover k with ⟨i,rfl⟩ | ⟨r,rfl⟩
    · rw [hcore₃ _ (fun r => familyInverseScalarReg_core r i)]
      by_cases hi132 : familyInverseCoreReg i = 132
      · have hnot : familyInverseCoreReg i ∉ (List.finRange 10).map familyInverseMasterPort := by
          rw [hi132]; decide
        simp only [hnot,ite_false]
        simp only [S₂,hi132,Function.update_self,output,h132]
      by_cases hi : familyInverseCoreReg i ∈ (List.finRange 10).map familyInverseMasterPort
      · have hi110 : i ≠ 110 := by
          intro he; subst i
          obtain ⟨j,_,hj⟩ := List.mem_map.mp hi
          have hne : familyInverseMasterPort j ≠ familyInverseCoreReg 110 := by fin_cases j <;> decide
          exact hne hj
        have hi132' : i ≠ 132 := by intro he; subst i; exact hi132 rfl
        simp [hi,Function.update_of_ne hi132,hblank i hi110 hi132']
      · have hports : ∀ j, familyInverseMasterPort j ≠ familyInverseCoreReg i := by
          intro j he; exact hi (List.mem_map.mpr ⟨j,List.mem_finRange j,he⟩)
        simp only [hi,ite_false,S₂,Function.update_of_ne hi132]
        exact hframe _ (fun r => familyInverseScalarReg_core r i) hports
    · change S₃.R (familyInverseScalarReg r) =
        Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132) (familyInverseScalarReg r)
      rw [hh₃ r]
      have hr132 : familyInverseScalarReg r ≠ 132 := familyInverseScalarReg_core r 132
      rw [Function.update_of_ne hr132]
      exact (hscalar r).symm
  refine ⟨v₃,n₁+(n₂+n₃),G,hu₃.trans (hu₂.trans hu₁),?_,?_,?_,?_⟩
  · simpa only [familyInverseCallerCost,Nat.add_assoc] using Nat.add_le_add hn₁ (Nat.add_le_add hn₂ hn₃)
  · exact (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk v₃) hfinal)
  · intro i
    have hh : ‖pairedCellRead q w (cstream A w (chirpLine s G)++S₁.R 132) i-z i‖ ≤ 1/(2 : ℝ)^target := herror i
    simpa only [h132] using hh
  · intro C hp hb depth
    have ht := mn_lifecycle_exec_within he₁ hn₁ htrace he₃ hn₃ C hp hb depth
    rw [hfinal] at ht
    exact ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
