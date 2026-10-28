module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBatchCoreReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseCaller

/-! One scalar-header installation prepares a whole batch and preserves its clock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

structure FamilyBatchHeaders {A W p u l target s t a b replicas : ℕ} [NeZero s]
    (recovery : Bool) (wl input : List (Fin (A+4)))
    (original : Stacks 303 A) (scalars : TblSt 25 A) (S : Stacks 303 A) : Prop where
  scalarBank : tblHolds familyInverseScalarReg S (tblRho W wl [] scalars)
  keep : ∀ i : Fin 8, scalars.val ⟨i.val,by omega⟩ = (inverseInputScalars (A := A) p u l target s t a b).val ⟨i.val,by omega⟩
  accumulator : scalars.acc = (inverseInputScalars (A := A) p u l target s t a b).acc
  fits : ∀ i, scalars.val i < 2^W
  inp : S.inp = original.inp
  out : S.out = original.out
  left : S.L = original.L
  headers : ∀ i, S.R (familyInverseMasterPort i) = List.replicate (inverseMasterValues p u l target s t a b i) Node.tick
  frame : ∀ k, (∀ r, familyInverseScalarReg r ≠ k) → (∀ i, familyInverseMasterPort i ≠ k) → S.R k = original.R k
  core : FamilyBatchCoreReady recovery p u l target s t a b replicas input S

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

theorem familyBatchHeaders_install_spec (recovery : Bool)
    {W p u l target s t a b replicas : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W)
    (v : HS 303 Q A U) (S : Stacks 303 A) (input wl : List (Fin (A+4))) (hwl : wl.length = W)
    (hscalar : tblHolds familyInverseScalarReg S (tblRho W wl [] (inverseInputScalars p u l target s t a b)))
    (hleft : ∀ i, S.L (familyInverseCoreReg i) = [])
    (hblank : ∀ i, i ≠ 110 → i ≠ 132 → i ≠ 246 → S.R (familyInverseCoreReg i) = [])
    (hsource : S.R 110 = input) (hcount : (S.R (familyInverseCoreReg 246)).length = replicas) :
    ∃ v' S' n scalars, v'.user = v.user ∧
      n ≤ inverseScalarAtoms p s t u a b*tblC W 0+
        inverseMasterCopyCost W (inverseMasterValues p u l target s t a b) ∧
      Exec body (installInverseHeaders familyInverseScalarReg familyInverseMasterPort) (mk v S) n (mk v' S') ∧
      FamilyBatchHeaders (W := W) (p := p) (u := u) (l := l) (target := target)
        (s := s) (t := t) (a := a) (b := b) (replicas := replicas) recovery wl input S scalars S' := by
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let E := inverseExecutionExponent p l target B.card (PhaseCellBand.width p u)
  let initial : TblSt 25 A := inverseInputScalars p u l target s t a b
  have hfit : ∀ i, initial.val i < 2^W := by
    have hroom : 2^15*(p+1)+8*E+2*(B.card+1)+4*(PhaseCellBand.width p u+1)+9 < 2^W := hprecisionRoom
    have hEl : 2*l+target ≤ E := by dsimp [E,inverseExecutionExponent]; omega
    have htW : t < 2^W := by nlinarith only [hgeometryRoom,Nat.zero_le (t*t)]
    have hsW : s < 2^W := by omega
    intro i
    fin_cases i <;> simp [initial,inverseInputScalars] <;> omega
  obtain ⟨v₁,S₁,n₁,scalars,hu₁,hn₁,he₁,hh₁,hkeep,hacc,hfit₁,hinp,hout,hL,hheaders,hframe⟩ :=
    installInverseHeaders_exec (body := body) (p := p) (u := u) (l := l) (target := target)
      (s := s) (t := t) (a := a) (b := b)
      familyInverseScalarReg familyInverseScalarReg_injective
      familyInverseMasterPort familyInverseMasterPort_injective familyInverseScalarReg_master
      wl hwl initial rfl rfl rfl rfl rfl rfl rfl rfl hst ha hb hband
      hbandRoom hgeometryRoom hprecisionRoom hfit v S hscalar
  have hmaster (i : Fin 10) : familyInverseMasterPort i =
      familyInverseCoreReg (familyBoundaryReg (sharedPageRecoveryReg (inverseMasterCorePort i))) :=
    (familyInverseCoreReg_legacy (inverseMasterCorePort i)).symm
  have hclean (k : Fin 263)
      (hk : ∀ i, familyBoundaryReg (sharedPageRecoveryReg (inverseMasterCorePort i)) ≠ k)
      (h110 : k ≠ 110) (h132 : k ≠ 132) (h246 : k ≠ 246) : S₁.R (familyInverseCoreReg k) = [] := by
    apply (hframe _ (fun r => familyInverseScalarReg_core r k) ?_).trans (hblank k h110 h132 h246)
    intro i he
    exact hk i (familyInverseCoreReg_injective ((hmaster i).symm.trans he))
  have hhead (i : Fin 10) : S₁.R (familyInverseMasterPort i) =
      List.replicate (inverseMasterValues p u l target s t a b i) Node.tick := by
    have hb := hblank (familyBoundaryReg (sharedPageRecoveryReg (inverseMasterCorePort i)))
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
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
    · intro he
      have hv := congrArg Fin.val he
      change k.val = 246 at hv
      have := k.isLt
      omega
  have hsource₁ : S₁.R (familyInverseSetupReg (inverseCoreReg 110)) =
      input :=
    (hframe _ (fun r => familyInverseScalarReg_core r 110)
      (by intro i; fin_cases i <;> decide)).trans hsource
  have hready := familyInverseHeaders_ready S₁ (input)
    hlegacyLeft hhead hlegacyClean hsource₁
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
    · intro he
      have hv := congrArg Fin.val he
      change i.val = 246 at hv
      have := i.isLt
      omega
  have hcleanLow : ∀ i ∈ ([109,115,116,0,106,139,127,138,143,147,151,153,152,94,131,134,135,136,140] : List (Fin 240)),
      S₁.R (familyInverseCoreReg (familyBoundaryReg i)) = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hclean _ (by intro j; fin_cases j <;> decide) (by decide) (by decide) (by decide)
  have hcount₁ : (S₁.R (familyInverseCoreReg 246)).length = replicas := by
    rw [hframe _ (fun r => familyInverseScalarReg_core r 246) (by intro i; fin_cases i <;> decide)]
    exact hcount
  refine ⟨v₁,S₁,n₁,scalars,hu₁,hn₁,he₁,hh₁,hkeep,hacc,hfit₁,hinp,hout,hL,hhead,hframe,?_⟩
  refine ⟨hready,?_,?_,?_,?_,?_,?_,?_,hcleanLow,hnew,hcount₁,?_,?_⟩
  · exact hclean _ (by cases recovery <;> intro j <;> fin_cases j <;> decide)
      (by cases recovery <;> decide) (by cases recovery <;> decide) (by cases recovery <;> decide)
  · exact hclean _ (by cases recovery <;> intro j <;> fin_cases j <;> decide)
      (by cases recovery <;> decide) (by cases recovery <;> decide) (by cases recovery <;> decide)
  · exact hclean _ (by cases recovery <;> intro j <;> fin_cases j <;> decide)
      (by cases recovery <;> decide) (by cases recovery <;> decide) (by cases recovery <;> decide)
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hclean _ (by intro j; fin_cases j <;> decide) (by decide) (by decide) (by decide)
  · intro i
    change S₁.L _ = []
    rw [hL]
    exact hleft _
  · simpa [familyInverseMasterPort,familyInverseSetupReg,inverseMasterPort,inverseCoreReg,
      familyInverseCoreReg,inverseMasterCorePort,inverseMasterValues,embStk,familyBoundaryReg,
      familyInverseLegacyReg,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg]
      using congrArg List.length (hhead 8)
  · simpa [familyInverseMasterPort,familyInverseSetupReg,inverseMasterPort,inverseCoreReg,
      familyInverseCoreReg,inverseMasterCorePort,inverseMasterValues,embStk,familyBoundaryReg,
      familyInverseLegacyReg,couplingBoundaryReg,couplingCacheLegacyReg,sharedComplexBatchCoreReg]
      using congrArg List.length (hhead 9)
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hclean _ (by intro j; fin_cases j <;> decide) (by decide) (by decide) (by decide)
  · exact hclean 137 (by intro j; fin_cases j <;> decide) (by decide) (by decide) (by decide)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
