module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBatchHeaders

/-! Header release restores the raw frame after an arbitrary batch output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

theorem familyBatchHeaders_release_spec
    {W p u l target s t a b replicas : ℕ} [NeZero s]
    {recovery : Bool} {wl input : List (Fin (A+4))}
    {S S₁ : Stacks 303 A} {scalars : TblSt 25 A}
    (prepared : FamilyBatchHeaders (W := W) (p := p) (u := u) (l := l)
      (target := target) (s := s) (t := t) (a := a) (b := b)
      (replicas := replicas) recovery wl input S scalars S₁)
    (hwl : wl.length = W)
    (hscalar : tblHolds familyInverseScalarReg S
      (tblRho W wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ i, i ≠ 110 → i ≠ 132 → i ≠ 246 → S.R (familyInverseCoreReg i) = [])
    (v₂ : HS 303 Q A U) (outputPrefix : List (Fin (A+4))) :
    ∃ v₃ n₃, v₃.user = v₂.user ∧
      n₃ ≤ inverseReleaseCost W (inverseMasterValues p u l target s t a b) ∧
      Exec body (releaseInverseHeaders familyInverseScalarReg familyInverseMasterPort)
        (mk v₂ {S₁ with R := Function.update S₁.R 132 (outputPrefix++S₁.R 132)}) n₃
        (mk v₃ {S with R := Function.update S.R 132 (outputPrefix++S.R 132)}) := by
  let initial : TblSt 25 A := inverseInputScalars p u l target s t a b
  let output := outputPrefix++S₁.R 132
  let S₂ : Stacks 303 A := {S₁ with R := Function.update S₁.R 132 output}
  have hh₂ : tblHolds familyInverseScalarReg S₂ (tblRho W wl [] scalars) := by
    intro r
    have hr132 : familyInverseScalarReg r ≠ 132 := familyInverseScalarReg_core r 132
    simpa only [S₂,Function.update_of_ne hr132] using prepared.scalarBank r
  have hmasterLen (i : Fin 10) : (S₂.R (familyInverseMasterPort i)).length =
      inverseMasterValues p u l target s t a b i := by
    have h132 : familyInverseMasterPort i ≠ 132 := by fin_cases i <;> decide
    simpa only [S₂,Function.update_of_ne h132,List.length_replicate] using congrArg List.length (prepared.headers i)
  obtain ⟨v₃,S₃,n₃,hu₃,hn₃,he₃,hh₃,hinp₃,hout₃,hL₃,hcore₃⟩ :=
    releaseInverseHeaders_exec (body := body) familyInverseScalarReg familyInverseScalarReg_injective
      familyInverseMasterPort familyInverseMasterPort_injective familyInverseScalarReg_master
      wl hwl scalars initial (inverseMasterValues p u l target s t a b)
      (fun i hi => prepared.keep ⟨i.val,hi⟩)
      (by intro i hi; fin_cases i <;> first | (simp at hi; done) | rfl) prepared.accumulator prepared.fits v₂ S₂ hh₂ hmasterLen
  have h132 : S₁.R 132 = S.R 132 := prepared.frame 132
    (fun r => familyInverseScalarReg_core r 132) (by intro i; fin_cases i <;> decide)
  have hfinal : S₃ = {S with R := Function.update S.R 132 (outputPrefix++S.R 132)} := by
    refine Stacks.ext (hinp₃.trans prepared.inp) (hout₃.trans prepared.out) (hL₃.trans prepared.left) ?_
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
        have hi246 : i ≠ 246 := by
          intro he; subst i
          obtain ⟨j,_,hj⟩ := List.mem_map.mp hi
          have hne : familyInverseMasterPort j ≠ familyInverseCoreReg 246 := by fin_cases j <;> decide
          exact hne hj
        simp [hi,Function.update_of_ne hi132,hblank i hi110 hi132' hi246]
      · have hports : ∀ j, familyInverseMasterPort j ≠ familyInverseCoreReg i := by
          intro j he; exact hi (List.mem_map.mpr ⟨j,List.mem_finRange j,he⟩)
        simp only [hi,ite_false,S₂,Function.update_of_ne hi132]
        exact prepared.frame _ (fun r => familyInverseScalarReg_core r i) hports
    · change S₃.R (familyInverseScalarReg r) =
        Function.update S.R 132 (outputPrefix++S.R 132) (familyInverseScalarReg r)
      rw [hh₃ r]
      have hr132 : familyInverseScalarReg r ≠ 132 := familyInverseScalarReg_core r 132
      rw [Function.update_of_ne hr132]
      exact (hscalar r).symm
  exact ⟨v₃,n₃,hu₃,hn₃,he₃.cast rfl (congrArg (mk v₃) hfinal)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
