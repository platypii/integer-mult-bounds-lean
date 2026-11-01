module

public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Place the existing boundary phase beside the recovery masters. Seven
persistent tapes for counters and the mask replace phase-local uses of the master ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def replicaBoundaryPhasePermutation : Equiv.Perm (Fin 255) :=
  (Equiv.swap 117 248).trans ((Equiv.swap 118 249).trans
    ((Equiv.swap 120 250).trans ((Equiv.swap 123 251).trans
      ((Equiv.swap 124 252).trans ((Equiv.swap 116 253).trans (Equiv.swap 167 254))))))

def replicaBoundaryPhaseReg (i : Fin 242) : Fin 255 :=
  replicaBoundaryPhasePermutation (Fin.castLE (by decide) i)

theorem replicaBoundaryPhaseReg_injective : Function.Injective replicaBoundaryPhaseReg := by
  intro i j he
  have hh := replicaBoundaryPhasePermutation.injective he
  exact Fin.ext (congrArg (fun k : Fin 255 => k.val) hh)

theorem replicaBoundaryPhaseReg_fixed (i : Fin 242) (hi : i ∉ [116,117,118,120,123,124,167]) :
    replicaBoundaryPhaseReg i = Fin.castLE (by decide) i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
  have hoff (j : Fin 255) (hj : 242 ≤ j.val) : (Fin.castLE (by decide) i : Fin 255) ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    have hi := i.isLt
    change i.val = j.val at hv
    omega
  have h116 : (Fin.castLE (by decide) i : Fin 255) ≠ 116 := fun h => hi.1 (Fin.ext (congrArg (fun k : Fin 255 => k.val) h))
  have h117 : (Fin.castLE (by decide) i : Fin 255) ≠ 117 := fun h => hi.2.1 (Fin.ext (congrArg (fun k : Fin 255 => k.val) h))
  have h118 : (Fin.castLE (by decide) i : Fin 255) ≠ 118 := fun h => hi.2.2.1 (Fin.ext (congrArg (fun k : Fin 255 => k.val) h))
  have h120 : (Fin.castLE (by decide) i : Fin 255) ≠ 120 := fun h => hi.2.2.2.1 (Fin.ext (congrArg (fun k : Fin 255 => k.val) h))
  have h123 : (Fin.castLE (by decide) i : Fin 255) ≠ 123 := fun h => hi.2.2.2.2.1 (Fin.ext (congrArg (fun k : Fin 255 => k.val) h))
  have h124 : (Fin.castLE (by decide) i : Fin 255) ≠ 124 := fun h => hi.2.2.2.2.2.1 (Fin.ext (congrArg (fun k : Fin 255 => k.val) h))
  have h167 : (Fin.castLE (by decide) i : Fin 255) ≠ 167 := fun h => hi.2.2.2.2.2.2 (Fin.ext (congrArg (fun k : Fin 255 => k.val) h))
  simp [replicaBoundaryPhaseReg,replicaBoundaryPhasePermutation,Equiv.trans_apply,Equiv.swap_apply_def,
    h116,h117,h118,h120,h123,h124,h167,hoff 248 (by decide),hoff 249 (by decide),hoff 250 (by decide),
    hoff 251 (by decide),hoff 252 (by decide),hoff 253 (by decide),hoff 254 (by decide)]

theorem replicaBoundaryPhaseReg_master_off (i : Fin 242) (k : Fin 255)
    (hk : k ∈ [116,117,118,120,123,124,167]) : replicaBoundaryPhaseReg i ≠ k := by
  have hback : ∃ j : Fin 255, 248 ≤ j.val ∧ replicaBoundaryPhasePermutation j = k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨253,by decide,by decide⟩
    · exact ⟨248,by decide,by decide⟩
    · exact ⟨249,by decide,by decide⟩
    · exact ⟨250,by decide,by decide⟩
    · exact ⟨251,by decide,by decide⟩
    · exact ⟨252,by decide,by decide⟩
    · exact ⟨254,by decide,by decide⟩
  obtain ⟨j,hj,hback⟩ := hback
  intro he
  have hh := replicaBoundaryPhasePermutation.injective (he.trans hback.symm)
  have hv := congrArg Fin.val hh
  change i.val = j.val at hv
  have hi := i.isLt
  omega

theorem replicaBoundaryPhaseReg_recovery_scratch_off (i : Fin 242) (k : Fin 255)
    (h242 : 242 ≤ k.val) (h248 : k.val < 248) : replicaBoundaryPhaseReg i ≠ k := by
  have hrange : (replicaBoundaryPhaseReg i).val < 242 ∨ 248 ≤ (replicaBoundaryPhaseReg i).val := by
    by_cases hi : i ∈ [116,117,118,120,123,124,167]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> right <;> decide
    · rw [replicaBoundaryPhaseReg_fixed i hi]
      exact Or.inl i.isLt
  intro he
  have hv := congrArg Fin.val he
  omega

@[simp] theorem replicaBoundaryPhaseReg_count : replicaBoundaryPhaseReg 116 = 253 := by decide
@[simp] theorem replicaBoundaryPhaseReg_mask : replicaBoundaryPhaseReg 167 = 254 := by decide

@[simp] theorem replicaBoundaryPhaseReg_floor : replicaBoundaryPhaseReg 117 = 248 := by decide
@[simp] theorem replicaBoundaryPhaseReg_parity : replicaBoundaryPhaseReg 118 = 249 := by decide
@[simp] theorem replicaBoundaryPhaseReg_bytes : replicaBoundaryPhaseReg 120 = 250 := by decide
@[simp] theorem replicaBoundaryPhaseReg_volume : replicaBoundaryPhaseReg 123 = 251 := by decide
@[simp] theorem replicaBoundaryPhaseReg_rhsVolume : replicaBoundaryPhaseReg 124 = 252 := by decide

theorem replicaBoundaryPhase_master_frame {A : ℕ} (S : Stacks 255 A) (F : Stacks 242 A)
    (k : Fin 255) (hk : k ∈ [116,117,118,120,123,124,167]) :
    (embOvr replicaBoundaryPhaseReg F.get S).L k = S.L k ∧
      (embOvr replicaBoundaryPhaseReg F.get S).R k = S.R k :=
  embOvr_off F.get S (fun i => replicaBoundaryPhaseReg_master_off i k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
