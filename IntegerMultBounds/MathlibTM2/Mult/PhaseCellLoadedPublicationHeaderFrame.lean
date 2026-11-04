module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControlPlacement

/-! Freshness after copying publication masters follows from one structural
frame over the assignment list. The queue is the only shared worker register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open FixedStreamedBank PackedTranspose
noncomputable section
variable {T A : ℕ}

theorem loadedPublicationHeaders_off (src : Fin 10 → Fin T) (S : Stacks (T+PackedTranspose.tapeCount) A)
    (k : Fin PackedTranspose.tapeCount) (hoff : ∀ r ∈ publicationHeaderAssignments, publicationReg r.2 ≠ k) :
    (loadedPublicationHeaders src S).R (Fin.natAdd T k) = S.R (Fin.natAdd T k) := by
  apply copyWordHeadersR_off
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact (Fin.natAdd_injective _ _).ne (hoff p hp)

theorem loadedPublicationHeaders_project_fresh (src : Fin 10 → Fin T)
    (S : Stacks (T+PackedTranspose.tapeCount) A) (hblank : ∀ i, S.R (Fin.natAdd T i) = [])
    (inputPort outputPort : Fin T) (k : Fin PackedTranspose.tapeCount)
    (hnum : k ≠ numericalPort) (hout : k ≠ ambientPort)
    (hoff : ∀ r ∈ publicationHeaderAssignments, publicationReg r.2 ≠ k) :
    (embStk (publicationPlacement inputPort outputPort) (loadedPublicationHeaders src S)).R k = [] := by
  change (loadedPublicationHeaders src S).R (publicationPlacement inputPort outputPort k) = []
  rw [publicationPlacement_private _ _ _ hnum hout,loadedPublicationHeaders_off src S k hoff,hblank]

theorem loadedPublicationHeaders_generator_fresh (src : Fin 10 → Fin T)
    (S : Stacks (T+PackedTranspose.tapeCount) A) (hblank : ∀ i, S.R (Fin.natAdd T i) = [])
    (inputPort outputPort : Fin T) (i : Fin 117) (hnum : i ≠ 95) (hout : i ≠ 96)
    (hoff : ∀ r ∈ publicationHeaderAssignments, r.2 ≠ i) :
    (embStk (publicationPlacement inputPort outputPort) (loadedPublicationHeaders src S)).R (publicationReg i) = [] :=
  loadedPublicationHeaders_project_fresh src S hblank inputPort outputPort _
    (publicationReg_injective.ne hnum) (publicationReg_injective.ne hout)
    (fun r hr => publicationReg_injective.ne (hoff r hr))

theorem publicationHeaderAssignments_lower (r : Fin 10 × Fin 117)
    (hr : r ∈ publicationHeaderAssignments) : 33 ≤ r.2.val := by
  simp only [publicationHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem loadedPublicationHeaders_small_fresh (src : Fin 10 → Fin T)
    (S : Stacks (T+PackedTranspose.tapeCount) A) (hblank : ∀ i, S.R (Fin.natAdd T i) = [])
    (inputPort outputPort : Fin T) (i : Fin 117) (hi : i.val < 33) :
    (embStk (publicationPlacement inputPort outputPort) (loadedPublicationHeaders src S)).R (publicationReg i) = [] := by
  apply loadedPublicationHeaders_generator_fresh src S hblank inputPort outputPort i
  · intro he; subst i; norm_num at hi
  · intro he; subst i; norm_num at hi
  · intro r hr he
    have hb := publicationHeaderAssignments_lower r hr
    rw [he] at hb
    omega

theorem loadedPublicationHeaders_extra_fresh (src : Fin 10 → Fin T)
    (S : Stacks (T+PackedTranspose.tapeCount) A) (hblank : ∀ i, S.R (Fin.natAdd T i) = [])
    (inputPort outputPort : Fin T) (i : Fin 7) :
    (embStk (publicationPlacement inputPort outputPort) (loadedPublicationHeaders src S)).R (extra i) = [] :=
  loadedPublicationHeaders_project_fresh src S hblank inputPort outputPort _
    (base_extra _ _).symm (base_extra _ _).symm (fun _ _ => base_extra _ _)

theorem loadedPublicationHeaders_worker_fresh (src : Fin 10 → Fin T)
    (S : Stacks (T+PackedTranspose.tapeCount) A) (hblank : ∀ i, S.R (Fin.natAdd T i) = [])
    (inputPort outputPort : Fin T) (i : Fin FixedStreamedBank.tapeCount) (hi : i ≠ FixedStreamedBank.control 7) :
    (embStk (publicationPlacement inputPort outputPort) (loadedPublicationHeaders src S)).R (base (callerWorker i)) = [] := by
  apply loadedPublicationHeaders_project_fresh src S hblank inputPort outputPort
  · exact (base_injective.ne (TransposeRegisterPlacement.generator_off_worker _ 95 (by decide) i)).symm
  · exact (base_injective.ne (TransposeRegisterPlacement.generator_off_worker _ 96 (by decide) i)).symm
  · intro r _
    apply base_injective.ne
    by_cases hq : r.2 = 109
    · simpa only [hq,callerGenerator,TransposeRegisterPlacement.generator_queue,callerWorker] using
        TransposeRegisterPlacement.worker_injective.ne hi.symm
    · exact TransposeRegisterPlacement.generator_off_worker _ _ hq i

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
