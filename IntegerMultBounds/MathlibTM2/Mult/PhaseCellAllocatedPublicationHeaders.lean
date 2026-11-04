module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedGatherBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders

/-! Load publication metadata only after numerical routing has restored its
fresh suffix. Retained caller words may be unary, binary or origin packets. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
open PackedTranspose
noncomputable section
variable {T Q A : ℕ} {P U : Type}

/-- Sources: a, b, capacity, replicas, core length, word width, row count,
geometry width, ambient length, origins, and three binary transpose dimensions. -/
def publicationHeaderAssignments : List (Fin 13 × Fin 117) :=
  [(0,61),(1,62),(2,60),(3,59),(4,33),(5,34),(6,36),
   (7,35),(8,79),(9,109),(10,82),(11,83),(12,84)]

def publicationHeaderCopies (src : Fin 13 → Fin T) : List (Fin (T+PackedTranspose.tapeCount) × Fin (T+PackedTranspose.tapeCount)) :=
  publicationHeaderAssignments.map fun r => (Fin.castAdd PackedTranspose.tapeCount (src r.1),Fin.natAdd T (publicationReg r.2))

def loadPublicationHeaders (src : Fin 13 → Fin T) : Pr P (T+PackedTranspose.tapeCount) Q A U :=
  copyWordHeaders (Fin.natAdd T (publicationReg 112)) (Fin.natAdd T (publicationReg 113)) (publicationHeaderCopies src)

def loadedPublicationHeaders (src : Fin 13 → Fin T) (S : Stacks (T+PackedTranspose.tapeCount) A) :=
  {S with R := copyWordHeadersR S.R (publicationHeaderCopies src) S.R}

theorem loadedPublicationHeaders_read (src : Fin 13 → Fin T)
    (S : Stacks (T+PackedTranspose.tapeCount) A)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (r : Fin 13 × Fin 117) (hr : r ∈ publicationHeaderAssignments) :
    (loadedPublicationHeaders src S).R (Fin.natAdd T (publicationReg r.2)) =
      S.R (Fin.castAdd PackedTranspose.tapeCount (src r.1)) := by
  have hnd : ((publicationHeaderCopies src).map Prod.snd).Nodup := by
    simp [publicationHeaderCopies,publicationHeaderAssignments,List.nodup_cons,publicationReg_injective.eq_iff]
  have hh := copyWordHeadersR_get S.R (publicationHeaderCopies src) hnd S.R
    (Fin.castAdd PackedTranspose.tapeCount (src r.1),Fin.natAdd T (publicationReg r.2)) (List.mem_map.mpr ⟨r,hr,rfl⟩)
  simpa only [loadedPublicationHeaders,hblank _,List.append_nil] using hh

theorem loadPublicationHeaders_exec_within
    (body : P → Pr P (T+PackedTranspose.tapeCount) Q A U) (src : Fin 13 → Fin T)
    (v : HS (T+PackedTranspose.tapeCount) Q A U) (S : Stacks (T+PackedTranspose.tapeCount) A)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (depth : ℕ) :
    let cost := ((publicationHeaderCopies src).map (fun r => 6*(S.R r.1).length+6)).sum+1
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*cost) depth
        (loadPublicationHeaders src) (mk v S) cost (mk v' (loadedPublicationHeaders src S)) ∧
      (∀ r ∈ publicationHeaderAssignments, (loadedPublicationHeaders src S).R (Fin.natAdd T (publicationReg r.2)) =
        S.R (Fin.castAdd PackedTranspose.tapeCount (src r.1))) ∧
      (∀ k : Fin T, (loadedPublicationHeaders src S).R (Fin.castAdd PackedTranspose.tapeCount k) = S.R (Fin.castAdd PackedTranspose.tapeCount k)) := by
  dsimp only
  have hregs : ∀ r ∈ publicationHeaderCopies src,
      [r.1,r.2,Fin.natAdd T (publicationReg 112),Fin.natAdd T (publicationReg 113)].Nodup := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    have h112 : p.2 ≠ 112 := by
      simp only [publicationHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h113 : p.2 ≠ 113 := by
      simp only [publicationHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [List.nodup_cons,prefix_ne_routing,publicationReg_injective.eq_iff,h112,h113]
  have hsep : ∀ r ∈ publicationHeaderCopies src, ∀ p ∈ publicationHeaderCopies src, r.2 ≠ p.1 := by
    intro r hr p hp
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hp
    exact (prefix_ne_routing _ _).symm
  obtain ⟨v',hu,he⟩ := copyWordHeaders_exec (body := body) (Fin.natAdd T (publicationReg 112))
    (Fin.natAdd T (publicationReg 113)) (publicationHeaderCopies src) hregs hsep S.R v S (by intros; rfl)
    (hblank _) (hblank _)
  refine ⟨v',hu,mn_native_exec_within he 2 (copyWordHeaders_native _ _ _) depth _ (by omega),?_,?_⟩
  · exact loadedPublicationHeaders_read src S hblank
  · intro k
    apply copyWordHeadersR_off
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact (prefix_ne_routing _ _).symm

/-- Publication masters never occupy either data port. -/
theorem publicationHeaderAssignments_off_ports (r : Fin 13 × Fin 117)
    (hr : r ∈ publicationHeaderAssignments) : r.2 ≠ 95 ∧ r.2 ≠ 96 := by
  simp only [publicationHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The loader supplies the exact projected bank read by publication, even
when its two data ports are redirected into the caller prefix. -/
theorem loadedPublicationHeaders_project_read (src : Fin 13 → Fin T)
    (S : Stacks (T+tapeCount) A) (hblank : ∀ i, S.R (Fin.natAdd T i) = [])
    (inputPort outputPort : Fin T) (r : Fin 13 × Fin 117)
    (hr : r ∈ publicationHeaderAssignments) :
    (embStk (publicationPlacement inputPort outputPort) (loadedPublicationHeaders src S)).R
      (publicationReg r.2) = S.R (Fin.castAdd tapeCount (src r.1)) := by
  have hoff := publicationHeaderAssignments_off_ports r hr
  have hnum : publicationReg r.2 ≠ numericalPort := publicationReg_injective.ne hoff.1
  have hout : publicationReg r.2 ≠ ambientPort := publicationReg_injective.ne hoff.2
  change (loadedPublicationHeaders src S).R (publicationPlacement inputPort outputPort (publicationReg r.2)) = _
  rw [publicationPlacement_private _ _ _ hnum hout]
  exact loadedPublicationHeaders_read src S hblank r hr

/-- Numerical output may be written before loading the publication bank. -/
theorem loadedPublicationHeaders_update_prefix (src : Fin 13 → Fin T)
    (S : Stacks (T+tapeCount) A) (k : Fin T) (xs : List (Fin (A+4)))
    (hoff : ∀ i, src i ≠ k) :
    loadedPublicationHeaders src {S with R := Function.update S.R (Fin.castAdd tapeCount k) xs} =
      {loadedPublicationHeaders src S with R := (Function.update
        (loadedPublicationHeaders src S).R (Fin.castAdd tapeCount k) xs)} := by
  refine Stacks.ext rfl rfl rfl ?_
  apply copyWordHeadersR_update_off
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact ⟨(Fin.castAdd_injective _ _).ne (hoff p.1),(prefix_ne_routing _ _).symm⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
