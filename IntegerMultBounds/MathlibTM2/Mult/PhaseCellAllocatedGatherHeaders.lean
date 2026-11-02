module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedGatherBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders

/-! Load the allocated routing bank from seven retained caller words. One
width word supplies both width ports; all sources and shared scratch survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
open PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ} {P U : Type}

def gatherHeaderAssignments : List (Fin 7 × Fin 117) :=
  [(0,32),(1,33),(2,34),(3,35),(4,37),(4,115),(5,87),(6,83)]

def gatherHeaderCopies (src : Fin 7 → Fin T) : List (Fin (T+PackedTranspose.tapeCount) × Fin (T+PackedTranspose.tapeCount)) :=
  gatherHeaderAssignments.map fun r => (Fin.castAdd PackedTranspose.tapeCount (src r.1),Fin.natAdd T (headerReg r.2))

def loadGatherHeaders (src : Fin 7 → Fin T) : Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U :=
  copyWordHeaders (Fin.natAdd T (headerReg 46)) (Fin.natAdd T (headerReg 47)) (gatherHeaderCopies src)

def loadedGatherHeaders (src : Fin 7 → Fin T) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K)) :=
  {S with R := copyWordHeadersR S.R (gatherHeaderCopies src) S.R}

theorem loadedGatherHeaders_read (src : Fin 7 → Fin T)
    (S : Stacks (T+PackedTranspose.tapeCount) (prime+K))
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (r : Fin 7 × Fin 117) (hr : r ∈ gatherHeaderAssignments) :
    (loadedGatherHeaders src S).R (Fin.natAdd T (headerReg r.2)) =
      S.R (Fin.castAdd PackedTranspose.tapeCount (src r.1)) := by
  have hnd : ((gatherHeaderCopies src).map Prod.snd).Nodup := by
    simp [gatherHeaderCopies,gatherHeaderAssignments,List.nodup_cons,headerReg_injective.eq_iff]
  have hh := copyWordHeadersR_get S.R (gatherHeaderCopies src) hnd S.R
    (Fin.castAdd PackedTranspose.tapeCount (src r.1),Fin.natAdd T (headerReg r.2)) (List.mem_map.mpr ⟨r,hr,rfl⟩)
  simpa only [loadedGatherHeaders,hblank _,List.append_nil] using hh

theorem loadGatherHeaders_exec_within
    (body : P → Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U) (src : Fin 7 → Fin T)
    (v : HS (T+PackedTranspose.tapeCount) Q (prime+K) U) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K))
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (depth : ℕ) :
    let cost := ((gatherHeaderCopies src).map (fun r => 6*(S.R r.1).length+6)).sum+1
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*cost) depth
        (loadGatherHeaders src) (mk v S) cost (mk v' (loadedGatherHeaders src S)) ∧
      (∀ r ∈ gatherHeaderAssignments, (loadedGatherHeaders src S).R (Fin.natAdd T (headerReg r.2)) =
        S.R (Fin.castAdd PackedTranspose.tapeCount (src r.1))) ∧
      (∀ k : Fin T, (loadedGatherHeaders src S).R (Fin.castAdd PackedTranspose.tapeCount k) = S.R (Fin.castAdd PackedTranspose.tapeCount k)) := by
  dsimp only
  have hni : Function.Injective (Fin.natAdd T : Fin PackedTranspose.tapeCount → Fin (T+PackedTranspose.tapeCount)) := by
    intro i j he
    apply Fin.ext
    have hv := congrArg (fun k : Fin (T+PackedTranspose.tapeCount) => k.val) he
    simp only [Fin.val_natAdd] at hv
    omega
  have hd := hni.comp headerReg_injective
  have hregs : ∀ r ∈ gatherHeaderCopies src,
      [r.1,r.2,Fin.natAdd T (headerReg 46),Fin.natAdd T (headerReg 47)].Nodup := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    have h46 : p.2 ≠ 46 := by
      simp only [gatherHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h47 : p.2 ≠ 47 := by
      simp only [gatherHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [List.nodup_cons,prefix_ne_routing,hd.eq_iff,headerReg_injective.eq_iff,h46,h47]
  have hsep : ∀ r ∈ gatherHeaderCopies src, ∀ p ∈ gatherHeaderCopies src, r.2 ≠ p.1 := by
    intro r hr p hp
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hp
    exact (prefix_ne_routing _ _).symm
  obtain ⟨v',hu,he⟩ := copyWordHeaders_exec (body := body) (Fin.natAdd T (headerReg 46))
    (Fin.natAdd T (headerReg 47)) (gatherHeaderCopies src) hregs hsep S.R v S (by intros; rfl)
    (hblank _) (hblank _)
  refine ⟨v',hu,mn_native_exec_within he 2 (copyWordHeaders_native _ _ _) depth _ (by omega),?_,?_⟩
  · exact loadedGatherHeaders_read src S hblank
  · intro k
    apply copyWordHeadersR_off
    intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact (prefix_ne_routing _ _).symm

/-- Actual word loading supplies every retained field of the allocated router. -/
theorem loadedGatherHeaders_ready (bank : ComputedClassBank → Fin T) (src : Fin 7 → Fin T)
    (V s a width radius L w : ℕ) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K))
    (hs : S.R (Fin.castAdd PackedTranspose.tapeCount (src 0)) = binSyms V s)
    (hw : S.R (Fin.castAdd PackedTranspose.tapeCount (src 1)) = binSyms V width)
    (hr : S.R (Fin.castAdd PackedTranspose.tapeCount (src 2)) = binSyms V radius)
    (hL : S.R (Fin.castAdd PackedTranspose.tapeCount (src 3)) = binSyms V L)
    (hV : (S.R (Fin.castAdd PackedTranspose.tapeCount (src 4))).length = V)
    (hword : (S.R (Fin.castAdd PackedTranspose.tapeCount (src 5))).length = w)
    (hrep : (S.R (Fin.castAdd PackedTranspose.tapeCount (src 6))).length = 2^a)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) (hleft : ∀ i, S.L (Fin.natAdd T i) = [])
    (hsourceLeft : S.L (control (extendedBank bank) .source) = []) :
    GeometryReady (gatherPlacement bank) V s a width radius L w (loadedGatherHeaders src S) := by
  have hread := loadedGatherHeaders_read src S hblank
  apply allocatedGeometryReady
  · rw [hread (0,32) (by simp [gatherHeaderAssignments])]; exact hs
  · rw [hread (1,33) (by simp [gatherHeaderAssignments])]; exact hw
  · rw [hread (2,34) (by simp [gatherHeaderAssignments])]; exact hr
  · rw [hread (3,35) (by simp [gatherHeaderAssignments])]; exact hL
  · rw [hread (4,37) (by simp [gatherHeaderAssignments])]; exact hV
  · rw [hread (4,115) (by simp [gatherHeaderAssignments])]; exact hV
  · rw [hread (5,87) (by simp [gatherHeaderAssignments])]; exact hword
  · change ((loadedGatherHeaders src S).R (Fin.natAdd T (headerReg 83))).length = _
    rw [hread (6,83) (by simp [gatherHeaderAssignments])]; exact hrep
  · intro i hi
    change copyWordHeadersR S.R (gatherHeaderCopies src) S.R (Fin.natAdd T i) = []
    rw [copyWordHeadersR_off S.R (gatherHeaderCopies src) S.R _ ?_]
    · exact hblank i
    · intro r hr
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      intro he
      have he' : headerReg p.2 = i := by
        apply Fin.ext
        have hv := congrArg (fun j : Fin (T+PackedTranspose.tapeCount) => j.val) he
        simp only [Fin.val_natAdd] at hv
        omega
      apply hi
      rw [←he']
      simp only [gatherHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [geometryLivePorts,show replicaCount = headerReg 83 from rfl]
  · exact hleft
  · exact hsourceLeft

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
