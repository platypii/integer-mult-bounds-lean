module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationRead

/-! An independent publication bank retains every word belonging to another
disjoint class. Class traversal therefore preserves earlier accuracy exactly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {A span L : ℕ}

theorem PublicationWindows.scatter_off_word {α : Type*} (windows : PublicationWindows span L)
    (w j : ℕ) (E X : List α) (hE : span*w ≤ E.length)
    (hX : windows.origins.length*(L*w) ≤ X.length)
    (hoff : ∀ n : Fin windows.origins.length,
      j+1 ≤ windows.origins[n.val]'n.isLt ∨ (windows.origins[n.val]'n.isLt)+L ≤ j) :
    ((scatterRows (L*w) E X (windows.gaps w)).drop (j*w)).take w = (E.drop (j*w)).take w := by
  apply scatterRows_slice_off (L*w) (windows.symbolOrigins w) E X (windows.symbolOrigins_disjoint w)
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    have hh := Nat.mul_le_mul_right w (windows.fits a ha)
    exact (by simpa only [Nat.add_mul] using hh : a*w+L*w ≤ span*w).trans hE
  · simpa only [PublicationWindows.symbolOrigins,List.length_map] using hX
  · intro n hn
    have hn' : n < windows.origins.length := by simpa only [PublicationWindows.symbolOrigins,List.length_map] using hn
    simp only [PublicationWindows.symbolOrigins,List.getElem_map]
    rcases hoff ⟨n,hn'⟩ with h | h
    · left
      simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right w h
    · right
      simpa only [Nat.add_mul] using Nat.mul_le_mul_right w h

/-- Exact word preservation in the complete packed replica bank. -/
theorem publicationReplicas_preserves_word (windows : PublicationWindows span L) (w j : ℕ)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (tail : List (Fin (A+4))) (r : Fin replicas.length) (hj : j+1 ≤ span)
    (hoff : ∀ n : Fin windows.origins.length,
      j+1 ≤ windows.origins[n.val]'n.isLt ∨ (windows.origins[n.val]'n.isLt)+L ≤ j) :
    (((replicas.flatMap (PublicationReplica.output windows w))++tail).drop ((r.val*span+j)*w)).take w =
      (((replicas.flatMap PublicationReplica.ambient)++tail).drop ((r.val*span+j)*w)).take w := by
  have hfit : j*w+w ≤ span*w := by simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right w hj
  have hout := flatMap_uniform_slice (PublicationReplica.output windows w) replicas (span*w) (j*w) w
    (fun z hz => (hvalid z hz).output_length) r hfit tail
  have hin := flatMap_uniform_slice PublicationReplica.ambient replicas (span*w) (j*w) w
    (fun z hz => (hvalid z hz).ambientLength) r hfit tail
  have hr := hvalid _ (List.getElem_mem r.isLt)
  have hword := windows.scatter_off_word w j (replicas[r.val]'r.isLt).ambient
    ((replicas[r.val]'r.isLt).words w) (by rw [hr.ambientLength]) (by rw [hr.words_length]) hoff
  calc
    _ = ((((replicas[r.val]'r.isLt).output windows w).drop (j*w)).take w) := by
      simpa only [Nat.add_mul,Nat.mul_assoc] using hout
    _ = (((replicas[r.val]'r.isLt).ambient.drop (j*w)).take w) := hword
    _ = _ := by simpa only [Nat.add_mul,Nat.mul_assoc] using hin.symm

/-- Earlier disjoint classes retain their full physical-read error bound. -/
theorem publicationReplicas_preserves_errorOn {s origin : ℕ} [NeZero s]
    (windows : PublicationWindows span L) (q w : ℕ)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (tail : List (Fin (A+4))) (r : Fin replicas.length)
    (core : Finset (ZMod s)) (x : ZMod s → ℝ) (error : ℝ)
    (hcore : ∀ k ∈ core, origin ≤ k.val ∧ k.val < origin+span)
    (hoff : ∀ k ∈ core, ∀ n : Fin windows.origins.length,
      k.val-origin+1 ≤ windows.origins[n.val]'n.isLt ∨
        (windows.origins[n.val]'n.isLt)+L ≤ k.val-origin)
    (herror : PhaseCellInterface.ErrorOn core
      (fun k => (packedIntervalRead q w origin
        (((replicas.flatMap PublicationReplica.ambient)++tail).drop (r.val*span*w)) k).re) x error) :
    PhaseCellInterface.ErrorOn core
      (fun k => (packedIntervalRead q w origin
        (((replicas.flatMap (PublicationReplica.output windows w))++tail).drop (r.val*span*w)) k).re) x error := by
  intro k hk
  have hcoord := hcore k hk
  have hword := publicationReplicas_preserves_word windows w (k.val-origin) replicas hvalid tail r
    (by omega) (hoff k hk)
  have hread : packedIntervalRead q w origin
      (((replicas.flatMap (PublicationReplica.output windows w))++tail).drop (r.val*span*w)) k =
      packedIntervalRead q w origin
        (((replicas.flatMap PublicationReplica.ambient)++tail).drop (r.val*span*w)) k := by
    dsimp only [packedIntervalRead]
    simp only [List.drop_drop]
    rw [show r.val*span*w+(k.val-origin)*w = (r.val*span+(k.val-origin))*w by ring,hword]
  have hh := herror k hk
  dsimp only at hh ⊢
  rw [hread]
  exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
