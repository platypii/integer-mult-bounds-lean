module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationFromEncoded
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaGatherData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCoreRead

/-! Exact packed-word reads after replica publication. Uniform list slicing
separates replica placement from the one-window scatter law. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {A span L : ℕ}

theorem flatMap_uniform_slice {α β : Type*} (f : β → List α) (xs : List β)
    (V p width : ℕ) (hlen : ∀ x ∈ xs, (f x).length = V)
    (r : Fin xs.length) (hfit : p+width ≤ V) (tail : List α) :
    (((xs.flatMap f)++tail).drop (r.val*V+p)).take width =
      ((f (xs[r.val]'r.isLt)).drop p).take width := by
  have hm : ∀ row ∈ xs.map f, row.length = V := by
    intro row hr
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact hlen x hx
  have htotal : (xs.flatMap f).length = xs.length*V := by
    rw [List.length_flatMap]
    rw [show xs.map (fun x => (f x).length) = xs.map (fun _ => V) from List.map_congr_left hlen]
    simp
  have hbound : r.val*V+p+width ≤ (xs.flatMap f).length := by
    rw [htotal]
    have hh := Nat.mul_le_mul_right V (Nat.succ_le_of_lt r.isLt)
    rw [Nat.succ_mul] at hh
    omega
  rw [List.drop_append_of_le_length (by omega),List.take_append_of_le_length (by
    simp only [List.length_drop]; omega)]
  have hh := flatten_uniform_window (xs.map f) V p width r.val hm (by simpa only [List.length_map] using r.isLt) hfit
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using r.isLt)] at hh
  simpa only [List.flatMap_def,List.getElem_map] using hh

theorem PublicationReplica.Valid.input_eq_words {w : ℕ} {r : PublicationReplica A}
    {windows : PublicationWindows span L} (h : r.Valid windows w 0) : r.input w = r.words w := by
  have hh := h.realRows
  simp only [Nat.zero_mul,List.drop_zero] at hh
  exact congrArg (cstream A w) hh

/-- Replica publication preserves the precise compact solver word, including
its position within a replica and its source's borrowed suffix. -/
theorem publicationReplicas_word (windows : PublicationWindows span L) (w : ℕ)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (tail : List (Fin (A+4))) (r : Fin replicas.length)
    (n : Fin windows.origins.length) (i : Fin L) :
    ((replicas.flatMap (PublicationReplica.output windows w)).drop
      ((r.val*span+(windows.origins[n.val]'n.isLt)+i.val)*w)).take w =
      (((replicas.flatMap (PublicationReplica.input w))++tail).drop
        (((r.val*windows.origins.length+n.val)*L+i.val)*w)).take w := by
  have hrow := hvalid _ (List.getElem_mem r.isLt)
  have hfit := windows.fits _ (List.getElem_mem n.isLt)
  have houtFit : ((windows.origins[n.val]'n.isLt)+i.val)*w+w ≤ span*w := by
    have hh := Nat.mul_le_mul_right w (show (windows.origins[n.val]'n.isLt)+i.val+1 ≤ span by omega)
    simpa only [Nat.add_mul,Nat.one_mul] using hh
  have hinFit : (n.val*L+i.val)*w+w ≤ (windows.origins.length*(L*w)) := by
    have hh := Nat.mul_le_mul_right L (Nat.succ_le_of_lt n.isLt)
    rw [Nat.succ_mul] at hh
    have hh' := Nat.mul_le_mul_right w (show n.val*L+i.val+1 ≤ windows.origins.length*L by omega)
    simpa only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc] using hh'
  have hout := flatMap_uniform_slice (PublicationReplica.output windows w) replicas (span*w)
    (((windows.origins[n.val]'n.isLt)+i.val)*w) w
    (fun x hx => (hvalid x hx).output_length) r houtFit []
  have hin := flatMap_uniform_slice (PublicationReplica.input w) replicas (windows.origins.length*(L*w))
    ((n.val*L+i.val)*w) w (by
      intro x hx
      rw [(hvalid x hx).input_eq_words]
      exact (hvalid x hx).words_length) r hinFit tail
  rw [hrow.output_word n i] at hout
  rw [hrow.input_eq_words] at hin
  calc
    _ = (((replicas[r.val]'r.isLt).words w).drop ((n.val*L+i.val)*w)).take w := by
      simpa only [List.append_nil,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using hout
    _ = _ := by
      convert hin.symm using 2; congr 1; ring

/-- Packed placement preserves the solver's ambient-coordinate error on every
cell, with the same error and no replica/window count factor. -/
theorem publicationReplicas_errorOn {s : ℕ} [NeZero s]
    (windows : PublicationWindows span L) (q w origin : ℕ) (hspan : origin+span ≤ s)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (tail : List (Fin (A+4))) (x : ℕ → ZMod s → ℝ) (error : ℝ)
    (herror : ∀ r : Fin replicas.length, ∀ n : Fin windows.origins.length,
      PhaseCellInterface.ErrorOn
        (publishedCellCore ((origin+(windows.origins[n.val]'n.isLt) : ℕ) : ZMod s) L)
        (publishedBatchRead q w (r.val*windows.origins.length+n.val) L
          ((origin+(windows.origins[n.val]'n.isLt) : ℕ) : ZMod s)
          (replicas.flatMap (PublicationReplica.input w)++tail)) (x r.val) error)
    (r : Fin replicas.length) (n : Fin windows.origins.length) :
    PhaseCellInterface.ErrorOn
      (publishedCellCore ((origin+(windows.origins[n.val]'n.isLt) : ℕ) : ZMod s) L)
      (fun k => (packedIntervalRead q w origin
        ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)) k).re)
      (x r.val) error := by
  intro k hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  have hiL : i < L := Finset.mem_range.mp hi
  let p := windows.origins[n.val]'n.isLt
  let lo : ZMod s := ((origin+p : ℕ) : ZMod s)
  have hfit := windows.fits p (List.getElem_mem n.isLt)
  have hlo : origin+p < s := by omega
  have hloVal : lo.val = origin+p := by simp only [lo,ZMod.val_natCast,Nat.mod_eq_of_lt hlo]
  have hloFit : lo.val+L ≤ s := by rw [hloVal]; omega
  have hsum : origin+p+i < s := by omega
  have hcoord : (lo+(i : ZMod s)).val-origin = p+i := by
    have hh : lo+(i : ZMod s) = ((origin+p+i : ℕ) : ZMod s) := by simp [lo,Nat.cast_add]
    rw [hh,ZMod.val_natCast,Nat.mod_eq_of_lt hsum]
    omega
  have hread : (packedIntervalRead q w origin
      ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w))
        (lo+(i : ZMod s))).re =
      publishedBatchRead q w (r.val*windows.origins.length+n.val) L lo
        (replicas.flatMap (PublicationReplica.input w)++tail) (lo+(i : ZMod s)) := by
    dsimp only [packedIntervalRead,publishedBatchRead,publishedCellRead]
    rw [publishedCell_offset lo hloFit hiL,hcoord]
    simp only [List.drop_drop]
    rw [show r.val*span*w+(p+i)*w = (r.val*span+p+i)*w by ring]
    rw [publicationReplicas_word windows w replicas hvalid tail r n ⟨i,hiL⟩]
    rw [show (r.val*windows.origins.length+n.val)*L*w+i*w =
      ((r.val*windows.origins.length+n.val)*L+i)*w by ring]
  change ‖(packedIntervalRead q w origin
    ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w))
      (lo+(i : ZMod s))).re-x r.val (lo+(i : ZMod s))‖ ≤ error
  rw [hread]
  exact herror r n _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
