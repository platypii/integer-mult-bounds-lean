module

public import IntegerMultBounds.MathlibTM2.Routing.RectangularColumns
public import IntegerMultBounds.MathlibTM2.Routing.FixedWidthIndex
public import IntegerMultBounds.MathlibTM2.Routing.PeriodicHaloIndex

/-! Exact coordinate action of expose/halo/return on rectangular data. Only
the selected periodic coordinate changes; the complete spectator index is retained. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RectangularHaloCoordinates
open PaddedFieldLayout RectangularColumns
variable {β : Type}

def entry2 (fill : β) (rows : List (List β)) (i j : ℕ) : β :=
  ((((rows[i]?).getD [])[j]?).getD fill)

def entry3 (fill : β) (matrices : List (List (List β))) (k b t : ℕ) : β :=
  entry2 fill ((matrices[k]?).getD []) b t

theorem transpose_entry (fill : β) (M : ℕ) (rows : List (List β)) (i j : ℕ) (hi : i < M) :
    entry2 fill (realColumns M fill rows) i j = entry2 fill rows j i := by
  cases he : rows[j]? <;> simp [entry2,realColumns,hi,he]

def gather (L : ℕ) (fill : β) (matrices : List (List (List β))) : List (List β) :=
  matrices.flatMap (realColumns L fill)

theorem gather_length (L : ℕ) (fill : β) (matrices : List (List (List β))) :
    (gather L fill matrices).length = matrices.length*L :=
  HaloRecordLayout.length_flatMap (realColumns L fill) L matrices
    (by intro rows _; exact realColumns_length _ _ _)

theorem gather_entry (fill : β) (L : ℕ) (hL : 0 < L) (matrices : List (List (List β))) (i b : ℕ) :
    entry2 fill (gather L fill matrices) i b = entry3 fill matrices (i/L) b (i%L) := by
  change ((((matrices.flatMap (realColumns L fill))[i]?).getD [])[b]?).getD fill =
    entry2 fill ((matrices[i/L]?).getD []) b (i%L)
  rw [FixedWidthIndex.getElem?_flatMap (realColumns L fill) L hL matrices
    (by intro rows _; exact realColumns_length _ _ _)]
  cases he : matrices[i/L]? with
  | none => simp [entry2]
  | some rows =>
    simp only [Option.bind_some,Option.getD_some]
    exact transpose_entry fill L rows (i%L) b (Nat.mod_lt i hL)

def haloRows (B L H N : ℕ) (fill : β) (matrices : List (List (List β))) : List (List (List β)) :=
  (HaloRecordLayout.windows L H N (gather L fill matrices)).map (realColumns B fill)

def sourceIndex (N L H k t : ℕ) : ℕ := (N*L+(k*L+t)-H)%(N*L)

theorem halo_entry (fill : β) (N B L H : ℕ) (matrices : List (List (List β)))
    (hN : matrices.length = N) (hL : 0 < L) (hH : H ≤ N*L)
    (k b t : ℕ) (hk : k < N) (hb : b < B) (ht : t < L+2*H) :
    entry3 fill (haloRows B L H N fill matrices) k b t =
      entry3 fill matrices (sourceIndex N L H k t/L) b (sourceIndex N L H k t%L) := by
  have hlen : (gather L fill matrices).length = N*L := by
    simpa only [hN] using gather_length L fill matrices
  have hkw : k < (HaloRecordLayout.windows L H N (gather L fill matrices)).length := by
    simpa only [HaloRecordLayout.windows_length] using hk
  have hperiod := PeriodicHaloIndex.window_getElem? (gather L fill matrices) L H N k t hlen
    (by rw [hlen]; exact hH) hk ht
  rw [List.getElem?_eq_getElem hkw] at hperiod
  simp only [Option.getD_some,hlen] at hperiod
  unfold entry3 haloRows
  rw [List.getElem?_map,List.getElem?_eq_getElem hkw]
  simp only [Option.map_some,Option.getD_some]
  rw [transpose_entry fill B _ b t hb]
  unfold entry2
  rw [hperiod]
  exact gather_entry fill L hL matrices (sourceIndex N L H k t) b

theorem halo_shape (fill : β) (N B L H : ℕ) (matrices : List (List (List β)))
    (hN : matrices.length = N) (hH : H ≤ N*L) :
    (haloRows B L H N fill matrices).length = N ∧
      ∀ rows ∈ haloRows B L H N fill matrices, rows.length = B ∧
        ∀ row ∈ rows, row.length = L+2*H := by
  refine ⟨by simp [haloRows,HaloRecordLayout.windows_length],?_⟩
  intro rows hr
  obtain ⟨window,hw,rfl⟩ := List.mem_map.mp hr
  refine ⟨realColumns_length _ _ _,?_⟩
  intro row hrow
  have hlen : (gather L fill matrices).length = N*L := by simpa only [hN] using gather_length L fill matrices
  exact (realColumns_row_length B fill window row hrow).trans
    (HaloRecordLayout.windows_row_length L H N (gather L fill matrices) hlen (by rw [hlen]; exact hH) window hw)

def entry4 (fill : β) (fibers : List (List (List (List β)))) (a k b t : ℕ) : β :=
  entry3 fill ((fibers[a]?).getD []) k b t

theorem prefix_halo_entry (fill : β) (N B L H : ℕ) (fibers : List (List (List (List β))))
    (hN : ∀ matrices ∈ fibers, matrices.length = N) (hL : 0 < L) (hH : H ≤ N*L)
    (a k b t : ℕ) (ha : a < fibers.length) (hk : k < N) (hb : b < B) (ht : t < L+2*H) :
    entry4 fill (fibers.map (haloRows B L H N fill)) a k b t =
      entry4 fill fibers a (sourceIndex N L H k t/L) b (sourceIndex N L H k t%L) := by
  simp only [entry4,List.getElem?_map,List.getElem?_eq_getElem ha,Option.map_some,Option.getD_some]
  exact halo_entry fill N B L H fibers[a] (hN _ (List.getElem_mem ha)) hL hH k b t hk hb ht

end IntegerMultBounds.MathlibTM2.Routing.RectangularHaloCoordinates
