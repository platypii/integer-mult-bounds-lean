module

public import IntegerMultBounds.MathlibTM2.Routing.HaloRecordLayout

/-! Periodic coordinate meaning of the bounded head/tail extension and its
regular windows. The physical source cut is retained through a modular index. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.PeriodicHaloIndex
open HaloIntervalLayout HaloRecordLayout
variable {β : Type}

theorem extended_getElem? (xs : List β) (H j : ℕ) (hH : H ≤ xs.length)
    (hj : j < xs.length+2*H) :
    (extended H xs)[j]? = xs[(xs.length+j-H)%xs.length]? := by
  have htail : (xs.drop (xs.length-H)).length = H := by simp; omega
  by_cases hfirst : j < H
  · rw [extended,List.append_assoc,List.getElem?_append_left (by rw [htail]; exact hfirst),List.getElem?_drop]
    have he : xs.length+j-H = xs.length-H+j := by omega
    rw [he,Nat.mod_eq_of_lt (by omega)]
  · rw [extended,List.append_assoc,List.getElem?_append_right (by rw [htail]; omega),htail]
    by_cases hmiddle : j-H < xs.length
    · rw [List.getElem?_append_left hmiddle]
      have he : xs.length+j-H = xs.length+(j-H) := by omega
      rw [he]
      simp [Nat.mod_eq_of_lt hmiddle]
    · rw [List.getElem?_append_right (by omega),List.getElem?_take_of_lt (by omega)]
      have he : xs.length+j-H = xs.length+xs.length+(j-H-xs.length) := by omega
      have hlast : j-H-xs.length < xs.length := by omega
      rw [he]
      simp [Nat.add_mod,Nat.mod_eq_of_lt hlast]

theorem window_getElem? (xs : List β) (L H N k t : ℕ) (hlen : xs.length = N*L)
    (hH : H ≤ xs.length) (hk : k < N) (ht : t < L+2*H) :
    (((windows L H N xs)[k]?).getD [])[t]? = xs[(xs.length+(k*L+t)-H)%xs.length]? := by
  have hwindow : (windows L H N xs)[k]? = some (slice (extended H xs) (k*L) ((k+1)*L+2*H)) := by
    simp only [HaloRecordLayout.windows,List.getElem?_map,List.getElem?_range' hk,Nat.one_mul,Nat.zero_add,Option.map_some]
  rw [hwindow]
  simp only [Option.getD_some,slice]
  have hwidth : (k+1)*L+2*H-k*L = L+2*H := by simp only [Nat.add_mul,Nat.one_mul]; omega
  rw [List.getElem?_take_of_lt (by rw [hwidth]; exact ht),List.getElem?_drop]
  apply extended_getElem? xs H (k*L+t) hH
  have hh := Nat.mul_le_mul_right L (show k+1 ≤ N by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hh
  omega

end IntegerMultBounds.MathlibTM2.Routing.PeriodicHaloIndex
