module

public import IntegerMultBounds.MathlibTM2.Routing.FixedWidthSlice

/-! Persistent halo windows act on complete records, including an arbitrary
spectator suffix. Encoding commutes with periodic extension and aligned slicing. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloRecordLayout
open HaloIntervalLayout
variable {α β : Type}

def extended (H : ℕ) (xs : List β) : List β := xs.drop (xs.length-H)++xs++xs.take H

theorem mem_extended {H : ℕ} {xs : List β} {x : β} (hx : x ∈ extended H xs) : x ∈ xs := by
  simp only [extended,List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact List.mem_of_mem_drop hx
  · exact hx
  · exact List.mem_of_mem_take hx

theorem length_flatMap (encode : β → List α) (R : ℕ) (xs : List β)
    (hencode : ∀ x ∈ xs, (encode x).length = R) : (xs.flatMap encode).length = xs.length*R := by
  rw [List.length_flatMap]
  have hm : xs.map (fun x => (encode x).length) = xs.map (fun _ => R) := List.map_congr_left hencode
  rw [hm]
  simp

theorem extended_flatMap (encode : β → List α) (R : ℕ) (xs : List β)
    (hencode : ∀ x ∈ xs, (encode x).length = R) (H : ℕ) :
    extended (H*R) (xs.flatMap encode) = (extended H xs).flatMap encode := by
  simp only [extended,List.flatMap_append]
  rw [length_flatMap encode R xs hencode,←Nat.sub_mul,
    FixedWidthSlice.drop_flatMap encode R xs hencode,FixedWidthSlice.take_flatMap encode R xs hencode]

def windows (L H N : ℕ) (xs : List β) : List (List β) :=
  (List.range' 0 N).map fun j => slice (extended H xs) (j*L) ((j+1)*L+2*H)

theorem windows_length (L H N : ℕ) (xs : List β) : (windows L H N xs).length = N := by
  simp [windows]

theorem windows_row_length (L H N : ℕ) (xs : List β) (hlen : xs.length = N*L) (hH : H ≤ xs.length) :
    ∀ row ∈ windows L H N xs, row.length = L+2*H := by
  intro row hr
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
  have hjN : j < N := by simpa using hj
  have hext : (extended H xs).length = N*L+2*H := by
    simp only [extended,List.length_append,List.length_drop,List.length_take,Nat.min_eq_left hH]
    omega
  have hb : (j+1)*L+2*H ≤ (extended H xs).length := by
    rw [hext]
    have hh := Nat.mul_le_mul_right L (show j+1 ≤ N by omega)
    omega
  rw [slice_length _ (by nlinarith) hb]
  simp only [Nat.add_mul,Nat.one_mul]
  omega

theorem mem_windows {L H N : ℕ} {xs : List β} {row : List β} {x : β}
    (hr : row ∈ windows L H N xs) (hx : x ∈ row) : x ∈ xs := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hr
  exact mem_extended (List.mem_of_mem_drop (List.mem_of_mem_take hx))

theorem emitted_flatMap (encode : β → List α) (R : ℕ) (xs : List β)
    (hencode : ∀ x ∈ xs, (encode x).length = R) (L H N : ℕ) :
    (List.range' 0 N).flatMap (fun j => slice (extended (H*R) (xs.flatMap encode))
      (j*(L*R)) ((j+1)*(L*R)+2*(H*R))) =
      (windows L H N xs).flatMap (fun row => row.flatMap encode) := by
  rw [extended_flatMap encode R xs hencode]
  simp only [windows,List.flatMap_map]
  apply List.flatMap_congr
  intro j _
  have ha : j*(L*R) = (j*L)*R := by simp only [Nat.mul_assoc]
  have hb : (j+1)*(L*R)+2*(H*R) = ((j+1)*L+2*H)*R := by
    simp only [Nat.add_mul,Nat.mul_assoc]
  rw [ha,hb,FixedWidthSlice.slice_flatMap encode R (extended H xs)
    (fun x hx => hencode x (mem_extended hx))]

end IntegerMultBounds.MathlibTM2.Routing.HaloRecordLayout
