import IntegerMultBounds.Machine.PrefixCounter

/-! Physical lexicographic prefix addresses. The scheduler order is fastest
field first, the reverse of the array's most-significant-first field order.
Widths need not agree, and arbitrary spectator fields occur in the address. -/
namespace IntegerMultBounds.Machine.PrefixAddressData
open RadixDigits PrefixCounterData
variable {q c : ℕ}

theorem value_append (xs ys : List (Fin q)) :
    value (xs++ys) = value xs+q^xs.length*value ys := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih => simp only [List.cons_append,value,List.length_cons,pow_succ,ih]; ring

/-- A complete radix field is read from its exact mixed-width address interval. -/
theorem extract_word (hq : 2 ≤ q) (low field high : List (Fin q)) :
    (value (low++field++high)/q^low.length)%q^field.length = value field := by
  rw [List.append_assoc,value_append,value_append]
  have hp : 0 < q^low.length := pow_pos (by omega) _
  rw [Nat.add_mul_div_left _ _ hp,
    Nat.div_eq_of_lt (value_lt hq low),Nat.zero_add,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (value_lt hq field)]

def widthSum (order : List (Fin c)) (width : Fin c → ℕ) : ℕ := (order.map width).sum

/-- A complete fixed field order counts every spectator width exactly once. -/
theorem full_widthSum (order : List (Fin c)) (width : Fin c → ℕ)
    (hfull : order.Perm (List.finRange c)) : widthSum order width = ∑ i, width i := by
  unfold widthSum
  rw [(hfull.map width).sum_eq]
  simp only [← List.ofFn_id,List.map_ofFn,List.sum_ofFn,Function.comp_def,id_eq]

/-- The integer rank in the physical prefix stream. -/
def address (order : List (Fin c)) (ds : Fin c → List (Fin q)) : ℕ := value (flatten order ds)

theorem flatten_length (order : List (Fin c)) (ds : Fin c → List (Fin q)) :
    (flatten order ds).length = widthSum order (fun i => (ds i).length) := by
  simp [flatten,widthSum,List.length_flatMap]

/-- Array order with the first field most significant. -/
def lexAddress (order : List (Fin c)) (ds : Fin c → List (Fin q)) : ℕ :=
  match order with
  | [] => 0
  | i::is => value (ds i)*q^widthSum is (fun j => (ds j).length)+lexAddress is ds

/-- The counter's fastest-first order is exactly reverse physical lexicographic order. -/
theorem address_reverse (order : List (Fin c)) (ds : Fin c → List (Fin q)) :
    address order.reverse ds = lexAddress order ds := by
  induction order with
  | nil => rfl
  | cons i order ih =>
    have hl : (flatten order.reverse ds).length = widthSum order (fun j => (ds j).length) := by
      simp [flatten,widthSum,List.length_flatMap]
    rw [List.reverse_cons]
    change value (flatten (order.reverse++[i]) ds) = _
    simp only [flatten,List.flatMap_append,List.flatMap_singleton,value_append]
    change address order.reverse ds+q^(flatten order.reverse ds).length*value (ds i) = _
    rw [ih,hl]
    change lexAddress order ds+q^widthSum order (fun j => (ds j).length)*value (ds i) =
      value (ds i)*q^widthSum order (fun j => (ds j).length)+lexAddress order ds
    ring

theorem selected_field (hq : 2 ≤ q) (low high : List (Fin c)) (j : Fin c)
    (ds : Fin c → List (Fin q)) :
    (address (low++j::high) ds / q^widthSum low (fun i => (ds i).length)) %
      q^(ds j).length = value (ds j) := by
  have h := extract_word hq (flatten low ds) (ds j) (flatten high ds)
  rw [flatten_length] at h
  simpa only [address,flatten,List.flatMap_append,List.flatMap_cons,List.append_assoc] using h

theorem zero_address (hq : 2 ≤ q) (order : List (Fin c)) (width : Fin c → ℕ) :
    address order (fun i => RadixCounterData.zeros hq (width i)) = 0 := by
  induction order with
  | nil => rfl
  | cons i order ih =>
    change value (RadixCounterData.zeros hq (width i) ++ flatten order _) = 0
    rw [value_append,RadixCounterData.zeros_value]
    change 0+q^_ * address order _ = 0
    rw [ih]; simp

/-- Zero-start physical carry states have exactly their increasing stream rank. -/
theorem enumeration_address (hq : 2 ≤ q) (order : List (Fin c)) (hn : order.Nodup)
    (width : Fin c → ℕ) (n : ℕ) (hb : n < q^widthSum order width) :
    address order (iterateFields hq order n (fun i => RadixCounterData.zeros hq (width i))) = n := by
  rw [address,enumeration_value hq order hn]
  change (address order (fun i => RadixCounterData.zeros hq (width i))+n)%_ = n
  rw [zero_address,flatten_length]
  simp only [RadixCounterData.zeros_length,Nat.zero_add,Nat.mod_eq_of_lt hb]

/-- The actually enumerated selected control equals the radix slice of the
physical fiber number; all intervening spectator widths enter the divisor. -/
theorem enumeration_selected (hq : 2 ≤ q) (low high : List (Fin c)) (j : Fin c)
    (hn : (low++j::high).Nodup) (width : Fin c → ℕ) (n : ℕ)
    (hb : n < q^widthSum (low++j::high) width) :
    value (iterateFields hq (low++j::high) n (fun i => RadixCounterData.zeros hq (width i)) j) =
      (n/q^widthSum low width)%q^(width j) := by
  have h := selected_field hq low high j
    (iterateFields hq (low++j::high) n (fun i => RadixCounterData.zeros hq (width i)))
  rw [enumeration_address hq _ hn width n hb] at h
  simpa only [iterate_widths,RadixCounterData.zeros_length] using h.symm

end IntegerMultBounds.Machine.PrefixAddressData
