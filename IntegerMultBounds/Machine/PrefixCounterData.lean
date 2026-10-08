import IntegerMultBounds.Machine.RadixCounterData

/-! Mixed-prefix carry semantics. Field zero is least significant; widths may
be arbitrary and unequal, including zero. Carries visit only overflowing fields.
The total potential is the sum of maximal-digit potentials of those fields. -/
namespace IntegerMultBounds.Machine.PrefixCounterData

open RadixDigits RadixCounterData
variable {q c : ℕ}

def overflow : List (Fin q) → Bool
  | [] => true
  | x::xs => if x.val+1 < q then false else overflow xs

theorem increment_append (hq : 2 ≤ q) (xs ys : List (Fin q)) :
    increment hq (xs++ys) = increment hq xs ++ (if overflow xs then increment hq ys else ys) := by
  induction xs with
  | nil => simp [increment,overflow]
  | cons x xs ih =>
    by_cases hx : x.val+1 < q <;> simp [increment,overflow,hx,ih]

/-- Field order is fixed by the finite control, not supplied as an input list. -/
def advanceFields (hq : 2 ≤ q) : List (Fin c) → (Fin c → List (Fin q)) → (Fin c → List (Fin q))
  | [],ds => ds
  | i::is,ds =>
    let next := Function.update ds i (increment hq (ds i))
    if overflow (ds i) then advanceFields hq is next else next

def stepCost (hq : 2 ≤ q) : List (Fin c) → (Fin c → List (Fin q)) → ℕ
  | [],_ => 0
  | i::is,ds => 2*carrySteps (ds i)+
    if overflow (ds i) then stepCost hq is (Function.update ds i (increment hq (ds i))) else 0

theorem outside (hq : 2 ≤ q) (is : List (Fin c)) (ds : Fin c → List (Fin q)) (j : Fin c)
    (hj : j ∉ is) : advanceFields hq is ds j = ds j := by
  induction is generalizing ds with
  | nil => rfl
  | cons i is ih =>
    have hji : j ≠ i := by simp only [List.mem_cons,not_or] at hj; exact hj.1
    have ht : j ∉ is := by simp only [List.mem_cons,not_or] at hj; exact hj.2
    simp only [advanceFields]
    split_ifs
    · rw [ih _ ht,Function.update_of_ne hji]
    · exact Function.update_of_ne hji _ _

theorem widths_preserved (hq : 2 ≤ q) (is : List (Fin c)) (ds : Fin c → List (Fin q)) (j : Fin c) :
    (advanceFields hq is ds j).length = (ds j).length := by
  induction is generalizing ds with
  | nil => rfl
  | cons i is ih =>
    simp only [advanceFields]
    split_ifs
    · rw [ih]
      by_cases hj : j = i <;> simp [hj]
    · by_cases hj : j = i <;> simp [hj]

def flatten (is : List (Fin c)) (ds : Fin c → List (Fin q)) : List (Fin q) := is.flatMap ds

private theorem flatten_update (is : List (Fin c)) (ds : Fin c → List (Fin q)) (j : Fin c)
    (xs : List (Fin q)) (hj : j ∉ is) : flatten is (Function.update ds j xs) = flatten is ds := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have hji : i ≠ j := by intro h; subst i; exact hj (by simp)
    have ht : j ∉ is := by intro h; exact hj (by simp [h])
    change (Function.update ds j xs) i ++ flatten is (Function.update ds j xs) = ds i ++ flatten is ds
    rw [Function.update_of_ne hji,ih ht]

/-- Exact lexicographic increment equals one ripple across the concatenation
of all field words, while preserving each field's own fixed width. -/
theorem flatten_advance (hq : 2 ≤ q) (is : List (Fin c)) (hn : is.Nodup)
    (ds : Fin c → List (Fin q)) :
    flatten is (advanceFields hq is ds) = increment hq (flatten is ds) := by
  induction is generalizing ds with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨hi,ht⟩ := List.nodup_cons.mp hn
    simp only [advanceFields]
    by_cases ho : overflow (ds i) = true
    · simp only [ho,ite_true]
      change advanceFields hq is (Function.update ds i (increment hq (ds i))) i ++
        flatten is (advanceFields hq is (Function.update ds i (increment hq (ds i)))) = _
      rw [outside hq is _ i hi,Function.update_self,ih ht,flatten_update is ds i _ hi]
      simpa only [flatten,List.flatMap_cons,ho,ite_true] using
        (increment_append hq (ds i) (flatten is ds)).symm
    · simp only [ho]
      change (Function.update ds i (increment hq (ds i))) i ++
        flatten is (Function.update ds i (increment hq (ds i))) = _
      rw [Function.update_self,flatten_update is ds i _ hi]
      symm
      simpa only [flatten,List.flatMap_cons,ho,Bool.false_eq_true,ite_false] using increment_append hq (ds i) (flatten is ds)

def potential (ds : Fin c → List (Fin q)) : ℕ := ∑ j, maxWeight (ds j)

theorem potential_update (ds : Fin c → List (Fin q)) (i : Fin c) (xs : List (Fin q)) :
    potential (Function.update ds i xs)+maxWeight (ds i) = potential ds+maxWeight xs := by
  simp only [potential]
  have he : (fun j => maxWeight (Function.update ds i xs j)) =
      Function.update (fun j => maxWeight (ds j)) i (maxWeight xs) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [he,Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

/-- Carry work telescopes across fields, even when spectator widths are huge. -/
theorem step_potential (hq : 2 ≤ q) (is : List (Fin c)) (ds : Fin c → List (Fin q)) :
    stepCost hq is ds+2*potential (advanceFields hq is ds) ≤ 4*is.length+2*potential ds := by
  induction is generalizing ds with
  | nil => simp [stepCost,advanceFields]
  | cons i is ih =>
    have hc := increment_potential hq (ds i)
    have hu := potential_update ds i (increment hq (ds i))
    have hr := ih (Function.update ds i (increment hq (ds i)))
    simp only [stepCost,advanceFields,List.length_cons]
    split_ifs <;> omega

def iterateFields (hq : 2 ≤ q) (is : List (Fin c)) : ℕ → (Fin c → List (Fin q)) → (Fin c → List (Fin q))
  | 0,ds => ds
  | n+1,ds => iterateFields hq is n (advanceFields hq is ds)

def cycleTime (hq : 2 ≤ q) (is : List (Fin c)) : ℕ → (Fin c → List (Fin q)) → ℕ
  | 0,_ => 0
  | n+1,ds => stepCost hq is ds+2+cycleTime hq is n (advanceFields hq is ds)

theorem cycle_potential (hq : 2 ≤ q) (is : List (Fin c)) (n : ℕ) (ds : Fin c → List (Fin q)) :
    cycleTime hq is n ds+2*potential (iterateFields hq is n ds) ≤ (4*is.length+2)*n+2*potential ds := by
  induction n generalizing ds with
  | zero => simp [cycleTime,iterateFields]
  | succ n ih =>
    have hs := step_potential hq is ds
    have hr := ih (advanceFields hq is ds)
    simp only [cycleTime,iterateFields]
    nlinarith

theorem cycle_amortized (hq : 2 ≤ q) (is : List (Fin c)) (n : ℕ) (ds : Fin c → List (Fin q)) :
    cycleTime hq is n ds ≤ (4*is.length+2)*n+2*∑ j, (ds j).length := by
  have hp := cycle_potential hq is n ds
  have hw : potential ds ≤ ∑ j, (ds j).length :=
    Finset.sum_le_sum (fun j _ => maxWeight_le_length (ds j))
  omega

/-- The whole fixed-width field family enumerates one concatenated radix
word, with the first scheduled field varying fastest. -/
theorem flatten_iterate (hq : 2 ≤ q) (is : List (Fin c)) (hn : is.Nodup)
    (n : ℕ) (ds : Fin c → List (Fin q)) :
    flatten is (iterateFields hq is n ds) = RadixCounterData.advance hq n (flatten is ds) := by
  induction n generalizing ds with
  | zero => rfl
  | succ n ih =>
    rw [iterateFields,ih,flatten_advance hq is hn]
    rfl

theorem enumeration_value (hq : 2 ≤ q) (is : List (Fin c)) (hn : is.Nodup)
    (n : ℕ) (ds : Fin c → List (Fin q)) :
    value (flatten is (iterateFields hq is n ds)) =
      (value (flatten is ds)+n)%q^(flatten is ds).length := by
  rw [flatten_iterate hq is hn,RadixCounterData.advance_value]

theorem iterate_widths (hq : 2 ≤ q) (is : List (Fin c)) (n : ℕ)
    (ds : Fin c → List (Fin q)) (j : Fin c) :
    (iterateFields hq is n ds j).length = (ds j).length := by
  induction n generalizing ds with
  | zero => rfl
  | succ n ih => rw [iterateFields,ih,widths_preserved]

theorem flatten_length (ds : Fin c → List (Fin q)) :
    (flatten (List.finRange c) ds).length = ∑ i, (ds i).length := by
  simp only [flatten,List.length_flatMap,← List.ofFn_id,List.map_ofFn,List.sum_ofFn,Function.comp_def,id_eq]

private theorem word_injective (hq : 2 ≤ q) (xs ys : List (Fin q))
    (hl : xs.length = ys.length) (hv : value xs = value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hl.symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hm := congrArg (fun n => n%q) hv
      simp only [value,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt x.isLt,Nat.mod_eq_of_lt y.isLt] at hm
      have he : x = y := Fin.ext hm
      subst y
      have ht : value xs = value ys := by simp only [value] at hv; nlinarith
      rw [ih ys (by simpa using hl) ht]

private theorem flatten_injective (is : List (Fin c)) (ds es : Fin c → List (Fin q))
    (hw : ∀ j ∈ is, (ds j).length = (es j).length) (he : flatten is ds = flatten is es) :
    ∀ j ∈ is, ds j = es j := by
  induction is with
  | nil => simp
  | cons i is ih =>
    obtain ⟨hi,ht⟩ := List.append_inj he (hw i (by simp))
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact ih (fun k hk => hw k (by simp [hk])) ht j hj

/-- A complete mixed-prefix period restores every field, including arbitrary
initial spectator contents, without an explicit width-dependent reset scan. -/
theorem full_cycle (hq : 2 ≤ q) (ds : Fin c → List (Fin q)) :
    iterateFields hq (List.finRange c) (q^(∑ i, (ds i).length)) ds = ds := by
  let is := List.finRange c
  let n := q^(∑ i, (ds i).length)
  have he : flatten is (iterateFields hq is n ds) = flatten is ds := by
    apply word_injective hq
    · rw [flatten_iterate hq is (List.nodup_finRange c),RadixCounterData.advance_length]
    · rw [enumeration_value hq is (List.nodup_finRange c)]
      change (value (flatten is ds)+q^(∑ i, (ds i).length))%q^(flatten is ds).length = _
      rw [← flatten_length ds,Nat.add_mod_right,Nat.mod_eq_of_lt (value_lt hq _)]
  funext j
  exact flatten_injective is _ ds (fun i _ => iterate_widths hq is n ds i) he j (List.mem_finRange j)

theorem full_cycle_cost (hq : 2 ≤ q) (ds : Fin c → List (Fin q)) :
    cycleTime hq (List.finRange c) (q^(∑ i, (ds i).length)) ds ≤
      (4*c+4)*q^(∑ i, (ds i).length) := by
  let w := ∑ i, (ds i).length
  have hw : w ≤ q^w := by
    induction w with
    | zero => simp
    | succ w ih =>
      rw [pow_succ]
      have := Nat.one_le_pow w q (by omega)
      nlinarith
  have h := cycle_amortized hq (List.finRange c) (q^w) ds
  rw [List.length_finRange] at h
  change cycleTime hq (List.finRange c) (q^w) ds ≤ (4*c+2)*q^w+2*w at h
  change cycleTime hq (List.finRange c) (q^w) ds ≤ (4*c+4)*q^w
  nlinarith

end IntegerMultBounds.Machine.PrefixCounterData
