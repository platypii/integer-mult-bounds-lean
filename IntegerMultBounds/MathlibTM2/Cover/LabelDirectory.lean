module

public import IntegerMultBounds.MathlibTM2.Cover.LabelSplit
public import IntegerMultBounds.Machine.PrefixAddressData
public import IntegerMultBounds.Machine.RadixCounterData

/-! Full label addresses in the directories of the two child streams. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectory
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RadixCounterData RadixDigits Host Node

/-- The current label counts cyclically, once through the box for each spectator prefix. -/
def digits (m w j : ℕ) : List (Fin prime) :=
  advance prime_prime.two_le j (zeros prime_prime.two_le (w*(m*m)))

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos w).ne'⟩

theorem value_at (m w p : ℕ) (g : LabelPadding.Label m w) :
    value (digits m w (p*(prime^w)^(m*m)+(LabelAddress.address g).val)) =
      (LabelAddress.address g).val := by
  unfold digits
  rw [advance_value,zeros_length,zeros_value,Nat.zero_add,pow_mul prime w (m*m),Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt (LabelAddress.address g).isLt]

/-- Inside a child label box the inherited label address keeps its high
digits and obtains its low digits from the current child label. The row
selected by the cyclic role split contributes only whole parent boxes. -/
theorem value_in_child_box (m w row beforeH block upper box : ℕ) (label : Fin box)
    (shape : (prime^w)^(m*m) = upper*box) (aligned : (prime^w)^(m*m) ∣ beforeH) :
    value (digits m w (row*beforeH + block*box + label.val)) =
      (block % upper)*box + label.val := by
  obtain ⟨blocks,h⟩ := aligned
  unfold digits
  rw [advance_value, zeros_length, zeros_value, Nat.zero_add, pow_mul, h, shape]
  have positive : 0 < upper*box := by rw [← shape]; exact pow_pos (pow_pos prime_prime.pos _) _
  have upperPos : 0 < upper := Nat.pos_of_mul_pos_right positive
  have fits : block % upper * box + label.val < upper*box := by
    calc
      _ < (block % upper + 1)*box := by rw [Nat.add_mul, one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right box (Nat.mod_lt _ upperPos)
  have index : row*(upper*box*blocks) + block*box + label.val =
      (block % upper * box + label.val) + (upper*box)*(row*blocks + block/upper) := by
    calc
      _ = row*(upper*box*blocks) + (block % upper + upper*(block/upper))*box + label.val := by
        rw [Nat.mod_add_div]
      _ = _ := by ring
  rw [index, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt fits]

/-- In tape order the varying child label precedes the fixed high part of
the inherited label. Both fields keep their leading zeroes. -/
theorem digits_in_child_box (m low high row beforeH block : ℕ)
    (label : Fin ((prime^low)^(m*m))) (aligned : (prime^(low+high))^(m*m) ∣ beforeH) :
    digits m (low+high) (row*beforeH + block*((prime^low)^(m*m)) + label.val) =
      digits m low label.val ++ digits m high block := by
  have shape : (prime^(low+high))^(m*m) = (prime^high)^(m*m)*(prime^low)^(m*m) := by
    rw [pow_add, mul_pow, Nat.mul_comm]
  apply PrefixCounterData.word_injective prime_prime.two_le
  · simp [digits, Nat.add_mul]
  · rw [value_in_child_box _ _ _ _ _ _ _ label shape aligned, PrefixAddressData.value_append]
    have lowValue : value (digits m low label.val) = label.val :=
      enumerate_value prime_prime.two_le _ _ (by simpa only [pow_mul] using label.isLt)
    rw [lowValue]
    simp only [digits, advance_value, zeros_length, zeros_value, Nat.zero_add, advance_length, pow_mul]
    ring

/-- Reading a whole atom from the directory recovers the original matrix coefficient. -/
theorem coefficient_at (m w p : ℕ) (g : LabelPadding.Label m w) (r c : Fin m) :
    value (digits m w (p*(prime^w)^(m*m)+(LabelAddress.address g).val)) /
      (prime^w)^FlatCoordinateLayout.suffixFields (finProdFinEquiv (c,r)) % (prime^w) =
        (g r c).val := by
  rw [value_at, LabelAddress.entry]

/-- Keep the frozen ancestor labels in front of the new label. -/
def entry (ancestor : ℕ → List (Fin (prime+4))) (m w j : ℕ) :=
  ancestor j ++ (digits m w j).map digitSymbol

/-- The full replay word for one child record. Within a child box, only
the low label digits depend on the record; the ancestor and high digits
can be read once for the whole box. -/
theorem entry_in_child_box (ancestor : ℕ → List (Fin (prime+4))) (m low high row blocks block : ℕ)
    (label : Fin ((prime^low)^(m*m))) :
    let box := (prime^low)^(m*m)
    let upper := (prime^high)^(m*m)
    let parentBox := (prime^(low+high))^(m*m)
    let beforeH := parentBox*blocks
    entry (fun j => ancestor (j/parentBox)) m (low+high) (row*beforeH + block*box + label.val) =
      ancestor (row*blocks + block/upper) ++ (digits m low label.val).map digitSymbol ++
        (digits m high block).map digitSymbol := by
  intro box upper parentBox beforeH
  have shape : parentBox = box*upper := by simp only [parentBox, box, upper, pow_add, mul_pow]
  have pos : 0 < parentBox := pow_pos (pow_pos prime_prime.pos _) _
  have index : row*beforeH + block*box + label.val = (label.val + box*block) + parentBox*(row*blocks) := by
    dsimp only [beforeH]
    ring
  have addr : (row*beforeH + block*box + label.val)/parentBox = row*blocks + block/upper := by
    rw [index, Nat.add_mul_div_left _ _ pos, shape, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (pow_pos (pow_pos prime_prime.pos _) _),
      Nat.div_eq_of_lt label.isLt, Nat.zero_add, Nat.add_comm]
  simp only [entry, addr]
  dsimp only [box]
  rw [digits_in_child_box m low high row beforeH block label (dvd_mul_right parentBox blocks),
    List.map_append, List.append_assoc]

theorem entry_length (ancestor : ℕ → List (Fin (prime+4))) (m w j : ℕ) :
    (entry ancestor m w j).length = (ancestor j).length+w*(m*m) := by simp [entry,digits]

/-- A child scanner numbers the selected records consecutively, while their
directory entries retain the original label addresses. -/
theorem child_prefixes (selected : List ℕ) (ancestor : ℕ → List (Fin (prime+4)))
    (m w a : ℕ) (width : ∀ j ∈ selected, (ancestor j).length = a) :
    let word := fun i : ℕ => entry ancestor m w (selected[i]?.getD 0)
    selected.flatMap (entry ancestor m w) = (List.range selected.length).flatMap word ∧
      ∀ i < selected.length, (word i).length = a+w*(m*m) := by
  intro word
  have indices : (List.range selected.length).map (fun i => selected[i]?.getD 0) = selected := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [hj]
  constructor
  · conv_lhs => rw [← indices]
    rw [List.flatMap_map]
  · intro i hi
    simp [word,hi,entry_length,width _ (List.getElem_mem hi)]

variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q prime U}

/-- The retained class mask orders full prefix entries exactly as it orders the child payloads. -/
theorem split_exec {src mask width symbols ts tm acc out : Fin T}
    (hr : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    (xs : List ℕ) (m w a : ℕ) (branch : Matrix (Fin m) (Fin m) (ZMod prime) → Bool)
    (ancestor : ℕ → List (Fin (prime+4))) (ha : ∀ j ∈ xs, (ancestor j).length = a)
    (u : HS T Q prime U) (S : Stacks T prime) (tail : List (Fin (prime+4))) :
    let keep := fun j => branch (LabelStock.residue m w 1 j)
    let word := entry ancestor m w
    let W := a+w*(m*m)
    S.R src = xs.flatMap word ++ tail → S.R mask = (xs.map keep).map bitSymbol →
    (S.R width).length = W → (∀ k ∈ [symbols,ts,tm,acc], S.R k = []) →
    ∃ u' n, u'.user = u.user ∧ n ≤ 2*(xs.length*(16*W+10)+16) ∧
      Exec body (LabelSplit.program src mask width symbols ts tm acc out) (mk u S) n
        (mk u' {S with R := Function.update S.R out ((xs.filter keep).flatMap word ++
          (xs.filter (fun j => !(keep j))).flatMap word ++ S.R out)}) := by
  intro keep word W hs hm hw hf
  exact LabelSplit.split_exec hr xs keep word W
    (fun j hj => by simp [word,W,entry_length,ha j hj]) u S tail hs hm hw hf

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectory
