import IntegerMultBounds.Machine.KeyRoutine
import IntegerMultBounds.Compact.PackedInverseValue
import IntegerMultBounds.Compact.ToggleValue
import IntegerMultBounds.Compact.GuardValue
import IntegerMultBounds.Compact.TapeRepair

/-! The key routine's words are the repair scan's key data for the concrete
early instance: ranks are the addresses in lexicographic order, the counter
word at rank `j` splits into the address words, the flag is membership in
the exceptional set, and the appended words are the destination rank's bits. -/

namespace IntegerMultBounds.Compact.PowerTwo

open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine (putWord bitSymbol blank)
open IntegerMultBounds.Machine.Gather (field)
open Radix

section Rank

/-- A field of a nonnegative integer modulus as a finite type. -/
def fieldFin (M : ℤ) (hM : 0 ≤ M) : Field M ≃ Fin M.toNat where
  toFun := fun x => ⟨x.val.toNat, by have := x.property; omega⟩
  invFun := fun i => ⟨i.val, by have := i.isLt; omega⟩
  left_inv := fun x => Subtype.ext (by have := x.property; simp; omega)
  right_inv := fun i => by ext; simp

theorem fieldFin_val (M : ℤ) (hM : 0 ≤ M) (x : Field M) :
    ((fieldFin M hM x : ℕ) : ℤ) = x.val := by
  simp [fieldFin]; have := x.property; omega

/-- Addresses in lexicographic order: the first component is the low part. -/
def lexEquiv (Q B : ℤ) (hQ : 0 ≤ Q) (hB : 0 ≤ B) :
    Field Q × Field B ≃ Fin (B.toNat * Q.toNat) :=
  (Equiv.prodComm _ _).trans ((Equiv.prodCongr (fieldFin B hB) (fieldFin Q hQ)).trans finProdFinEquiv)

theorem lexEquiv_val (Q B : ℤ) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (x : Field Q × Field B) :
    ((lexEquiv Q B hQ hB x : ℕ) : ℤ) = x.1.val + Q * x.2.val := by
  simp only [lexEquiv, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap, Equiv.prodCongr_apply,
    Prod.map, finProdFinEquiv_apply_val]
  push_cast
  rw [fieldFin_val, fieldFin_val]
  have : ((Q.toNat : ℕ) : ℤ) = Q := by omega
  rw [this]

end Rank

section Words

theorem value_field_prefix (cs : List Bool) (d : ℕ) (hd : d ≤ cs.length) :
    value (field cs 0 d) = value cs % 2 ^ d := by
  rw [field_take cs d hd, value_take_add_drop cs d, List.length_take, min_eq_left hd]
  have := Counter.value_lt (cs.take d)
  rw [List.length_take, min_eq_left hd] at this
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]

theorem value_field_middle (cs : List Bool) (m d : ℕ) (h : m + d ≤ cs.length) :
    value (field cs m d) = value cs / 2 ^ m % 2 ^ d := by
  have hsplit := value_take_add_drop cs m
  rw [List.length_take, min_eq_left (by omega)] at hsplit
  have hlt := Counter.value_lt (cs.take m)
  rw [List.length_take, min_eq_left (by omega)] at hlt
  have hdiv : value cs / 2 ^ m = value (cs.drop m) := by
    rw [hsplit, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  rw [hdiv, ← value_field_prefix (cs.drop m) d (by rw [List.length_drop]; omega)]
  congr 1
  have := field_append_right (cs.take m) (cs.drop m) 0 d
  rw [List.take_append_drop, List.length_take, min_eq_left (by omega), add_zero] at this
  exact this

/-- The fixed-width counter's value after `j` increments from zero. -/
theorem advance_value (j : ℕ) (bs : List Bool) :
    value (Counter.advance j bs) = (value bs + j) % 2 ^ bs.length := by
  induction j with
  | zero => simp [Counter.advance, Nat.mod_eq_of_lt (Counter.value_lt bs)]
  | succ j ih =>
    rw [Machine.RepairScan.advance_succ', Counter.increment_value, ih, Machine.RepairScan.advance_length,
      Nat.mod_add_mod, Nat.add_assoc]

theorem value_replicate_false' (c : ℕ) : value (List.replicate c false) = 0 := value_replicate_false c

theorem counter_value (c j : ℕ) (hj : j < 2 ^ c) :
    value (Machine.RepairScan.counter c j) = j := by
  rw [Machine.RepairScan.counter, advance_value, value_replicate_false', List.length_replicate,
    zero_add, Nat.mod_eq_of_lt hj]

/-- The binary expansion of a word's value is the word. -/
theorem testBit_value (xs : List Bool) (j : ℕ) : Nat.testBit (value xs) j = xs.getD j false := by
  induction xs generalizing j with
  | nil => simp [value]
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [value, Nat.testBit_zero, List.getD_cons_zero]
      cases x <;> simp [Nat.add_mul_mod_self_left]
    | succ j =>
      rw [Nat.testBit_succ, List.getD_cons_succ, ← ih j]
      congr 1
      simp only [value]
      cases x <;> simp [Nat.add_mul_div_left]

theorem rankBits_value (xs : List Bool) : rankBits xs.length (value xs) = xs := by
  apply List.ext_getElem
  · simp [rankBits]
  · intro i h1 h2
    simp only [rankBits, List.getElem_ofFn, testBit_value]
    exact List.getD_eq_getElem _ _ h2

end Words

section Instance

/-- The control bits as integers. -/
abbrev controls (Zb : List Bool) : List ℤ := Zb.map ctrl

theorem controls_bits (Zb : List Bool) : Bits (controls Zb) := by
  intro z hz
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hz
  cases x <;> simp [ctrl]

theorem controls_length (Zb : List Bool) : (controls Zb).length = Zb.length := by simp

/-- The instance's radices. -/
abbrev Bi (b : ℕ) : ℤ := (2 : ℤ) ^ b
abbrev Li (q : ℕ) : ℤ := (2 : ℤ) ^ (q - 1)

theorem Li_pos (q : ℕ) : 0 < Li q := by positivity
theorem Bi_one (b : ℕ) : 1 ≤ Bi b := one_le_pow₀ (by norm_num)
theorem two_Li (q : ℕ) (hq : 1 ≤ q) : 2 * Li q = (2 : ℤ) ^ q := by
  rw [Li, ← pow_succ']; congr 1; omega

/-- The instance's permutations, exceptional set and rank order. -/
abbrev Sperm (q b : ℕ) (Zb : List Bool) : Equiv.Perm (EarlyAddress (Bi b) (Li q) (controls Zb).length) :=
  packedEarlyPerm (2 * Li q) (Bi b) (by have := Li_pos q; omega) (by have := Bi_one b; omega) (controls Zb)
abbrev Tperm (q b : ℕ) (Zb : List Bool) : Equiv.Perm (EarlyAddress (Bi b) (Li q) (controls Zb).length) :=
  earlyIdeal (Bi b) (Li q) (Li_pos q) (controls Zb) (controls_bits Zb)
abbrev badSet (q b : ℕ) (Zb : List Bool) (y : EarlyAddress (Bi b) (Li q) (controls Zb).length) : Prop :=
  ¬ earlyGood (Bi b) (Li q) (controls Zb).length y
abbrev Mi (q b : ℕ) (Zb : List Bool) : ℕ :=
  ((Bi b) ^ (controls Zb).length).toNat * ((2 * Li q) ^ (controls Zb).length).toNat
noncomputable abbrev rankEquiv (q b : ℕ) (Zb : List Bool) :
    EarlyAddress (Bi b) (Li q) (controls Zb).length ≃ Fin (Mi q b Zb) :=
  lexEquiv ((2 * Li q) ^ (controls Zb).length) ((Bi b) ^ (controls Zb).length)
    (by positivity) (by positivity)

theorem twoL_pow (q : ℕ) (Zb : List Bool) (hq : 1 ≤ q) :
    ((2 * Li q) ^ (controls Zb).length) = (2 : ℤ) ^ (Zb.length * q) := by
  rw [two_Li q hq, controls_length, pow_blocks]
theorem B_pow (b : ℕ) (Zb : List Bool) : ((Bi b) ^ (controls Zb).length) = (2 : ℤ) ^ (Zb.length * b) := by
  rw [Bi, controls_length, pow_blocks]
theorem Mi_eq (q b : ℕ) (Zb : List Bool) (hq : 1 ≤ q) :
    Mi q b Zb = 2 ^ (Zb.length * b) * 2 ^ (Zb.length * q) := by
  rw [Mi, twoL_pow q Zb hq, B_pow,
    show ((2 : ℤ) ^ (Zb.length * b)) = ((2 ^ (Zb.length * b) : ℕ) : ℤ) by push_cast; rfl,
    show ((2 : ℤ) ^ (Zb.length * q)) = ((2 ^ (Zb.length * q) : ℕ) : ℤ) by push_cast; rfl,
    Int.toNat_natCast, Int.toNat_natCast]

/-- The address words of a rank. -/
abbrev Vw (q : ℕ) (Zb cs : List Bool) : List Bool := field cs 0 (Zb.length * q)
abbrev Ww (q b : ℕ) (Zb cs : List Bool) : List Bool := field cs (Zb.length * q) (Zb.length * b)

theorem Vw_bound (q : ℕ) (Zb cs : List Bool) (hq : 1 ≤ q) :
    (value (Vw q Zb cs) : ℤ) < (2 * Li q) ^ (controls Zb).length := by
  rw [twoL_pow q Zb hq]
  have := Counter.value_lt (Vw q Zb cs)
  rw [Machine.Gather.field_length] at this
  exact_mod_cast this
theorem Ww_bound (q b : ℕ) (Zb cs : List Bool) :
    (value (Ww q b Zb cs) : ℤ) < (Bi b) ^ (controls Zb).length := by
  rw [B_pow]
  have := Counter.value_lt (Ww q b Zb cs)
  rw [Machine.Gather.field_length] at this
  exact_mod_cast this

/-- The rank's address. -/
def addr (q b : ℕ) (Zb cs : List Bool) (hq : 1 ≤ q) : EarlyAddress (Bi b) (Li q) (controls Zb).length :=
  (⟨(value (Vw q Zb cs) : ℤ), by positivity, Vw_bound q Zb cs hq⟩,
   ⟨(value (Ww q b Zb cs) : ℤ), by positivity, Ww_bound q b Zb cs⟩)

/-- A rank's counter word splits into its address. -/
theorem rank_split (q b : ℕ) (Zb cs : List Bool) (hq : 1 ≤ q) (j : ℕ) (hj : j < Mi q b Zb)
    (hcs : value cs = j) (hcsl : Zb.length * q + Zb.length * b ≤ cs.length) :
    (rankEquiv q b Zb).symm ⟨j, hj⟩ = addr q b Zb cs hq := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  have h := lexEquiv_val ((2 * Li q) ^ (controls Zb).length) ((Bi b) ^ (controls Zb).length)
    (by positivity) (by positivity) (addr q b Zb cs hq)
  have hval : ((((rankEquiv q b Zb) (addr q b Zb cs hq)).val : ℕ) : ℤ) = (j : ℤ) := by
    simp only [rankEquiv]
    rw [h]
    simp only [addr]
    rw [twoL_pow q Zb hq, value_field_prefix cs _ (by omega), value_field_middle cs _ _ hcsl, hcs]
    rw [Mi_eq q b Zb hq] at hj
    have hdiv : j / 2 ^ (Zb.length * q) < 2 ^ (Zb.length * b) :=
      (Nat.div_lt_iff_lt_mul (by positivity)).mpr hj
    rw [Nat.mod_eq_of_lt hdiv]
    have := Nat.mod_add_div j (2 ^ (Zb.length * q))
    exact_mod_cast this
  exact_mod_cast hval.symm

/-- The guard flags of the rank are the repair scan's membership flag. -/
theorem flag_bridge (q b : ℕ) (hq1 : b + 3 ≤ q) (Zb cs C1 C2 C3 : List Bool)
    (hC1 : C1.length = q - 1) (hC2 : C2.length = q - 1) (hC3 : C3.length = b)
    (hC1v : value C1 = 2 ^ (b + 1)) (hC2v : value C2 + 2 ^ (b + 1) + 1 = 2 ^ (q - 1))
    (hC3v : value C3 + 2 = 2 ^ b) (j : ℕ) (hj : j < Mi q b Zb) (hcs : value cs = j)
    (hcsl : Zb.length * q + Zb.length * b ≤ cs.length) :
    (Machine.GuardGadget.flagWordW q b Zb.length (Vw q Zb cs) (Ww q b Zb cs) C1 C2 C3 Zb.length).any id =
      rankFlag (rankEquiv q b Zb) (badSet q b Zb) j := by
  have hq : 1 ≤ q := by omega
  rw [rankFlag, dif_pos hj, rank_split q b Zb cs hq j hj hcs hcsl]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  have := flags_any q b (controls Zb).length (Vw q Zb cs) (Ww q b Zb cs) C1 C2 C3
    (by rw [controls_length]; exact Machine.Gather.field_length _ _ _)
    (by rw [controls_length]; exact Machine.Gather.field_length _ _ _) hq1 hC1 hC2 hC3 hC1v hC2v hC3v
    (Vw_bound q Zb cs hq) (Ww_bound q b Zb cs)
  have hL : Machine.GuardGadget.flagWordW q b (controls Zb).length (Vw q Zb cs) (Ww q b Zb cs) C1 C2 C3
      (controls Zb).length = Machine.GuardGadget.flagWordW q b Zb.length (Vw q Zb cs) (Ww q b Zb cs)
      C1 C2 C3 Zb.length := by rw [controls_length]
  rw [hL] at this
  rw [this]
  exact Iff.rfl

/-- `packedEarly` at a radix given by an equation. -/
theorem inverse_value' (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool)
    (hV : V2.length = Z.length * q) (hW : W2.length = Z.length * b) (Q : ℤ) (hQ : Q = (2 : ℤ) ^ q) :
    packedEarly Q ((2 : ℤ) ^ b) (Z.map ctrl) (value (Machine.PackedInverse.v q b hb hbq V2 W2 Z))
      (value (Machine.PackedInverse.w q b hb hbq V2 W2 Z)) = ((value V2 : ℤ), (value W2 : ℤ)) := by
  subst hQ
  exact inverse_value q b hb hbq V2 W2 Z hV hW

/-- The recovered words as an address. -/
def recovered (q b : ℕ) (hb : 1 ≤ b) (hbq1 : b + 1 ≤ q) (Zb cs : List Bool) (hq : 1 ≤ q) :
    EarlyAddress (Bi b) (Li q) (controls Zb).length :=
  (⟨(value (Machine.PackedInverse.v q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb) : ℤ), by positivity, by
      rw [twoL_pow q Zb hq]
      have hl := (Machine.PackedInverse.lengths q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb
        (Machine.Gather.field_length _ _ _) (Machine.Gather.field_length _ _ _)).2.2.2.2.2.2.2.2.2
      have := Counter.value_lt (Machine.PackedInverse.v q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb)
      rw [hl] at this
      exact_mod_cast this⟩,
   ⟨(value (Machine.PackedInverse.w q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb) : ℤ), by positivity, by
      rw [B_pow]
      have hl := (Machine.PackedInverse.lengths q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb
        (Machine.Gather.field_length _ _ _) (Machine.Gather.field_length _ _ _)).2.2.2.2.2.2.2.1
      have := Counter.value_lt (Machine.PackedInverse.w q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb)
      rw [hl] at this
      exact_mod_cast this⟩)

/-- The inverse program's words are the packed permutation's preimage of the address. -/
theorem inverse_bridge (q b : ℕ) (hb : 1 ≤ b) (hbq1 : b + 1 ≤ q) (Zb cs : List Bool) (hq : 1 ≤ q) :
    (Sperm q b Zb).symm (addr q b Zb cs hq) = recovered q b hb hbq1 Zb cs hq := by
  rw [Equiv.symm_apply_eq]
  have h := packedEarlyPerm_agrees (2 * Li q) (Bi b) (by have := Li_pos q; omega)
    (by have := Bi_one b; omega) (controls Zb) (recovered q b hb hbq1 Zb cs hq)
  simp only at h
  rw [show (recovered q b hb hbq1 Zb cs hq).1.val =
      value (Machine.PackedInverse.v q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb) from rfl,
    show (recovered q b hb hbq1 Zb cs hq).2.val =
      value (Machine.PackedInverse.w q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb) from rfl,
    inverse_value' q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb (Machine.Gather.field_length _ _ _)
      (Machine.Gather.field_length _ _ _) (2 * Li q) (two_Li q hq)] at h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst h).symm
  · exact Subtype.ext (congrArg Prod.snd h).symm

/-- The toggled words as an address. -/
def toggled (q b : ℕ) (hb : 1 ≤ b) (hbq1 : b + 1 ≤ q) (Zb cs : List Bool) (hq : 1 ≤ q) :
    EarlyAddress (Bi b) (Li q) (controls Zb).length :=
  (⟨(value (List.zipWith xor (Machine.PackedInverse.v q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb)
      (toggleMask q Zb)) : ℤ), by positivity, by
      rw [twoL_pow q Zb hq]
      have hl := (Machine.PackedInverse.lengths q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb
        (Machine.Gather.field_length _ _ _) (Machine.Gather.field_length _ _ _)).2.2.2.2.2.2.2.2.2
      have := Counter.value_lt (List.zipWith xor
        (Machine.PackedInverse.v q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb) (toggleMask q Zb))
      rw [List.length_zipWith, hl, toggleMask_length q hq, min_self] at this
      exact_mod_cast this⟩,
   (recovered q b hb hbq1 Zb cs hq).2)

/-- The ideal map on the recovered address is the toggled address. -/
theorem toggle_bridge (q b : ℕ) (hb : 1 ≤ b) (hbq1 : b + 1 ≤ q) (Zb cs : List Bool) (hq : 1 ≤ q) :
    (Tperm q b Zb) (recovered q b hb hbq1 Zb cs hq) = toggled q b hb hbq1 Zb cs hq := by
  apply Prod.ext
  · apply Subtype.ext
    have h := idealTarget_value (Li q) (Li_pos q) (controls Zb) (controls_bits Zb)
      (recovered q b hb hbq1 Zb cs hq).1
    have hpack : ∀ xv : ℤ, pack (2 * Li q) (toggleList (digits (2 * Li q) (controls Zb).length xv)
        (controls Zb)) = pack ((2 : ℤ) ^ q) (toggleList (digits ((2 : ℤ) ^ q) Zb.length xv) (controls Zb)) :=
      fun xv => by rw [two_Li q hq, controls_length]
    show (idealTarget (Li q) (Li_pos q) (controls Zb) (controls_bits Zb)
      (recovered q b hb hbq1 Zb cs hq).1).val = _
    rw [h, hpack]
    exact (toggle_word_value q hq _ Zb (Machine.PackedInverse.lengths q b hb hbq1 (Vw q Zb cs)
      (Ww q b Zb cs) Zb (Machine.Gather.field_length _ _ _)
      (Machine.Gather.field_length _ _ _)).2.2.2.2.2.2.2.2.2).symm
  · rfl

theorem map_zip_xor (xs ys : List Bool) :
    (xs.zip ys).map (fun c => xor c.1 c.2) = List.zipWith xor xs ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => cases ys <;> simp [ih]

/-- The appended words are the destination rank's bits. -/
theorem bits_bridge (q b : ℕ) (hb : 1 ≤ b) (hbq1 : b + 1 ≤ q) (Zb cs : List Bool) (hq : 1 ≤ q)
    (j : ℕ) (hj : j < Mi q b Zb) (hcs : value cs = j)
    (hcsl : Zb.length * q + Zb.length * b ≤ cs.length) :
    rankKey (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb) (Zb.length * q + Zb.length * b) j =
      Machine.ColumnTransducer.digits Machine.ColumnTransducer.xorRule 0
        ((Machine.PackedInverse.v q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb).zip
          (Machine.Gather.gather (fun _ z => z) (Machine.PackedArith.controlsAt q b hb hbq1)
            (Ww q b Zb cs) Zb Zb.length)) ++
        Machine.PackedInverse.w q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb := by
  obtain ⟨_, _, _, _, _, _, _, hwl, _, hvl⟩ := Machine.PackedInverse.lengths q b hb hbq1 (Vw q Zb cs)
    (Ww q b Zb cs) Zb (Machine.Gather.field_length _ _ _) (Machine.Gather.field_length _ _ _)
  rw [rankKey, dif_pos hj]
  have h1 : destRank (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb) ⟨j, hj⟩ =
      (rankEquiv q b Zb) (toggled q b hb hbq1 Zb cs hq) := by
    show (rankEquiv q b Zb) ((Tperm q b Zb) ((Sperm q b Zb).symm ((rankEquiv q b Zb).symm ⟨j, hj⟩))) = _
    rw [rank_split q b Zb cs hq j hj hcs hcsl, inverse_bridge, toggle_bridge]
  rw [h1, Machine.ColumnTransducer.xorRule_digits, map_zip_xor, gather_controls]
  set Vt := List.zipWith xor (Machine.PackedInverse.v q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb)
    (toggleMask q Zb) with hVt
  set Wr := Machine.PackedInverse.w q b hb hbq1 (Vw q Zb cs) (Ww q b Zb cs) Zb with hWr
  have hVtl : Vt.length = Zb.length * q := by
    rw [hVt, List.length_zipWith, hvl, toggleMask_length q hq, min_self]
  have hval : (((rankEquiv q b Zb) (toggled q b hb hbq1 Zb cs hq) : ℕ) : ℤ) = value (Vt ++ Wr) := by
    simp only [rankEquiv]
    rw [lexEquiv_val]
    change ((value Vt : ℤ)) + (2 * Li q) ^ (controls Zb).length * (value Wr : ℤ) = _
    rw [twoL_pow q Zb hq, Machine.ColumnTransducer.value_append, hVtl]
    push_cast
    ring
  have hk : Zb.length * q + Zb.length * b = (Vt ++ Wr).length := by
    rw [List.length_append, hVtl, hwl]
  rw [hk, show (((rankEquiv q b Zb) (toggled q b hb hbq1 Zb cs hq) : Fin _) : ℕ) = value (Vt ++ Wr) by
    exact_mod_cast hval, rankBits_value]

end Instance

end IntegerMultBounds.Compact.PowerTwo
