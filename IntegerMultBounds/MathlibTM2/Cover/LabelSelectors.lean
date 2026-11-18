module

public import IntegerMultBounds.MathlibTM2.Cover.LabelMask

/-! Enumerate the residue classes in physical order, retaining only one low digit per atom. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelSelectors
noncomputable section

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open IntegerMultBounds.Machine.FlatCoordinateLayout (suffixFields)

private theorem range_blocks (n Q : ℕ) :
    List.range (n*Q) = (List.range n).flatMap (fun i => (List.range Q).map (i*Q+·)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- The low digits of successive atoms, from the least significant atom upwards. -/
def digits (Q k n : ℕ) (i : Fin k) : ZMod prime := ((n / Q^i.val % Q : ℕ) : ZMod prime)

private theorem digits_cons (Q k a b : ℕ) (hb : b < Q) :
    digits Q (k+1) (a*Q+b) = Fin.cons (b : ZMod prime) (digits Q k a) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [digits, Nat.add_mod, Nat.mod_eq_of_lt hb]
  | succ i =>
    simp only [Fin.cons_succ, digits, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm a Q, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, Nat.add_zero]

/-- One cycle of low digits repeats for each possible high part of an atom. -/
def cycle (H : ℕ) : List (ZMod prime) :=
  (List.replicate H ((List.range prime).map Nat.cast)).flatten

private theorem cycle_eq (H : ℕ) :
    cycle H = (List.range (H*prime)).map Nat.cast := by
  rw [range_blocks, List.map_flatMap]
  unfold cycle
  rw [← List.length_range (n := H), ← List.map_const']
  simp only [List.length_range]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  simp [List.map_map, Function.comp_def]

/-- Extend each higher-atom prefix by the same low-digit cycle. -/
def classes (H : ℕ) : (k : ℕ) → List (Fin k → ZMod prime)
  | 0 => [Fin.elim0]
  | k+1 => (classes H k).flatMap fun a => (cycle H).map fun b => Fin.cons b a

theorem classes_eq (H k : ℕ) :
    classes H k = (List.range ((H*prime)^k)).map (digits (H*prime) k) := by
  induction k with
  | zero =>
    simp only [classes, pow_zero, List.range_one, List.map_cons, List.map_nil]
    congr 2
    funext i
    exact i.elim0
  | succ k ih =>
    rw [classes, ih, cycle_eq, pow_succ, range_blocks ((H*prime)^k) (H*prime), List.map_flatMap, List.flatMap_map]
    simp only [List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro a _
    simp only [List.map_map]
    apply List.map_congr_left
    intro b hb
    exact (digits_cons _ _ _ _ (List.mem_range.mp hb)).symm

private theorem digits_period (Q k p j : ℕ) (hQ : 0 < Q) :
    digits Q k (p*Q^k+j) = digits Q k j := by
  funext i
  have he : k = i.val+((k-i.val-1)+1) := by omega
  have hpow : p*Q^k = Q^i.val*((p*Q^(k-i.val-1))*Q) := by
    conv_lhs => rw [he, pow_add, pow_succ]
    ring
  simp only [digits, hpow, Nat.mul_add_div (pow_pos hQ _), Nat.add_mod,
    Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]

/-- Assemble the column-major label from digits enumerated least significant first. -/
def matrix (m : ℕ) (a : Fin (m*m) → ZMod prime) : Matrix (Fin m) (Fin m) (ZMod prime) :=
  fun r c => a (finProdFinEquiv (c,r)).rev

theorem residue_eq (m w i : ℕ) :
    LabelStock.residue m w 1 i = matrix m (digits (prime^w) (m*m) i) := by
  funext r c
  simp [matrix, digits, LabelStock.residue, suffixFields, Fin.rev, Nat.sub_sub, Nat.add_comm]

/-- A fixed finite test on the low digits of one box entry. -/
def accept (m : ℕ) (a : Fin (m*m) → ZMod prime) : Bool :=
  decide ((matrix m a).det ≠ 0)

/-- Read every record in physical order and apply a fixed function to its residue digits. -/
def recordMap (v : IntegerMultBounds.Machine.RecursiveInterchangeLayout.Descriptor)
    (m w : ℕ) (f : (Fin (m*m) → ZMod prime) → α) :=
  (List.range (LabelMask.records v)).map (fun j => f (digits (prime^w) (m*m) j))

theorem selectors_eq (v : IntegerMultBounds.Machine.RecursiveInterchangeLayout.Descriptor)
    (m w : ℕ) : LabelMask.selectors m w (LabelMask.records v) = recordMap v m w (accept m) :=
  List.map_congr_left fun j _ => by simp only [LabelStock.live, accept, residue_eq]

theorem recordMap_eq (v : IntegerMultBounds.Machine.RecursiveInterchangeLayout.Descriptor)
    (m w B : ℕ) (hw : 0 < w) (hv : v.beforeH = B*prime^(m*(w*m)))
    (f : (Fin (m*m) → ZMod prime) → α) :
    recordMap v m w f = (List.replicate (v.beforeRows*v.rows*B)
      ((classes (prime^(w-1)) (m*m)).map f)).flatten := by
  let Q := prime^w
  have hQ : 0 < Q := pow_pos prime_prime.pos _
  have hr : LabelMask.records v = (v.beforeRows*v.rows*B)*Q^(m*m) := by
    unfold LabelMask.records Q
    rw [hv, ← pow_mul, Nat.mul_assoc (v.beforeRows*v.rows)]
    congr 3
    ring
  have hp : prime^(w-1)*prime = Q := by rw [← pow_succ]; unfold Q; congr 1; omega
  rw [classes_eq, hp, recordMap, hr, range_blocks, List.map_flatMap, List.flatMap_def]
  apply congrArg List.flatten
  rw [← List.length_range (n := v.beforeRows*v.rows*B), ← List.map_const']
  simp only [List.length_range]
  apply List.map_congr_left
  intro p _
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _
  exact congrArg f (digits_period Q (m*m) p j hQ)

end
end IntegerMultBounds.MathlibTM2.Cover.LabelSelectors
