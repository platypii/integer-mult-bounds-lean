import IntegerMultBounds.Compact.PackedControl

/-!
Reversibility of modular address operations on the entire rectangle, including
bad addresses. Canonical integer residues let the equivalence agree literally
with the executable integer program in PackedControl.lean.
-/

namespace IntegerMultBounds.Compact
open Radix

def Field (M : ℤ) := {x : ℤ // 0 ≤ x ∧ x < M}

def fieldAdd {M : ℤ} (hM : 0 < M) (x : Field M) (a : ℤ) : Field M :=
  ⟨(x.val + a) % M, Int.emod_nonneg _ (ne_of_gt hM), Int.emod_lt_of_pos _ hM⟩

theorem fieldAdd_cancel {M : ℤ} (hM : 0 < M) (x : Field M) (a : ℤ) :
    fieldAdd hM (fieldAdd hM x a) (-a) = x := by
  apply Subtype.ext
  change ((x.val + a) % M + -a) % M = x.val
  rw [Int.emod_add_emod, add_neg_cancel_right, Int.emod_eq_of_lt x.property.1 x.property.2]

/-- A controlled modular rotation is a permutation whenever its offset is
independent of its target. The other component can be an arbitrary type. -/
def rotateLeft {M : ℤ} (hM : 0 < M) {C : Type*} (offset : C → ℤ) :
    Equiv.Perm (Field M × C) where
  toFun := fun (x, c) => (fieldAdd hM x (offset c), c)
  invFun := fun (x, c) => (fieldAdd hM x (-offset c), c)
  left_inv := fun (x, c) => by simp [fieldAdd_cancel]
  right_inv := fun (x, c) => by
    have h := fieldAdd_cancel hM x (-offset c)
    simpa using congrArg (fun y => (y, c)) h

def rotateRight {M : ℤ} (hM : 0 < M) {C : Type*} (offset : C → ℤ) :
    Equiv.Perm (C × Field M) :=
  (Equiv.prodComm C (Field M)).trans
    ((rotateLeft hM offset).trans (Equiv.prodComm (Field M) C))

/-- An arbitrary dirty back field is restored by swap, rotate, swap. -/
theorem swap_load_swap {M : ℤ} (hM : 0 < M) (front back : Field M) (offset : ℤ) :
    ((Equiv.prodComm (Field M) (Field M)).trans
      ((rotateRight hM (fun _ => offset)).trans (Equiv.prodComm (Field M) (Field M))))
        (front, back) = (fieldAdd hM front offset, back) := rfl

/-- The actual early-source four rotations as a permutation. This construction
does not require good-address bounds or even bit-valued controls. -/
def packedEarlyPermN (Q B : ℤ) (hQ : 0 < Q) (hB : 0 < B) (n : ℕ) (controls : List ℤ) :
    Equiv.Perm (Field (Q ^ n) × Field (B ^ n)) :=
  let a := rotateLeft (pow_pos hQ n) (fun t : Field (B ^ n) =>
    pack Q (List.zipWith (fun z w => 2 * z * w) controls (digits B n t.val)))
  let b := rotateRight (pow_pos hB n) (fun v : Field (Q ^ n) =>
    pack B ((digits Q n v.val).map (· % 2)))
  let c := rotateLeft (pow_pos hQ n) (fun t : Field (B ^ n) =>
    pack Q (List.zipWith (fun z w => z * (1 - 2 * w)) controls (digits B n t.val)))
  let d := rotateRight (pow_pos hB n) (fun v : Field (Q ^ n) =>
    -pack B (List.zipWith (fun v z => (v % 2 + z) % 2) (digits Q n v.val) controls))
  a.trans (b.trans (c.trans d))

def packedEarlyPerm (Q B : ℤ) (hQ : 0 < Q) (hB : 0 < B) (controls : List ℤ) :
    Equiv.Perm (Field (Q ^ controls.length) × Field (B ^ controls.length)) :=
  packedEarlyPermN Q B hQ hB controls.length controls

theorem packedEarlyPerm_agrees (Q B : ℤ) (hQ : 0 < Q) (hB : 0 < B)
    (controls : List ℤ) (x : Field (Q ^ controls.length) × Field (B ^ controls.length)) :
    let y := packedEarlyPerm Q B hQ hB controls x
    (y.1.val, y.2.val) = packedEarly Q B controls x.1.val x.2.val := by
  simp only [packedEarlyPerm, packedEarlyPermN, rotateLeft, rotateRight, Equiv.trans_apply,
    Equiv.coe_fn_mk, Equiv.prodComm_apply, Prod.swap, fieldAdd, packedEarly, sub_eq_add_neg]

/-- In particular, inverse execution is exact even when guard checks fail. -/
theorem packedEarlyPerm_inverse (Q B : ℤ) (hQ : 0 < Q) (hB : 0 < B)
    (controls : List ℤ) (x : Field (Q ^ controls.length) × Field (B ^ controls.length)) :
    (packedEarlyPerm Q B hQ hB controls).symm (packedEarlyPerm Q B hQ hB controls x) = x :=
  (packedEarlyPerm Q B hQ hB controls).symm_apply_apply x

/-- Execute a family of reversible programs, chosen by an unchanged control. -/
def fiberPerm {C D : Type*} (program : C → Equiv.Perm D) : Equiv.Perm (C × D) where
  toFun := fun (c, d) => (c, program c d)
  invFun := fun (c, d) => (c, (program c).symm d)
  left_inv := fun (c, d) => by simp
  right_inv := fun (c, d) => by simp

/-- Order is `(control, target, temp)`; the unchanged source bits choose the
control load. This is reversible on every address, with modular overflow. -/
def packedLatePerm (Q B : ℤ) (hQ : 0 < Q) (hB : 0 < B) (source : List ℤ) :
    Equiv.Perm (Field (B ^ source.length) ×
      (Field (Q ^ source.length) × Field (B ^ source.length))) :=
  let n := source.length
  let early := fiberPerm (fun u : Field (B ^ n) =>
    packedEarlyPermN Q B hQ hB n ((digits B n u.val).map (· % 2)))
  let load := rotateLeft (pow_pos hB n)
    (fun _ : Field (Q ^ n) × Field (B ^ n) => pack B source)
  early.trans (load.trans (early.trans load.symm))

theorem packedLatePerm_agrees (Q B : ℤ) (hQ : 0 < Q) (hB : 0 < B)
    (source : List ℤ) (x : Field (B ^ source.length) ×
      (Field (Q ^ source.length) × Field (B ^ source.length))) :
    let y := packedLatePerm Q B hQ hB source x
    (y.2.1.val, y.2.2.val, y.1.val) = packedLate Q B source x.2.1.val x.2.2.val x.1.val := by
  simp only [packedLatePerm, fiberPerm, packedEarlyPermN, rotateLeft, rotateRight,
    Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.prodComm_apply, Prod.swap,
    Equiv.symm_mk, fieldAdd, packedLate, packedEarly, List.length_map, digits_length,
    sub_eq_add_neg]

theorem packedLatePerm_inverse (Q B : ℤ) (hQ : 0 < Q) (hB : 0 < B)
    (source : List ℤ) (x : Field (B ^ source.length) ×
      (Field (Q ^ source.length) × Field (B ^ source.length))) :
    (packedLatePerm Q B hQ hB source).symm (packedLatePerm Q B hQ hB source x) = x :=
  (packedLatePerm Q B hQ hB source).symm_apply_apply x

end IntegerMultBounds.Compact
