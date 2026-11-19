module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackCorrectedExchange
public import IntegerMultBounds.MathlibTM2.Cover.Weighted

/-! The corrected exchange schedule on the two packed fields of a stopped leaf. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open M8.Exchange IntegerMultBounds.Swap.Shear
variable {R : Type*} [CommRing R] {d : ℕ}

/-- The corrected machine exchange writes exactly one reversed pair in the packed address. -/
theorem leafAt_packed (w inv : Fin d → R) (s : State (Fin d) R) (i : Fin d)
    (unit : w i * inv i = 1) :
    let z := Weighted.leafAt w inv s i
    Fin.append z.1 z.2 = exchangeAddress (i.castAdd d) (i.rev.natAdd d) (w i) (inv i)
      (Fin.append s.1 s.2) := by
  simp only [Weighted.leafAt,Weighted.leaf_word _ _ unit,exchangeAddress]
  have apart (a b : Fin d) : a.castAdd d ≠ b.natAdd d := by
    intro eq
    have := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at this
    omega
  funext j
  induction j using Fin.addCases with
  | left j =>
    by_cases eq : j = i <;> simp [-Fin.natAdd_eq_addNat,eq,apart]
  | right j =>
    by_cases eq : j = i.rev <;> simp [-Fin.natAdd_eq_addNat,eq,Ne.symm (apart _ _)]

theorem leafSchedule_packed (rank : ℕ) (w inv : Fin d → R) (unit : ∀ i, w i * inv i = 1)
    (s : State (Fin d) R) :
    ((List.finRange d).filter (fun i => i.val < rank)).foldl (fun addr i =>
      exchangeAddress (i.castAdd d) (i.rev.natAdd d) (w i) (inv i) addr) (Fin.append s.1 s.2) =
      Fin.append (Weighted.child rank w inv s).1 (Weighted.child rank w inv s).2 := by
  have schedule := Weighted.child_leafWords rank w inv (fun i _ => unit i) s
  rw [← schedule]
  exact List.foldl_hom (fun z : State (Fin d) R => Fin.append z.1 z.2)
    (fun z i => (leafAt_packed w inv z i (unit i)).symm)

/-- Interpret the occurrence-indexed address function returned by
`correctedSchedule_exec` for every starting payload address. -/
theorem leafSchedule_action {X : Type*} (rank : ℕ) (w inv : Fin d → R)
    (unit : ∀ i, w i * inv i = 1) (s : X → State (Fin d) R) :
    let coords := (List.finRange d).filter (fun i => i.val < rank)
    let start := fun x => Fin.append (s x).1 (s x).2
    let move := fun (addr : X → Fin (d+d) → R) (a : Fin coords.length) x =>
      let i := coords.get a
      exchangeAddress (i.castAdd d) (i.rev.natAdd d) (w i) (inv i) (addr x)
    (List.finRange coords.length).foldl move start = fun x =>
      let z := Weighted.child rank w inv (s x)
      Fin.append z.1 z.2 := by
  intro coords start move
  funext x
  let step := fun (addr : Fin (d+d) → R) (i : Fin d) =>
    exchangeAddress (i.castAdd d) (i.rev.natAdd d) (w i) (inv i) addr
  calc
    _ = (List.finRange coords.length).foldl (fun addr a => step addr (coords.get a)) (start x) :=
      (List.foldl_hom (fun addr : X → Fin (d+d) → R => addr x) (g₁ := move) (fun _ _ => rfl)).symm
    _ = coords.foldl step (start x) := by rw [← List.foldl_map,List.map_get_finRange]
    _ = _ := leafSchedule_packed rank w inv unit (s x)

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open Mult.PhaseCellToeplitz M8 ActualAffineScaling FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {w W Q : ℕ}
local notation "M" => prime^(w+1)
local notation "fields" => d+1
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- Run a stopped leaf on the packed column. The reciprocal archive supplies
the outer shear and a single unit pivot serves every pair. -/
theorem packedLeaf_exec (rank : ℕ) (weight inv : Fin fields → ZMod M)
    (unit : ∀ i, weight i * inv i = 1) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(fields+fields)*W : ℕ) → dest z = blank)
    (original : Fin (M^(fields+fields)*W) → ZMod 2) (state : (Fin (fields+fields) → ZMod M) → State (Fin fields) (ZMod M)) :
    let coords := (List.finRange fields).filter (fun i => i.val < rank)
    let k : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).castAdd fields
    let t : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).rev.natAdd fields
    ∀ (capacity : columnCapacity ≤ Q) (signCapacity : ∀ a : Fin coords.length, (fieldSignProgram (n := (fields+d)+1) (k a) true).1 ≤ Q),
    CorrectedScheduleRuns (P := P) (U := U) (d := fields+d) (n := coords.length) (Q := Q) (w := w) (W := W) k t capacity signCapacity inv coords.get
      (fun _ : Fin 1 => (1 : ZMod M)) (fun _ => 0) H J tail rest dest q original
      (fun x => Fin.append (m := fields) (n := fields) (state x).1 (state x).2)
      (fun x => let z := Weighted.child rank weight inv (state x); Fin.append (m := fields) (n := fields) z.1 z.2) := by
  intro coords k t capacity signCapacity
  have lt (a) : k a < t a := by
    change (coords.get a).val < fields + (coords.get a).rev.val
    have := (coords.get a).isLt
    omega
  have run := correctedSchedule_exec (P := P) (U := U) (d := fields+d) (n := coords.length) (Q := Q) (w := w) (W := W) k t lt capacity signCapacity inv coords.get
    (fun a => weight (coords.get a)) (fun a => (mul_comm ..).trans (unit _))
    (fun _ : Fin 1 => (1 : ZMod M)) (fun _ => 0) (fun _ => isUnit_one)
    H J hm hw hW tail rest dest q empty original (fun x => Fin.append (m := fields) (n := fields) (state x).1 (state x).2)
  have act := leafSchedule_action rank weight inv unit state
  dsimp only at act
  apply (congrArg (fun out => CorrectedScheduleRuns (P := P) (U := U) (d := fields+d) k t
    capacity signCapacity inv coords.get (fun _ : Fin 1 => (1 : ZMod M)) (fun _ => 0) H J tail rest dest q original
    (fun x => Fin.append (m := fields) (n := fields) (state x).1 (state x).2) out) act).mp
  simpa only [Ring.inverse_one,mul_one,k,t,coords,Nat.add_one,Nat.add_succ] using run

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
