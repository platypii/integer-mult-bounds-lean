module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackCorrectedExchange
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodPayload

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

/-- Inactive coordinates carry the identity weight in the semantic address map. -/
def extendLeafWeight {rank n : ℕ} (a : Fin rank → R) (j : Fin n) : R :=
  if h : j.val < rank then a ⟨j.val,h⟩ else 1

theorem packedLeaf_childFields {r g : ℕ} (weight inv : Fin r → R)
    (hg tg : Fin g → R) (s : State (Fin r) R) :
    Weighted.child r (extendLeafWeight weight) (extendLeafWeight inv) (childFields hg tg s) =
      childFields hg tg (Weighted.child r weight inv s) := by
  rw [childFields_apply]
  simp [extendLeafWeight]

/-- View the serialized head and tail coordinates in place. -/
def leafFields {n : ℕ} {R : Type*} (x : Fin (n+n) → R) : State (Fin n) R :=
  (fun i => x (i.castAdd n),fun i => x (i.natAdd n))

theorem leafFields_append {n : ℕ} {R : Type*} (s : State (Fin n) R) :
    leafFields (Fin.append s.1 s.2) = s := by
  apply Prod.ext <;> funext i <;> simp only [leafFields,Fin.append_left,Fin.append_right]

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open Mult.PhaseCellToeplitz M8 ActualAffineScaling FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
/-- Read the returned payload on the caller's tape, including every spectator slice. -/
theorem packedLeaf_return {A T b w r g W : ℕ} [NeZero (b^(w+1))] {α : Type}
    (weight inv : Fin r → ZMod (b^(w+1))) (bank : Fin 35 ↪ Fin T) (H J : ℕ)
    (archive : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (original : Fin ((b^(w+1))^((r+g)+(r+g))*W) → α) (S : Stacks T A) :
    ColumnRecordReady bank H J archive sym source dest p q original
      (fun x => let z := Weighted.child r (extendLeafWeight weight) (extendLeafWeight inv)
                  (leafFields (n := r+g) x)
                Fin.append z.1 z.2) S →
    ∃ out : Fin ((b^(w+1))^((r+g)+(r+g))*W) → α, RecordReady (d := (r+g)+(r+g)) (b := b) (w := w) (W := W) bank H J archive sym source dest p q out S ∧
      ∀ (hg tg : Fin g → ZMod (b^(w+1))) (x : State (Fin r) (ZMod (b^(w+1)))) (j : Fin W),
        let addr := fun y => let z := childFields hg tg y; index (Fin.append z.1 z.2) j
        out (addr (Weighted.child r weight inv x)) = original (addr x) := by
  rintro ⟨out,ready,action⟩
  refine ⟨out,ready,?_⟩
  intro hg tg x j
  let z := childFields hg tg x
  have result := action (Fin.append z.1 z.2) j
  simpa only [leafFields_append,z,packedLeaf_childFields] using result

variable [M8.Machine.Net] {P U : Type} {w W Q : ℕ}
local notation "M" => prime^(w+1)
local notation "fields" => d+1
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- Run a stopped leaf on the packed column. The reciprocal archive supplies
the outer shear and a single unit pivot serves every pair. -/
theorem packedLeaf_exec (rank : ℕ) (weight inv : Fin rank → ZMod M)
    (unit : ∀ i, weight i * inv i = 1) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(fields+fields)*W : ℕ) → dest z = blank)
    (original : Fin (M^(fields+fields)*W) → ZMod 2) :
    let coords := (List.finRange fields).filter (fun i => i.val < rank)
    let read := fun a : Fin coords.length => (⟨(coords.get a).val,
      of_decide_eq_true (List.mem_filter.mp (coords.get_mem a)).2⟩ : Fin rank)
    let k : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).castAdd fields
    let t : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).rev.natAdd fields
    ∀ (capacity : columnCapacity ≤ Q) (signCapacity : ∀ a : Fin coords.length, (fieldSignProgram (n := (fields+d)+1) (k a) true).1 ≤ Q),
    CorrectedScheduleRuns (P := P) (U := U) (d := fields+d) (n := coords.length) (Q := Q) (w := w) (W := W) k t capacity signCapacity inv read
      (fun _ : Fin 1 => (1 : ZMod M)) (fun _ => 0) H J tail rest dest q original
      id
      (fun x => let z := Weighted.child rank (extendLeafWeight weight) (extendLeafWeight inv) (leafFields x); Fin.append (m := fields) (n := fields) z.1 z.2) := by
  intro coords read k t capacity signCapacity
  have lt (a) : k a < t a := by
    change (coords.get a).val < fields + (coords.get a).rev.val
    have := (coords.get a).isLt
    omega
  have run := correctedSchedule_exec (P := P) (U := U) (d := fields+d) (n := coords.length) (Q := Q) (w := w) (W := W) k t lt capacity signCapacity inv read
    (fun a => weight (read a)) (fun a => (mul_comm ..).trans (unit _))
    (fun _ : Fin 1 => (1 : ZMod M)) (fun _ => 0) (fun _ => isUnit_one)
    H J hm hw hW tail rest dest q empty original (fun x => Fin.append (m := fields) (n := fields) (leafFields x).1 (leafFields x).2)
  have units (j : Fin fields) : extendLeafWeight weight j * extendLeafWeight inv j = 1 := by
    by_cases h : j.val < rank <;> simp [extendLeafWeight,h,unit]
  have inRange (a : Fin coords.length) : (coords.get a).val < rank := (read a).isLt
  have act := leafSchedule_action rank (extendLeafWeight weight) (extendLeafWeight inv) units (leafFields (n := fields))
  dsimp only at act
  rw [show (id : (Fin (fields+fields) → ZMod M) → _) =
    (fun x => Fin.append (m := fields) (n := fields) (leafFields x).1 (leafFields x).2) by
      funext x; exact Fin.append_castAdd_natAdd.symm]
  apply (congrArg (fun out => CorrectedScheduleRuns (P := P) (U := U) (d := fields+d) k t
    capacity signCapacity inv read (fun _ : Fin 1 => (1 : ZMod M)) (fun _ => 0) H J tail rest dest q original
    (fun x => Fin.append (m := fields) (n := fields) (leafFields x).1 (leafFields x).2) out) act).mp
  have atCoord (a : Fin coords.length) (f : Fin rank → ZMod M) :
      extendLeafWeight f (coords.get a) = f (read a) := dite_eq_left (inRange a)
  dsimp only [coords] at atCoord
  simpa only [Ring.inverse_one,mul_one,k,t,coords,atCoord,Nat.add_one,Nat.add_succ] using run

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
