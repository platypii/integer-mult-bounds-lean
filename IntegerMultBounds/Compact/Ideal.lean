import IntegerMultBounds.Compact.Permutations

/-! The ideal selected-parity permutation on every packed address, with no
guard restriction. This is the destination map used in exceptional repair. -/

namespace IntegerMultBounds.Compact
open Radix

abbrev DigitBlock (B : ℤ) (n : ℕ) := {xs : List ℤ // xs.length = n ∧ Bounded B xs}

def radixEquiv (B : ℤ) (hB : 0 < B) (n : ℕ) : DigitBlock B n ≃ Field (B ^ n) where
  toFun := fun xs => ⟨pack B xs.val, by
    have h := pack_bounds B hB xs.val xs.property.2
    simpa [xs.property.1] using h⟩
  invFun := fun x => ⟨digits B n x.val, digits_length B n x.val, digits_bounded B hB n x.val⟩
  left_inv := fun xs => by
    apply Subtype.ext
    change digits B n (pack B xs.val) = xs.val
    simpa only [xs.property.1] using digits_pack B hB xs.val xs.property.2
  right_inv := fun x => by
    apply Subtype.ext
    exact pack_digits B hB n x.val x.property

def Bits (zs : List ℤ) : Prop := ∀ z ∈ zs, z = 0 ∨ z = 1

def toggleList (vs zs : List ℤ) : List ℤ := List.zipWith toggle vs zs

theorem toggleList_length (vs zs : List ℤ) (hlen : vs.length = zs.length) :
    (toggleList vs zs).length = vs.length := by simp [toggleList, hlen]

theorem toggle_bounded (L v z : ℤ) (hv : 0 ≤ v ∧ v < 2 * L) (hz : z = 0 ∨ z = 1) :
    0 ≤ toggle v z ∧ toggle v z < 2 * L := by
  rcases hz with rfl | rfl <;> dsimp [toggle] <;> omega

theorem toggleList_bounded (L : ℤ) (vs zs : List ℤ) (hv : Bounded (2 * L) vs)
    (hz : Bits zs) : Bounded (2 * L) (toggleList vs zs) := by
  induction vs generalizing zs with
  | nil => simp [toggleList, Bounded]
  | cons v vs ih =>
    cases zs with
    | nil => simp [toggleList, Bounded]
    | cons z zs =>
      obtain ⟨hv₀, hvs⟩ := (bounded_cons _ _ _).mp hv
      change Bounded (2 * L) (toggle v z :: toggleList vs zs)
      rw [bounded_cons]
      exact ⟨toggle_bounded L v z hv₀ (hz z (by simp)),
        ih zs hvs (fun z hz' => hz z (by simp [hz']))⟩

theorem toggleList_twice (vs zs : List ℤ) (hlen : vs.length = zs.length) (hz : Bits zs) :
    toggleList (toggleList vs zs) zs = vs := by
  induction vs generalizing zs with
  | nil => simp [toggleList]
  | cons v vs ih =>
    cases zs with
    | nil => simp at hlen
    | cons z zs =>
      change toggle (toggle v z) z :: toggleList (toggleList vs zs) zs = v :: vs
      rw [toggle_twice v z (hz z (by simp)),
        ih zs (by simpa using hlen) (fun z hz' => hz z (by simp [hz']))]

def digitToggle (L : ℤ) (zs : List ℤ) (hz : Bits zs) :
    Equiv.Perm (DigitBlock (2 * L) zs.length) where
  toFun := fun vs => ⟨toggleList vs.val zs,
    (toggleList_length _ _ vs.property.1).trans vs.property.1,
    toggleList_bounded L _ _ vs.property.2 hz⟩
  invFun := fun vs => ⟨toggleList vs.val zs,
    (toggleList_length _ _ vs.property.1).trans vs.property.1,
    toggleList_bounded L _ _ vs.property.2 hz⟩
  left_inv := fun vs => Subtype.ext (toggleList_twice _ _ vs.property.1 hz)
  right_inv := fun vs => Subtype.ext (toggleList_twice _ _ vs.property.1 hz)

def idealTarget (L : ℤ) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs) :
    Equiv.Perm (Field ((2 * L) ^ zs.length)) :=
  (radixEquiv (2 * L) (by omega) zs.length).symm.trans
    ((digitToggle L zs hz).trans (radixEquiv (2 * L) (by omega) zs.length))

theorem idealTarget_value (L : ℤ) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs)
    (x : Field ((2 * L) ^ zs.length)) :
    (idealTarget L hL zs hz x).val =
      pack (2 * L) (toggleList (digits (2 * L) zs.length x.val) zs) := rfl

theorem idealTarget_digits (L : ℤ) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs)
    (x : Field ((2 * L) ^ zs.length)) :
    digits (2 * L) zs.length (idealTarget L hL zs hz x).val =
      toggleList (digits (2 * L) zs.length x.val) zs := by
  rw [idealTarget_value]
  have hl := toggleList_length (digits (2 * L) zs.length x.val) zs (digits_length ..)
  rw [digits_length] at hl
  simpa only [hl] using digits_pack (2 * L) (by omega)
    (toggleList (digits (2 * L) zs.length x.val) zs)
    (toggleList_bounded L _ zs (digits_bounded (2 * L) (by omega) zs.length x.val) hz)

def Guard (B L v : ℤ) : Prop := 2 * B ≤ v / 2 ∧ v / 2 < L - 2 * B

theorem toggle_guard_iff (B L v z : ℤ) (hz : z = 0 ∨ z = 1) :
    Guard B L (toggle v z) ↔ Guard B L v := by
  unfold Guard
  rw [toggle_guard v z hz]

theorem toggleList_guards (B L : ℤ) (vs zs : List ℤ)
    (hlen : vs.length = zs.length) (hz : Bits zs) :
    (∀ v ∈ toggleList vs zs, Guard B L v) ↔ (∀ v ∈ vs, Guard B L v) := by
  induction vs generalizing zs with
  | nil => simp [toggleList]
  | cons v vs ih =>
    cases zs with
    | nil => simp at hlen
    | cons z zs =>
      change (∀ a ∈ toggle v z :: toggleList vs zs, Guard B L a) ↔
        (∀ a ∈ v :: vs, Guard B L a)
      simp only [List.forall_mem_cons, toggle_guard_iff B L v z (hz z (by simp)),
        ih zs (by simpa using hlen) (fun z hz' => hz z (by simp [hz']))]

end IntegerMultBounds.Compact
