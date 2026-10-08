import IntegerMultBounds.Compact.DirtyControl
import IntegerMultBounds.Compact.Radix

/-!
A packed implementation of the earlier-source four-update gadget. Every field
update is one modular addition on an entire packed integer; digits used by an
offset are decoded from the *current* packed field. The theorem proves exact
restoration and selected-parity toggling for every length on the guarded set.

This is address arithmetic. Realizing the loads by front/back swaps and
accounting for their tape costs are additional tasks.
-/

namespace IntegerMultBounds.Compact
open Radix

structure DigitState where
  v : ℤ
  w : ℤ
  z : ℤ

namespace DigitState

def v₁ (d : DigitState) : ℤ := d.v + 2 * d.z * d.w
def w₁ (d : DigitState) : ℤ := d.w + d.v₁ % 2
def v₂ (d : DigitState) : ℤ := d.v₁ + d.z * (1 - 2 * d.w₁)
def w₂ (d : DigitState) : ℤ := d.w₁ - ((d.v₂ % 2 + d.z) % 2)

def Good (B L : ℤ) (d : DigitState) : Prop :=
  2 * B ≤ d.v / 2 ∧ d.v / 2 < L - 2 * B ∧
  0 ≤ d.w ∧ d.w < B - 1 ∧ (d.z = 0 ∨ d.z = 1)

theorem bounds (B L : ℤ) (hB : 1 ≤ B) (d : DigitState) (h : d.Good B L) :
    (0 ≤ d.v₁ ∧ d.v₁ < 2 * L) ∧ (0 ≤ d.w₁ ∧ d.w₁ < B) ∧
    (0 ≤ d.v₂ ∧ d.v₂ < 2 * L) := by
  obtain ⟨hg₀, hg₁, hw₀, hw₁, hz⟩ := h
  have ha : d.v % 2 = 0 ∨ d.v % 2 = 1 := by omega
  have hv : 2 * (d.v / 2) + d.v % 2 = d.v := by omega
  have hh := guarded_updates B L (d.v / 2) (d.v % 2) d.w d.z
    hB hg₀ hg₁ ha hw₀ hw₁ hz
  dsimp only at hh
  rw [hv] at hh
  exact ⟨⟨hh.1, hh.2.1⟩, ⟨hh.2.2.1, hh.2.2.2.1⟩, hh.2.2.2.2⟩

theorem restored (d : DigitState) (hz : d.z = 0 ∨ d.z = 1) : d.w₂ = d.w := by
  exact congrArg Prod.snd (fourUpdate_eq d.v d.w d.z hz)

theorem toggled (d : DigitState) (hz : d.z = 0 ∨ d.z = 1) :
    d.v₂ = toggle d.v d.z := by
  exact congrArg Prod.fst (fourUpdate_eq d.v d.w d.z hz)

end DigitState

/-- A direct packed arithmetic program. It recomputes every offset from the
current target and temporary values; it does not use an ideal-map oracle. -/
def packedEarly (Q B : ℤ) (controls : List ℤ) (target temp : ℤ) : ℤ × ℤ :=
  let n := controls.length
  let v₁ := (target + pack Q
    (List.zipWith (fun z w => 2 * z * w) controls (digits B n temp))) % Q ^ n
  let w₁ := (temp + pack B ((digits Q n v₁).map (· % 2))) % B ^ n
  let v₂ := (v₁ + pack Q
    (List.zipWith (fun z w => z * (1 - 2 * w)) controls (digits B n w₁))) % Q ^ n
  let w₂ := (w₁ - pack B
    (List.zipWith (fun v z => (v % 2 + z) % 2) (digits Q n v₂) controls)) % B ^ n
  (v₂, w₂)

private theorem zip_maps {α β γ δ : Type*} (f : β → γ → δ)
    (g : α → β) (h : α → γ) (xs : List α) :
    List.zipWith f (xs.map g) (xs.map h) = xs.map (fun x => f (g x) (h x)) := by
  induction xs <;> simp_all

private theorem mapped_bounded {α : Type*} (B : ℤ) (xs : List α) (f : α → ℤ)
    (h : ∀ x ∈ xs, 0 ≤ f x ∧ f x < B) : Bounded B (xs.map f) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact h x hx

private theorem pack_map_add {α : Type*} (B : ℤ) (xs : List α) (f g : α → ℤ) :
    pack B (xs.map f) + pack B (xs.map g) = pack B (xs.map (fun x => f x + g x)) := by
  rw [← pack_add B _ _ (by simp), zip_maps]

private theorem pack_map_sub {α : Type*} (B : ℤ) (xs : List α) (f g : α → ℤ) :
    pack B (xs.map f) - pack B (xs.map g) = pack B (xs.map (fun x => f x - g x)) := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih => simp only [List.map_cons, pack]; linear_combination B * ih

/-- Arbitrarily many packed digits, arbitrary dirty temporaries in the good
range, exact modular arithmetic, and no omitted carry assumptions. -/
theorem packedEarly_correct (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (ds : List DigitState) (hgood : ∀ d ∈ ds, d.Good B L) :
    packedEarly (2 * L) B (ds.map DigitState.z)
      (pack (2 * L) (ds.map DigitState.v)) (pack B (ds.map DigitState.w)) =
    (pack (2 * L) (ds.map (fun d => toggle d.v d.z)), pack B (ds.map DigitState.w)) := by
  have hBp : 0 < B := by omega
  have hQp : 0 < 2 * L := by omega
  have hw : Bounded B (ds.map DigitState.w) := mapped_bounded _ _ _ (by
    intro d hd
    have h := hgood d hd
    exact ⟨h.2.2.1, lt_trans h.2.2.2.1 (by omega)⟩)
  have hv₁ : Bounded (2 * L) (ds.map DigitState.v₁) := mapped_bounded _ _ _ (by
    intro d hd; exact (d.bounds B L hB (hgood d hd)).1)
  have hw₁ : Bounded B (ds.map DigitState.w₁) := mapped_bounded _ _ _ (by
    intro d hd; exact (d.bounds B L hB (hgood d hd)).2.1)
  have hv₂ : Bounded (2 * L) (ds.map DigitState.v₂) := mapped_bounded _ _ _ (by
    intro d hd; exact (d.bounds B L hB (hgood d hd)).2.2)
  have mod_pack (R : ℤ) (hR : 0 < R) (f : DigitState → ℤ)
      (hf : Bounded R (ds.map f)) :
      pack R (ds.map f) % R ^ ds.length = pack R (ds.map f) := by
    have hp := pack_bounds R hR _ hf
    simpa using Int.emod_eq_of_lt hp.1 hp.2
  have dec_pack (R : ℤ) (hR : 0 < R) (f : DigitState → ℤ)
      (hf : Bounded R (ds.map f)) :
      digits R ds.length (pack R (ds.map f)) = ds.map f := by
    simpa using digits_pack R hR (ds.map f) hf
  have hvmap : ds.map DigitState.v₂ = ds.map (fun d => toggle d.v d.z) := by
    apply List.map_congr_left
    intro d hd
    exact d.toggled (hgood d hd).2.2.2.2
  have hwmap : ds.map DigitState.w₂ = ds.map DigitState.w := by
    apply List.map_congr_left
    intro d hd
    exact d.restored (hgood d hd).2.2.2.2
  have ev₁ (d : DigitState) : d.v + 2 * d.z * d.w = d.v₁ := rfl
  have ew₁ (d : DigitState) : d.w + d.v₁ % 2 = d.w₁ := rfl
  have ev₂ (d : DigitState) : d.v₁ + d.z * (1 - 2 * d.w₁) = d.v₂ := rfl
  have ew₂ (d : DigitState) : d.w₁ - ((d.v₂ % 2 + d.z) % 2) = d.w₂ := rfl
  unfold packedEarly
  simp only [List.length_map, dec_pack B hBp _ hw, zip_maps, pack_map_add,
    ev₁, mod_pack (2 * L) hQp _ hv₁, dec_pack (2 * L) hQp _ hv₁,
    List.map_map, Function.comp_def, ew₁, mod_pack B hBp _ hw₁,
    dec_pack B hBp _ hw₁, ev₂, mod_pack (2 * L) hQp _ hv₂,
    dec_pack (2 * L) hQp _ hv₂, pack_map_sub, ew₂, hwmap,
    mod_pack B hBp _ hw]
  rw [hvmap]

structure LateDigitState where
  v : ℤ
  w : ℤ
  u : ℤ
  x : ℤ

namespace LateDigitState

def first (d : LateDigitState) : DigitState := ⟨d.v, d.w, d.u % 2⟩
def second (d : LateDigitState) : DigitState :=
  ⟨toggle d.v (d.u % 2), d.w, (d.u + d.x) % 2⟩

def Good (B L : ℤ) (d : LateDigitState) : Prop :=
  2 * B ≤ d.v / 2 ∧ d.v / 2 < L - 2 * B ∧
  0 ≤ d.w ∧ d.w < B - 1 ∧ 0 ≤ d.u ∧ d.u < B - 1 ∧
  (d.x = 0 ∨ d.x = 1)

theorem first_good (B L : ℤ) (d : LateDigitState) (h : d.Good B L) :
    d.first.Good B L :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by dsimp [first]; omega⟩

theorem second_good (B L : ℤ) (d : LateDigitState) (h : d.Good B L) :
    d.second.Good B L := by
  have hz : d.u % 2 = 0 ∨ d.u % 2 = 1 := by omega
  dsimp [second, DigitState.Good]
  rw [toggle_guard d.v (d.u % 2) hz]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by omega⟩

end LateDigitState

def packedLate (Q B : ℤ) (source : List ℤ) (target temp control : ℤ) : ℤ × ℤ × ℤ :=
  let n := source.length
  let first := packedEarly Q B ((digits B n control).map (· % 2)) target temp
  let loaded := (control + pack B source) % B ^ n
  let second := packedEarly Q B ((digits B n loaded).map (· % 2)) first.1 first.2
  let restored := (loaded - pack B source) % B ^ n
  (second.1, second.2, restored)

/-- Two early gadgets and a dirty load/unload implement the later-source map
for every number of packed digits, restoring both front temporary fields. -/
theorem packedLate_correct (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (ds : List LateDigitState) (hgood : ∀ d ∈ ds, d.Good B L) :
    packedLate (2 * L) B (ds.map LateDigitState.x)
      (pack (2 * L) (ds.map LateDigitState.v))
      (pack B (ds.map LateDigitState.w)) (pack B (ds.map LateDigitState.u)) =
    (pack (2 * L) (ds.map (fun d => toggle d.v d.x)),
      pack B (ds.map LateDigitState.w), pack B (ds.map LateDigitState.u)) := by
  have hBp : 0 < B := by omega
  have hu : Bounded B (ds.map LateDigitState.u) := mapped_bounded _ _ _ (by
    intro d hd
    have h := hgood d hd
    exact ⟨h.2.2.2.2.1, lt_trans h.2.2.2.2.2.1 (by omega)⟩)
  have huload : Bounded B (ds.map (fun d => d.u + d.x)) := mapped_bounded _ _ _ (by
    intro d hd
    obtain ⟨_, _, _, _, hu₀, hu₁, hx⟩ := hgood d hd
    rcases hx with hx | hx <;> rw [hx] <;> omega)
  have mod_pack (f : LateDigitState → ℤ) (hf : Bounded B (ds.map f)) :
      pack B (ds.map f) % B ^ ds.length = pack B (ds.map f) := by
    have hp := pack_bounds B hBp _ hf
    simpa using Int.emod_eq_of_lt hp.1 hp.2
  have dec_pack (f : LateDigitState → ℤ) (hf : Bounded B (ds.map f)) :
      digits B ds.length (pack B (ds.map f)) = ds.map f := by
    simpa using digits_pack B hBp (ds.map f) hf
  have hfirst := packedEarly_correct B L hB hL (ds.map LateDigitState.first) (by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact d.first_good B L (hgood d hd))
  have hsecond := packedEarly_correct B L hB hL (ds.map LateDigitState.second) (by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact d.second_good B L (hgood d hd))
  simp only [List.map_map, Function.comp_def, LateDigitState.first] at hfirst
  simp only [List.map_map, Function.comp_def, LateDigitState.second] at hsecond
  have htoggle : ds.map (fun d => toggle (toggle d.v (d.u % 2)) ((d.u + d.x) % 2)) =
      ds.map (fun d => toggle d.v d.x) := by
    apply List.map_congr_left
    intro d hd
    exact later_source d.v d.u d.x (hgood d hd).2.2.2.2.2.2
  unfold packedLate
  simp only [List.length_map, dec_pack _ hu, List.map_map, Function.comp_def,
    pack_map_add, mod_pack _ huload, dec_pack _ huload, hfirst, hsecond,
    pack_map_sub, add_sub_cancel_right, mod_pack _ hu, htoggle]

end IntegerMultBounds.Compact
