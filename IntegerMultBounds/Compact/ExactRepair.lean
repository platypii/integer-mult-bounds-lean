import IntegerMultBounds.Compact.Ideal
import IntegerMultBounds.Compact.Repair

/-! Concrete deterministic exceptional-address repair for the packed program.
The conclusion is unconditional in the input address. Guards decide *where*
repair runs, rather than restricting the correctness theorem's inputs.
Tape implementation and sorting cost are not supplied by this file. -/

namespace IntegerMultBounds.Compact
open Radix

abbrev EarlyAddress (B L : ℤ) (n : ℕ) := Field ((2 * L) ^ n) × Field (B ^ n)

def earlyIdeal (B L : ℤ) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs) :
    Equiv.Perm (EarlyAddress B L zs.length) :=
  Equiv.prodCongr (idealTarget L hL zs hz) (Equiv.refl _)

def earlyGood (B L : ℤ) (n : ℕ) (x : EarlyAddress B L n) : Prop :=
  (∀ v ∈ digits (2 * L) n x.1.val, Guard B L v) ∧
  (∀ w ∈ digits B n x.2.val, w < B - 1)

instance earlyGoodDecidable (B L : ℤ) (n : ℕ) : DecidablePred (earlyGood B L n) :=
  fun x => by unfold earlyGood Guard; infer_instance

theorem earlyIdeal_preserves_good (B L : ℤ) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs)
    (x : EarlyAddress B L zs.length) :
    earlyGood B L zs.length (earlyIdeal B L hL zs hz x) ↔ earlyGood B L zs.length x := by
  change ((∀ v ∈ digits (2 * L) zs.length (idealTarget L hL zs hz x.1).val, Guard B L v) ∧
    (∀ w ∈ digits B zs.length x.2.val, w < B - 1)) ↔ _
  rw [idealTarget_digits, toggleList_guards B L _ zs (digits_length ..) hz]
  rfl

private theorem align_digits (vs ws zs : List ℤ)
    (hw : vs.length = ws.length) (hz : vs.length = zs.length) :
    ∃ ds : List DigitState, ds.map DigitState.v = vs ∧
      ds.map DigitState.w = ws ∧ ds.map DigitState.z = zs := by
  induction vs generalizing ws zs with
  | nil =>
    have hw' : ws = [] := List.length_eq_zero_iff.mp hw.symm
    have hz' : zs = [] := List.length_eq_zero_iff.mp hz.symm
    subst ws; subst zs
    exact ⟨[], rfl, rfl, rfl⟩
  | cons v vs ih =>
    cases ws with
    | nil => simp at hw
    | cons w ws =>
      cases zs with
      | nil => simp at hz
      | cons z zs =>
        obtain ⟨ds, hv, hw', hz'⟩ := ih ws zs (by simpa using hw) (by simpa using hz)
        exact ⟨⟨v, w, z⟩ :: ds, by simp [hv], by simp [hw'], by simp [hz']⟩

private theorem toggleList_projections (ds : List DigitState) :
    toggleList (ds.map DigitState.v) (ds.map DigitState.z) =
      ds.map (fun d => toggle d.v d.z) := by
  induction ds <;> simp_all [toggleList]

theorem early_program_agrees_on_good (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (zs : List ℤ) (hz : Bits zs) (x : EarlyAddress B L zs.length)
    (hx : earlyGood B L zs.length x) :
    packedEarlyPerm (2 * L) B (by omega) (by omega) zs x = earlyIdeal B L hL zs hz x := by
  have hBp : 0 < B := by omega
  have hQp : 0 < 2 * L := by omega
  obtain ⟨ds, hvs, hws, hzs⟩ := align_digits
    (digits (2 * L) zs.length x.1.val) (digits B zs.length x.2.val) zs
    (by simp [digits_length]) (digits_length ..)
  have hgood : ∀ d ∈ ds, d.Good B L := by
    intro d hd
    have hv : d.v ∈ digits (2 * L) zs.length x.1.val := by
      rw [← hvs]; exact List.mem_map_of_mem hd
    have hw : d.w ∈ digits B zs.length x.2.val := by
      rw [← hws]; exact List.mem_map_of_mem hd
    have hzmem : d.z ∈ zs := by rw [← hzs]; exact List.mem_map_of_mem hd
    have hguard := hx.1 d.v hv
    exact ⟨hguard.1, hguard.2, (digits_bounded B hBp _ _ d.w hw).1,
      hx.2 d.w hw, hz d.z hzmem⟩
  have hrun := packedEarly_correct B L hB hL ds hgood
  rw [← toggleList_projections ds, hvs, hws, hzs,
    pack_digits (2 * L) hQp _ _ x.1.property,
    pack_digits B hBp _ _ x.2.property] at hrun
  have hvals := (packedEarlyPerm_agrees (2 * L) B hQp hBp zs x).trans hrun
  apply Prod.ext
  · apply Subtype.ext
    change (packedEarlyPerm (2 * L) B hQp hBp zs x).1.val =
      (idealTarget L hL zs hz x.1).val
    rw [idealTarget_value]
    exact congrArg Prod.fst hvals
  · apply Subtype.ext
    exact congrArg Prod.snd hvals

/-- Repair only exceptional *destinations*, computing the original address by
the true modular inverse. -/
def repairedEarly (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs)
    (x : EarlyAddress B L zs.length) : EarlyAddress B L zs.length :=
  let S := packedEarlyPerm (2 * L) B (by omega) (by omega) zs
  let T := earlyIdeal B L hL zs hz
  let y := S x
  if ¬earlyGood B L zs.length y then T (S.symm y) else y

theorem repairedEarly_correct (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (zs : List ℤ) (hz : Bits zs) (x : EarlyAddress B L zs.length) :
    repairedEarly B L hB hL zs hz x = earlyIdeal B L hL zs hz x := by
  exact repair_exact (packedEarlyPerm (2 * L) B (by omega) (by omega) zs)
    (earlyIdeal B L hL zs hz) (fun y => ¬earlyGood B L zs.length y)
    (fun y => not_congr (earlyIdeal_preserves_good B L hL zs hz y))
    (fun y hy => early_program_agrees_on_good B L hB hL zs hz y (not_not.mp hy)) x

abbrev LateAddress (B L : ℤ) (n : ℕ) := Field (B ^ n) × EarlyAddress B L n

def lateIdeal (B L : ℤ) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs) :
    Equiv.Perm (LateAddress B L zs.length) :=
  Equiv.prodCongr (Equiv.refl _) (earlyIdeal B L hL zs hz)

def lateGood (B L : ℤ) (n : ℕ) (x : LateAddress B L n) : Prop :=
  earlyGood B L n x.2 ∧ (∀ u ∈ digits B n x.1.val, u < B - 1)

instance lateGoodDecidable (B L : ℤ) (n : ℕ) : DecidablePred (lateGood B L n) :=
  fun x => by unfold lateGood; infer_instance

theorem lateIdeal_preserves_good (B L : ℤ) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs)
    (x : LateAddress B L zs.length) :
    lateGood B L zs.length (lateIdeal B L hL zs hz x) ↔ lateGood B L zs.length x := by
  change (earlyGood B L zs.length (earlyIdeal B L hL zs hz x.2) ∧
    (∀ u ∈ digits B zs.length x.1.val, u < B - 1)) ↔ _
  rw [earlyIdeal_preserves_good]
  rfl

private theorem align_late_digits (vs ws us zs : List ℤ)
    (hw : vs.length = ws.length) (hu : vs.length = us.length) (hz : vs.length = zs.length) :
    ∃ ds : List LateDigitState, ds.map LateDigitState.v = vs ∧
      ds.map LateDigitState.w = ws ∧ ds.map LateDigitState.u = us ∧
      ds.map LateDigitState.x = zs := by
  induction vs generalizing ws us zs with
  | nil =>
    have hw' : ws = [] := List.length_eq_zero_iff.mp hw.symm
    have hu' : us = [] := List.length_eq_zero_iff.mp hu.symm
    have hz' : zs = [] := List.length_eq_zero_iff.mp hz.symm
    subst ws; subst us; subst zs
    exact ⟨[], rfl, rfl, rfl, rfl⟩
  | cons v vs ih =>
    cases ws with
    | nil => simp at hw
    | cons w ws =>
      cases us with
      | nil => simp at hu
      | cons u us =>
        cases zs with
        | nil => simp at hz
        | cons z zs =>
          obtain ⟨ds, hv, hw', hu', hz'⟩ := ih ws us zs
            (by simpa using hw) (by simpa using hu) (by simpa using hz)
          exact ⟨⟨v, w, u, z⟩ :: ds, by simp [hv], by simp [hw'], by simp [hu'], by simp [hz']⟩

private theorem toggleList_lateProjections (ds : List LateDigitState) :
    toggleList (ds.map LateDigitState.v) (ds.map LateDigitState.x) =
      ds.map (fun d => toggle d.v d.x) := by
  induction ds <;> simp_all [toggleList]

theorem late_program_agrees_on_good (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (zs : List ℤ) (hz : Bits zs) (x : LateAddress B L zs.length)
    (hx : lateGood B L zs.length x) :
    packedLatePerm (2 * L) B (by omega) (by omega) zs x = lateIdeal B L hL zs hz x := by
  have hBp : 0 < B := by omega
  have hQp : 0 < 2 * L := by omega
  obtain ⟨ds, hvs, hws, hus, hzs⟩ := align_late_digits
    (digits (2 * L) zs.length x.2.1.val) (digits B zs.length x.2.2.val)
    (digits B zs.length x.1.val) zs
    (by simp [digits_length]) (by simp [digits_length]) (digits_length ..)
  have hgood : ∀ d ∈ ds, d.Good B L := by
    intro d hd
    have hv : d.v ∈ digits (2 * L) zs.length x.2.1.val := by
      rw [← hvs]; exact List.mem_map_of_mem hd
    have hw : d.w ∈ digits B zs.length x.2.2.val := by
      rw [← hws]; exact List.mem_map_of_mem hd
    have hu : d.u ∈ digits B zs.length x.1.val := by
      rw [← hus]; exact List.mem_map_of_mem hd
    have hzmem : d.x ∈ zs := by rw [← hzs]; exact List.mem_map_of_mem hd
    have hguard := hx.1.1 d.v hv
    exact ⟨hguard.1, hguard.2, (digits_bounded B hBp _ _ d.w hw).1,
      hx.1.2 d.w hw, (digits_bounded B hBp _ _ d.u hu).1, hx.2 d.u hu, hz d.x hzmem⟩
  have hrun := packedLate_correct B L hB hL ds hgood
  rw [← toggleList_lateProjections ds, hvs, hws, hus, hzs,
    pack_digits (2 * L) hQp _ _ x.2.1.property,
    pack_digits B hBp _ _ x.2.2.property,
    pack_digits B hBp _ _ x.1.property] at hrun
  have hvals := (packedLatePerm_agrees (2 * L) B hQp hBp zs x).trans hrun
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : ℤ × ℤ × ℤ => z.2.2) hvals
  · apply Prod.ext
    · apply Subtype.ext
      change (packedLatePerm (2 * L) B hQp hBp zs x).2.1.val =
        (idealTarget L hL zs hz x.2.1).val
      rw [idealTarget_value]
      exact congrArg Prod.fst hvals
    · apply Subtype.ext
      exact congrArg (fun z : ℤ × ℤ × ℤ => z.2.1) hvals

def repairedLate (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) (zs : List ℤ) (hz : Bits zs)
    (x : LateAddress B L zs.length) : LateAddress B L zs.length :=
  let S := packedLatePerm (2 * L) B (by omega) (by omega) zs
  let T := lateIdeal B L hL zs hz
  let y := S x
  if ¬lateGood B L zs.length y then T (S.symm y) else y

/-- All source bit patterns and all addresses, including arbitrary overflowing
temporary digits: repair recovers the ideal selected-parity operation. -/
theorem repairedLate_correct (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (zs : List ℤ) (hz : Bits zs) (x : LateAddress B L zs.length) :
    repairedLate B L hB hL zs hz x = lateIdeal B L hL zs hz x := by
  exact repair_exact (packedLatePerm (2 * L) B (by omega) (by omega) zs)
    (lateIdeal B L hL zs hz) (fun y => ¬lateGood B L zs.length y)
    (fun y => not_congr (lateIdeal_preserves_good B L hL zs hz y))
    (fun y hy => late_program_agrees_on_good B L hB hL zs hz y (not_not.mp hy)) x

end IntegerMultBounds.Compact
