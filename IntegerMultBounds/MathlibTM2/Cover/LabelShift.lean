module

public import IntegerMultBounds.MathlibTM2.Cover.LabelView
public import IntegerMultBounds.Machine.RecursiveShiftRoleBank

/-! A label shear on a role tape with the headers of its two-atom view installed. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelShift

open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open LabelView (colView)
open RecursiveShiftRoleBank
open ActualAffineScaling (modulus)

variable {c k s t B : ℕ} {v : Descriptor}

theorem pack_lt {x X y Y : ℕ} (hx : x < X) (hy : y < Y) : x * Y + y < X * Y := by
  nlinarith

/-- Split the label at its control and target atoms. The last field includes all the payload. -/
noncomputable def viewAddress (a row b lp cs mid ct ls h m d after : ℕ)
    (ha : a < v.beforeRows) (hr : row < v.rows) (hb : b < B) (hlp : lp < prime ^ (s*c))
    (hcs : cs < modulus c) (hm : mid < prime ^ ((t-s-1)*c)) (hct : ct < modulus c)
    (hls : ls < prime ^ ((k-1-t)*c)) (hh : h < prime ^ v.width) (hm' : m < v.between)
    (hd : d < prime ^ v.width) (he : after < v.afterD) :
    RecursiveInterchangeScaling.Address (colView prime c k s t B v) :=
  ⟨⟨a, ha⟩, ⟨row, hr⟩, ⟨_, pack_lt hb hlp⟩, ⟨cs, hcs⟩, ⟨mid, hm⟩, ⟨ct, hct⟩,
    ⟨_, pack_lt hls (pack_lt (pack_lt (pack_lt hh hm') hd) he)⟩⟩

/-- Destination on the original tape after the shift machine adds a multiple of the control. -/
theorem shift_index (hv : v.beforeH = B * prime ^ (k*c)) (hst : s < t) (ht : t < k)
    (r : ℚ) (hden : r.den < prime) (a row b lp cs mid ct ls h m d after : ℕ)
    (ha : a < v.beforeRows) (hr : row < v.rows) (hb : b < B) (hlp : lp < prime ^ (s*c))
    (hcs : cs < modulus c) (hm : mid < prime ^ ((t-s-1)*c)) (hct : ct < modulus c)
    (hls : ls < prime ^ ((k-1-t)*c)) (hh : h < prime ^ v.width) (hm' : m < v.between)
    (hd : d < prime ^ v.width) (he : after < v.afterD) :
    let z := viewAddress a row b lp cs mid ct ls h m d after ha hr hb hlp hcs hm hct hls hh hm' hd he
    (RecursiveInterchangeScaling.index (RecursiveInterchangeShift.shiftAddress r z)).val =
      RecursiveInterchangeLayout.index prime v a row
        (b * prime ^ (k*c) + LabelView.label prime c k s t lp cs mid
          ((ct + (IntegerMultBounds.Swap.Modular.ratMod (modulus c) r *
            (cs : ZMod (modulus c))).val) % modulus c) ls) h m d after := by
  dsimp only
  rw [RecursiveInterchangeScaling.index_val, RecursiveInterchangeShift.shiftAddress_d r hden]
  exact LabelView.colView_index prime c k s t B v hv hst ht a row b lp cs mid _ ls h m d after

/-- With the view headers installed, the role-bank program realizes the shear at a cost
linear in the caller's volume. The header and auxiliary tapes survive the call. -/
theorem realizes {n u : ℕ} (hv : v.beforeH = B * prime ^ (k*c)) (hst : s < t) (ht : t < k)
    (hp : v.Positive) (r : ℚ) (wire : Fin n) (roles : Tapes n prime)
    (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (headers : RecursiveDimensionBank.Headers (colView prime c k s t B v) hs)
    (data : Fin (volume prime (colView prime c k s t B v)) → Fin 4)
    (hh : roles.head wire = 0) (htape : roles.tape wire = source data) :
    HoareTime (program (u := u) r wire)
      (fun x => x = CleanSubbank.bank (common roles hs aux))
      (fun x => x = CleanSubbank.bank
        (common (updated roles wire (RecursiveInterchangeShift.array r data)) hs aux))
      (221536 * volume prime v + 32370) := by
  have hq : 0 < prime := by simpa [modulus] using ActualAffineScaling.modulus_pos 1
  obtain ⟨ha, hr, hbefore, hm, he⟩ := hp
  rw [hv] at hbefore
  have hb : 0 < B := Nat.pos_of_ne_zero (by rintro rfl; simp at hbefore)
  have hpos : (colView prime c k s t B v).Positive := by
    refine ⟨ha, hr, Nat.mul_pos hb (pow_pos hq _), pow_pos hq _, ?_⟩
    exact Nat.mul_pos (pow_pos hq _) (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (pow_pos hq _) hm)
      (pow_pos hq _)) he)
  simpa only [LabelView.colView_volume prime c k s t B v hv hst ht] using
    RecursiveShiftRoleBank.realizes r wire roles hs aux data hh htape headers hpos

end IntegerMultBounds.MathlibTM2.Cover.LabelShift
