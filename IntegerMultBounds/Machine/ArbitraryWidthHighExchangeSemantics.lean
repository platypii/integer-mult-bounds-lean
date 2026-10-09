import IntegerMultBounds.Machine.ArbitraryWidthHighLayout
import IntegerMultBounds.Machine.ArbitrarySliceRepeat

/-! Consecutive physical one-digit slice calls exchange exactly the leading
rho digit pairs, at the numeric serialized addresses used by high-row joining. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighExchangeSemantics
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open FlatCoordinateLayout (rank coordinates)
open ArbitraryWidthSliceTranspose (windowAddress)
local instance : NeZero prime := ⟨ne_of_gt Shared50ModularControl.prime_prime.pos⟩

private theorem address_ext {v : Descriptor} {x y : RecursiveInterchangeScaling.Address v}
    (hA : x.beforeRows = y.beforeRows) (hR : x.row = y.row) (hB : x.before = y.before)
    (hH : x.h = y.h) (hC : x.middle = y.middle) (hD : x.d = y.d) (hE : x.after = y.after) : x = y := by
  cases x
  cases y
  cases hA; cases hR; cases hB; cases hH; cases hC; cases hD; cases hE
  rfl

private theorem rank_empty (x : Fin 0 → ZMod prime) : (rank x).val = 0 := by
  have h := (rank x).isLt
  simpa only [pow_zero,Nat.lt_one_iff] using h

theorem prefix_ranks (e r : ℕ) (hr : r ≤ e) (z : Fin (prime^e))
    (h : Fin (prime^r)) (l : Fin (prime^(e-r))) (hz : z.val = h.val*prime^(e-r)+l.val) :
    (rank (ArbitraryWidthSliceTranspose.middle 0 r (by omega) (coordinates z))).val = h.val ∧
    (rank (ArbitraryWidthSliceTranspose.suffix 0 r (by omega) (coordinates z))).val = l.val := by
  have hs := ArbitraryWidthSliceTranspose.rank_split 0 r (by omega : 0+r ≤ e) (coordinates z)
  rw [FlatCoordinateLayout.rank_coordinates,rank_empty] at hs
  simp only [zero_mul,zero_add,Nat.sub_zero] at hs
  have ht := (rank (ArbitraryWidthSliceTranspose.suffix 0 r (by omega) (coordinates z))).isLt
  simp only [Nat.sub_zero] at ht
  have hh : (rank (ArbitraryWidthSliceTranspose.middle 0 r (by omega) (coordinates z))).val = h.val := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn <;> nlinarith [l.isLt]
  constructor
  · exact hh
  · nlinarith

theorem window_original (P e r G B : ℕ) (hr : r ≤ e)
    (a : ArbitraryWidthHighLayout.Coordinate P (prime^r) (prime^(e-r)) G B) :
    windowAddress 0 r (ArbitraryWidthHighLayout.originalAddress P e r G B hr a) =
      ArbitraryWidthHighLayout.originalAddress P e r G B hr (ArbitraryWidthHighLayout.highSwap a) := by
  have hh := prefix_ranks e r hr
    (ArbitraryWidthHighLayout.originalAddress P e r G B hr a).h a.highH a.lowH
    (RecursiveInterchangeRows.pack_val _ _)
  have hd := prefix_ranks e r hr
    (ArbitraryWidthHighLayout.originalAddress P e r G B hr a).d a.highD a.lowD
    (RecursiveInterchangeRows.pack_val _ _)
  have hleft := ArbitraryWidthSliceTranspose.rank_window 0 r (by omega : 0+r ≤ e)
    (coordinates (ArbitraryWidthHighLayout.originalAddress P e r G B hr a).h)
    (coordinates (ArbitraryWidthHighLayout.originalAddress P e r G B hr a).d)
  have hright := ArbitraryWidthSliceTranspose.rank_window_d 0 r (by omega : 0+r ≤ e)
    (coordinates (ArbitraryWidthHighLayout.originalAddress P e r G B hr a).h)
    (coordinates (ArbitraryWidthHighLayout.originalAddress P e r G B hr a).d)
  rw [rank_empty,hd.1,hh.2] at hleft
  rw [rank_empty,hh.1,hd.2] at hright
  simp only [zero_mul,zero_add,Nat.sub_zero] at hleft hright
  apply address_ext <;> try rfl
  · apply Fin.ext
    exact hleft.trans (RecursiveInterchangeRows.pack_val a.highD a.lowH).symm
  · apply Fin.ext
    exact hright.trans (RecursiveInterchangeRows.pack_val a.highH a.lowD).symm

theorem address_window (v : Descriptor) (r : ℕ) (a : RecursiveInterchangeScaling.Address v) :
    ArbitraryWidthSchedule.address (List.replicate r 1) 0 a = windowAddress 0 r a := by
  have hc := ArbitraryWidthSchedule.address_coordinates (List.replicate r 1) 0 a
  have hw : ArbitraryWidthPieces.runWindows (List.replicate r 1) 0
      (fun z => (coordinates a.h z,coordinates a.d z)) =
      ArbitraryWidthPieces.swapWindow 0 r (fun z => (coordinates a.h z,coordinates a.d z)) := by
    funext z
    rw [ArbitraryWidthPieces.runWindows_cell]
    simp [ArbitraryWidthPieces.swapWindow,List.sum_replicate]
  rw [hw] at hc
  have hh := congrArg (fun f => rank (fun z => (f z).1)) hc
  have hd := congrArg (fun f => rank (fun z => (f z).2)) hc
  obtain ⟨hA,hR,hB,hC,hE⟩ := ArbitraryWidthSchedule.address_spectators (List.replicate r 1) 0 a
  apply address_ext (y := windowAddress 0 r a) hA hR hB _ hC _ hE
  · exact (FlatCoordinateLayout.rank_coordinates _).symm.trans hh
  · exact (FlatCoordinateLayout.rank_coordinates _).symm.trans hd

def array {α : Type*} (v : Descriptor) (r : ℕ) (hr : r ≤ v.width)
    (x : Fin (volume prime v) → α) :=
  ArbitraryWidthSchedule.run (List.replicate r 1) 0 (by simpa [List.sum_replicate] using hr) x

theorem repeat_eq (v : Descriptor) (r : ℕ) (hr : r ≤ v.width)
    (x : Fin (volume prime v) → ZMod 2) :
    ArbitrarySliceRepeat.images v 0 1 r (by simpa using hr) x = array v r hr x := rfl

/-- The actual repeated slices have exact highSwap semantics at numeric
addresses, including unchanged low fields and every spectator coordinate. -/
theorem array_highSwap {α : Type*} (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (ArbitraryWidthHighLayout.originalDescriptor P e G B)) → α)
    (a : ArbitraryWidthHighLayout.Coordinate P (prime^r) (prime^(e-r)) G B) :
    array (ArbitraryWidthHighLayout.originalDescriptor P e G B) r hr x
      (ArbitraryWidthHighLayout.originalEquiv prime P e r G B hr a) =
      x (ArbitraryWidthHighLayout.originalEquiv prime P e r G B hr (ArbitraryWidthHighLayout.highSwap a)) := by
  have h := ArbitraryWidthSchedule.run_entry (List.replicate r 1) 0
    (by simpa [List.sum_replicate,ArbitraryWidthHighLayout.originalDescriptor] using hr) x
    (ArbitraryWidthHighLayout.originalAddress P e r G B hr (ArbitraryWidthHighLayout.highSwap a))
  rw [address_window,window_original,ArbitraryWidthHighLayout.highSwap_twice,
    ArbitraryWidthHighLayout.originalAddress_index,ArbitraryWidthHighLayout.originalAddress_index] at h
  exact h

end
end IntegerMultBounds.Machine.ArbitraryWidthHighExchangeSemantics
