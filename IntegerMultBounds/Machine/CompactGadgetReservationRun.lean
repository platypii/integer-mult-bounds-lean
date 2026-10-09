import IntegerMultBounds.Machine.CompactGadgetReservationData
import IntegerMultBounds.Machine.BinaryPackedOffsetOriginalRun
import IntegerMultBounds.Machine.PlacementBank

/-! Actual compact-front/back load on each physically reserved role stream.
The original shape headers and packed offset word remain explicit physical
inputs. No header installer or offset computation is assumed by this module. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationRun
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open CompactGadgetReservationData
open BinaryPackedFieldSwap (store)
open BinaryPackedOffsetOriginalRun (headers input cost)
variable {c r : ℕ}

def output (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front) (hc : 0 < c)
    (x : Fin (1*r*s.recordWidth) → Bool) (j : Fin c) (V : List Bool) :=
  BinaryPackedOffsetData.result V (s.prefixRange (rowCount r c) f) (s.width n)
    (s.gap n f) (s.suffix n) (rectangle (a := prime) s n hn f hc x j)

theorem caller_store (caller : Tapes 6 prime) (s : Shape) (n : ℕ) (hn : n ≤ s.axes)
    (f : Front) (hc : 0 < c) (x : Fin (1*r*s.recordWidth) → Bool) (rs ls : List Bool)
    (j : Fin c)
    (ht : caller.tape 5 = (CompactRowReservationEndpoint.final (a := prime) hc x rs ls).tape (roleSlot c j))
    (hh : caller.head 5 = 0) :
    store caller 5 (rectangle (a := prime) s n hn f hc x j) = caller := by
  have hw := (role_tape (a := prime) s n hn f hc x rs ls j).2
  rw [hw] at ht
  apply congrArg₂ Tapes.mk <;> funext i
  · change Function.update caller.head 5 0 i = caller.head i
    by_cases hi : i = 5
    · subst i
      rw [Function.update_self]
      exact hh.symm
    · exact Function.update_of_ne hi _ _
  · change Function.update caller.tape 5 _ i = caller.tape i
    by_cases hi : i = 5
    · subst i
      rw [Function.update_self]
      exact ht.symm
    · exact Function.update_of_ne hi _ _

/-- Literal fixed-machine temp/back or control/back action, beginning with
the exact word supplied by complete-row reservation. Other original tapes,
all heads and every private tape are restored by the actual run. -/
theorem runs (caller : Tapes 6 prime) (s : Shape) (n : ℕ) (hn : n ≤ s.axes)
    (f : Front) (hc : 0 < c) (x : Fin (1*r*s.recordWidth) → Bool) (rs ls : List Bool)
    (j : Fin c) (hrows : 0 < rowCount r c) (hp : 0 < s.payload)
    (V : List Bool)
    (hV : V.length = BinaryPackedOffsetData.rows (s.prefixRange (rowCount r c) f)
      (s.width n) (s.gap n f)*s.width n)
    (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values
      (s.prefixRange (rowCount r c) f) (s.gap n f) (s.suffix n) (s.width n) i)
    (hcH : ∀ i, GrowingCounterData.Canonical (hs i))
    (hsrc : BinaryAdjacentWidthHeadersShared.Sources caller headers hs)
    (htV : caller.tape 4 = putWord (StreamedFiberTranslationAlphabet.mapTape (fun _ => blank))
      0 (V.map bitSymbol)) (hhV : caller.head 4 = 0)
    (ht : caller.tape 5 = (CompactRowReservationEndpoint.final (a := prime) hc x rs ls).tape (roleSlot c j))
    (hh : caller.head 5 = 0) :
    HoareTime BinaryPackedOffsetOriginalRun.program (fun v => v = BinaryPackedOffsetOriginalRun.input caller)
      (fun v => v = BinaryPackedOffsetOriginalRun.input (store caller 5 (output s n hn f hc x j V)))
      (cost (s.prefixRange (rowCount r c) f) (s.width n) (s.gap n f) (s.suffix n) hs) := by
  have hr := BinaryPackedOffsetOriginalRun.runs caller V
    (s.prefixRange (rowCount r c) f) (s.width n) (s.gap n f) (s.suffix n) hV
    (s.prefix_pos _ _ hrows) (s.gap_pos n f) (s.suffix_pos n hp)
    hs hv hcH hsrc (fun _ => blank) 0 rfl htV hhV
    (rectangle (a := prime) s n hn f hc x j)
  rw [caller_store caller s n hn f hc x rs ls j ht hh] at hr
  exact hr

/-- Every prefix/unused front coordinate, active middle coordinate, original
dirty back coordinate, unused back coordinate and payload bit is retained.
Only the selected compact front field moves by the physically read offset. -/
theorem output_entry (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front) (hc : 0 < c)
    (x : Fin (1*r*s.recordWidth) → Bool) (j : Fin c) (V : List Bool)
    (hV : V.length = BinaryPackedOffsetData.rows (s.prefixRange (rowCount r c) f)
      (s.width n) (s.gap n f)*s.width n)
    (p : Fin (s.prefixRange (rowCount r c) f)) (front back : Fin (2^(s.width n)))
    (g : Fin (s.gap n f)) (b : Fin (s.suffix n)) :
    output s n hn f hc x j V (RadixRangePadding.index p
      ⟨(front.val+PackedOffsetPayloadValue.offset V (s.width n)
        (BinaryPackedOffsetData.rowIndex p back g).val)%2^(s.width n),
        Nat.mod_lt _ (by positivity)⟩ g back b) =
      rectangle (a := prime) s n hn f hc x j (RadixRangePadding.index p front g back b) :=
  BinaryPackedOffsetData.result_entry V _ _ _ _ hV _ p front back g b

/-- Placement preserves the entire complementary bank, including all other
physical roles. The active-bank premise explicitly accounts for original
shape/offset inputs and blank private work areas. -/
theorem placed {t u : ℕ}
    (e : Fin (((6+9)+BinaryPackedOffsetOriginalRun.count+12)+u) ≃ Fin t)
    (caller : Tapes t prime) (before after : Tapes 6 prime) (C : ℕ)
    (ha : Placement.active e caller = BinaryPackedOffsetOriginalRun.input before)
    (hr : HoareTime BinaryPackedOffsetOriginalRun.program
      (fun v => v = BinaryPackedOffsetOriginalRun.input before) (fun v => v = BinaryPackedOffsetOriginalRun.input after) C) :
    HoareTime (Placement.placed BinaryPackedOffsetOriginalRun.program e)
      (fun v => v = caller)
      (fun v => v = Placement.replace e caller (BinaryPackedOffsetOriginalRun.input after) ∧
        Placement.extra e v = Placement.extra e caller) C := by
  have h := Placement.hoare_at hr e caller ha
  refine h.consequence (fun _ h => h) ?_ (le_refl _)
  rintro v ⟨small,rfl,rfl⟩
  exact ⟨rfl,Placement.extra_replace _ _ _⟩

end
end IntegerMultBounds.Machine.CompactGadgetReservationRun
