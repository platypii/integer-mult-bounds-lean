import IntegerMultBounds.Machine.FlatCoordinateLayout
import IntegerMultBounds.Machine.FlatAffineScalingArray

/-! Actual initialized affine scaling on the common ordered-coordinate layout.
The returned source is a canonical array with the common physical volume. -/
namespace IntegerMultBounds.Machine.FlatCoordinateScaling
open Networks
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
noncomputable section
variable {d b W : ℕ}
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

def array {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin ((modulus b)^d*W) → Fin 4) (t : Fin d) : Fin ((modulus b)^d*W) → Fin 4 :=
  fun i => FlatAffineScalingArray.array hr (fiberView a t) (Fin.cast (split_volume t) i)

theorem array_word {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin ((modulus b)^d*W) → Fin 4) (t : Fin d) :
    List.ofFn (array hr a t) = List.ofFn (FlatAffineScalingArray.array hr (fiberView a t)) :=
  (List.ofFn_congr (split_volume t).symm _).symm

/-- The concrete returned array transports every coordinate and suffix symbol
according to the ordered-affine scaling operation. -/
theorem array_entry {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin ((modulus b)^d*W) → Fin 4) (t : Fin d)
    (x : Fin d → ZMod (modulus b)) (j : Fin W) :
    array hr a t (index (OrderedAffine.execute (.scale t (Swap.Modular.ratMod (modulus b) r)) x) j) =
      a (index x j) := by
  have hh := FlatAffineScalingArray.array_entry hr (fiberView a t)
    ⟨prefixIndex x t,prefix_lt x t⟩ ⟨(x t).val,ZMod.val_lt _⟩ ⟨suffix x t j,suffix_lt x t j⟩
  rw [fiberView_index] at hh
  unfold array
  convert hh using 1
  congr 1
  apply Fin.ext
  simp only [Fin.val_cast,scale_destination,FiberLayoutData.index_val,
    FlatAffineScalingArray.coordinate,ZMod.natCast_zmod_val]

theorem output_source {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin ((modulus b)^d*W) → Fin 4) (t : Fin d)
    (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :
    (FlatAffineScalingReady.output hr (fiberView a t) bs qs ns source dest).tape
      (FlatAffineScaling.sourceSlot r) = putWord source 0 (List.ofFn (array hr a t)) := by
  rw [FlatAffineScalingArray.output_source,array_word]

/-- The ready physical machine realizes this common-coordinate array, with
its concrete runtime and original source/destination origins restored. -/
theorem realizes_hoare {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin ((modulus b)^d*W) → Fin 4) (t : Fin d) (hW : 0 < W)
    (bs qs ns : List Bool) (hb : Counter.value bs = suffixSize (Q := modulus b) (W := W) t)
    (hq : Counter.value qs = modulus b) (hn : Counter.value ns = prefixSize (Q := modulus b) t)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (source dest : ℤ → Fin 4)
    (hdblank : ∀ z, 0 ≤ z → z < (((modulus b)^d*W : ℕ) : ℤ) → dest z = blank) :
    HoareTime (FlatAffineScalingReady.program hr)
      (fun v => v = FlatAffineScalingReady.input hr (fiberView a t) bs qs ns source dest)
      (fun v => v = FlatAffineScalingReady.output hr (fiberView a t) bs qs ns source dest ∧
        v.tape (FlatAffineScaling.sourceSlot r) = putWord source 0 (List.ofFn (array hr a t)) ∧
        ∀ (x : Fin d → ZMod (modulus b)) (j : Fin W),
          array hr a t (index (OrderedAffine.execute (.scale t (Swap.Modular.ratMod (modulus b) r)) x) j) =
            a (index x j))
      ((2064+120*(r.num.natAbs+r.den))*((modulus b)^d*W)+254) := by
  have hs := FlatAffineScalingReady.realizes_hoare hr (fiberView a t)
    (Nat.mul_pos (pow_pos (ActualAffineScaling.modulus_pos b) _) hW)
    (pow_pos (ActualAffineScaling.modulus_pos b) _) bs qs ns hb hq hn cb cq cn source dest
    (by simpa only [← split_volume t] using hdblank)
  apply hs.consequence (fun _ h => h) ?_ ?_
  · intro v hv
    rcases hv with ⟨rfl,_⟩
    exact ⟨rfl,output_source hr a t bs qs ns source dest,array_entry hr a t⟩
  · rw [split_volume t]

end
end IntegerMultBounds.Machine.FlatCoordinateScaling
