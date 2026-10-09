import IntegerMultBounds.Machine.BinaryVaryingControlOffsetGather
import IntegerMultBounds.Machine.BinaryVaryingSelectedOffsetData
import IntegerMultBounds.Compact.ToggleValue

/-! Literal varying control masks for the third early load. Combined with
the varying selected offsets, these are the two physical inputs to the
existing rowwise modular subtraction machine. -/
namespace IntegerMultBounds.Machine.BinaryVaryingControlOffsetData
open BinaryVaryingSelectedOffsetData (stream)

theorem word_eq (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) :
    BinaryVaryingControlOffsetGather.word q b hb hbq xs zs=Compact.PowerTwo.toggleMask q zs :=
  Compact.PowerTwo.gather_controls q b hb hbq xs zs

theorem mask_stream (q N : ℕ) (Z : ℕ → List Bool) :
    Compact.PowerTwo.toggleMask q (stream N Z)=
      stream N (fun i => Compact.PowerTwo.toggleMask q (Z i)) := by
  simp [Compact.PowerTwo.toggleMask,stream,List.flatten_flatten,Function.comp_def]

theorem stream_field (N w i : ℕ) (Z : ℕ → List Bool)
    (hz : ∀ k<N, (Z k).length=w) (hi : i<N) :
    Gather.field (stream N Z) (i*w) w=Z i := by
  apply List.ext_getElem
  · simp [hz i hi]
  · intro j hj hj'
    have hjw : j<w := by simpa using hj
    have h := BinaryVaryingSelectedOffsetData.stream_entry N w Z hz i j hi hjw
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some] at h
    simpa only [Gather.field,List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD] using h

/-- Every physical row is exactly the mask of that row's varying controls. -/
theorem field_eq (q b n N i : ℕ) (xs : List Bool) (Z : ℕ → List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hz : ∀ k<N, (Z k).length=n) (hi : i<N) :
    Gather.field (BinaryVaryingControlOffsetGather.word q b hb hbq xs (stream N Z))
      (i*(n*q)) (n*q)=Compact.PowerTwo.toggleMask q (Z i) := by
  rw [word_eq,mask_stream]
  exact stream_field N (n*q) i _
    (by intro k hk; rw [Compact.PowerTwo.toggleMask_length q (by omega),hz k hk]) hi

theorem field_value (q b n N i : ℕ) (xs : List Bool) (Z : ℕ → List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hz : ∀ k<N, (Z k).length=n) (hi : i<N) :
    (Counter.value (Gather.field (BinaryVaryingControlOffsetGather.word q b hb hbq xs (stream N Z))
      (i*(n*q)) (n*q)) : ℤ)=Compact.Radix.pack ((2 : ℤ)^q) ((Z i).map Compact.PowerTwo.ctrl) := by
  rw [field_eq q b n N i xs Z hb hbq hz hi]
  rw [← Compact.PowerTwo.gather_controls q b hb hbq (Z i) (Z i)]
  exact Compact.PowerTwo.controls_value q b hb hbq (Z i) (Z i) le_rfl

end IntegerMultBounds.Machine.BinaryVaryingControlOffsetData
