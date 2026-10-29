module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedEncodedStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDecode

/-! Interpret a local word list in its original ambient coordinates. This is a
semantic field; its representation remains the local list, with no ambient tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedField {s : ℕ} (a : ℕ) (xs : List GaussianInt) (i : ZMod s) : GaussianInt :=
  if a ≤ i.val ∧ i.val < a+xs.length then xs[i.val-a]?.getD 0 else 0

theorem packedField_get {s a : ℕ} (xs : List GaussianInt) (hfit : a+xs.length ≤ s)
    (j : ℕ) (hj : j < xs.length) :
    packedField a xs ((a+j : ℕ) : ZMod s) = xs[j] := by
  have hv : (((a+j : ℕ) : ZMod s)).val = a+j := ZMod.val_cast_of_lt (by omega)
  unfold packedField
  rw [hv]
  simp [hj,List.getElem?_eq_getElem hj]

theorem packedField_outside {s a : ℕ} (xs : List GaussianInt) (i : ZMod s)
    (hi : ¬ (a ≤ i.val ∧ i.val < a+xs.length)) : packedField a xs i = 0 := by
  simp only [packedField,if_neg hi]

theorem packedInterval_packedField {s a : ℕ} (xs : List GaussianInt) (hfit : a+xs.length ≤ s) :
    packedInterval a xs.length (packedField (s := s) a xs) = xs := by
  apply List.ext_getElem (packedInterval_length _ hfit)
  intro j hj hk
  rw [packedInterval_get _ hfit hk,packedField_get xs hfit j hk]

theorem packedField_property {s a : ℕ} (xs : List GaussianInt) (P : GaussianInt → Prop)
    (hzero : P 0) (hxs : ∀ z ∈ xs, P z) (i : ZMod s) : P (packedField a xs i) := by
  unfold packedField
  split
  · rename_i hi
    have hj : i.val-a < xs.length := by omega
    rw [List.getElem?_eq_getElem hj,Option.getD_some]
    exact hxs _ (List.getElem_mem hj)
  · exact hzero

theorem packedField_read {A s a q w : ℕ} (hA : 4 ≤ A) (hw : 1 ≤ w)
    (xs : List GaussianInt) (tail : List (Fin (A+4))) (hxs : ∀ z ∈ xs, Fits w z)
    (i : ZMod s) (hi : a ≤ i.val ∧ i.val < a+xs.length) :
    packedIntervalRead q w a (cstream A w xs++tail) i = value q (packedField a xs i) := by
  have hj : i.val-a < xs.length := by omega
  unfold packedIntervalRead
  rw [cstream_word w xs tail (i.val-a) hj,decodeWord_of_fits hA hw _ (hxs _ (List.getElem_mem hj))]
  simp only [packedField,if_pos hi,List.getElem?_eq_getElem hj,Option.getD_some]

/-- A bounded encoded local prefix determines a fitting ambient field supported
on that interval, without allocating an ambient-sized stream. -/
theorem encodedRange_packedField {A s a N w q e : ℕ} [NeZero s]
    (hw : 0 < w) (hfit : a+N ≤ s) (hbudget : q+e+2 ≤ w)
    (E : List (Fin (A+4))) (hlen : E.length = N*w) (hrange : EncodedRange A w q e E) :
    ∃ D : ZMod s → GaussianInt, E = cstream A w (packedInterval a N D) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^e) ∧ (∀ i, Fits w (D i)) := by
  obtain ⟨xs,hxs,hbound⟩ := hrange
  have hxlen : xs.length = N := by
    have hh : xs.length*w = N*w := by simpa only [hxs,length_cstream] using hlen
    nlinarith only [hh,hw]
  let D := packedField (s := s) a xs
  have hD : ∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^e := by
    intro i
    apply packedField_property xs _ ?_ hbound i
    have hz : value q (0 : GaussianInt) = (0 : ℂ) := by apply Complex.ext <;> simp [value]
    rw [hz]; simp
  have hpacked : packedInterval a N D = xs := by
    simpa only [hxlen] using packedInterval_packedField (s := s) xs (by rw [hxlen]; exact hfit)
  exact ⟨D,by rw [hpacked]; exact hxs,hD,fun i => fits_of_value_power hbudget (D i) (hD i)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
