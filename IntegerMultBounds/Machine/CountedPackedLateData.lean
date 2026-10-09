import IntegerMultBounds.Machine.CountedPackedParityValue
import IntegerMultBounds.Machine.CountedPackedControlLoadValue
import IntegerMultBounds.Machine.CountedPackedGuarded

/-! Exact word specification for the two early gadgets and the physical dirty
load/unload used by the later-source gadget. These are data semantics; the
actual sequential tape assembly is proved separately. -/
namespace IntegerMultBounds.Machine.CountedPackedLateData
noncomputable section
open Compact Compact.PowerTwo Compact.Radix
open ColumnTransducer (addRule subRule)
open CountedPackedControlLoadRun (word word_length load_value unload_value)
open CountedPackedParityRun (parities parities_length)

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (V W U X : List Bool)
def firstV := PackedArith.v2 q b hb hbq V W (parities b U X.length)
def firstW := PackedArith.w2 q b hb hbq V W (parities b U X.length)
def loaded := word addRule b hb U X

def target := PackedArith.v2 q b hb hbq (firstV q b hb hbq V W U X)
  (firstW q b hb hbq V W U X) (parities b (loaded b hb U X) X.length)
def temp := PackedArith.w2 q b hb hbq (firstV q b hb hbq V W U X)
  (firstW q b hb hbq V W U X) (parities b (loaded b hb U X) X.length)
def restored := word subRule b hb (loaded b hb U X) X

/-- Every stage has the literal original width; no target erasure is assumed
when physically replacing an equal-width word. -/
theorem lengths (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hU : U.length=X.length*b) :
    (firstV q b hb hbq V W U X).length=V.length ∧
    (firstW q b hb hbq V W U X).length=W.length ∧
    (loaded b hb U X).length=U.length ∧
    (target q b hb hbq V W U X).length=V.length ∧
    (temp q b hb hbq V W U X).length=W.length ∧
    (restored b hb U X).length=U.length := by
  have hpV : V.length=(parities b U X.length).length*q := by simpa using hV
  have hpW : W.length=(parities b U X.length).length*b := by simpa using hW
  obtain ⟨_,_,_,_,_,_,_,hv,_,hw⟩ := PackedArith.lengths q b hb hbq V W
    (parities b U X.length) hpV hpW
  have hv' : (firstV q b hb hbq V W U X).length=V.length := by
    exact hv.trans hpV.symm
  have hw' : (firstW q b hb hbq V W U X).length=W.length := by
    exact hw.trans hpW.symm
  have hu' : (loaded b hb U X).length=U.length := word_length addRule b hb U X hU
  have hfv : (firstV q b hb hbq V W U X).length=
      (parities b (loaded b hb U X) X.length).length*q := by simpa [hv'] using hV
  have hfw : (firstW q b hb hbq V W U X).length=
      (parities b (loaded b hb U X) X.length).length*b := by simpa [hw'] using hW
  obtain ⟨_,_,_,_,_,_,_,hvv,_,hww⟩ := PackedArith.lengths q b hb hbq
    (firstV q b hb hbq V W U X) (firstW q b hb hbq V W U X)
    (parities b (loaded b hb U X) X.length) hfv hfw
  refine ⟨hv',hw',hu',hvv.trans ?_,hww.trans ?_,?_⟩
  · simp only [parities_length]; exact hV.symm
  · simp only [parities_length]; exact hW.symm
  · exact (word_length subRule b hb (loaded b hb U X) X (hu'.trans hU)).trans hu'

/-- The literal data produced by the eight real stages has precisely the
packedLate integer specification, even outside the guarded set. -/
theorem value_spec (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hU : U.length=X.length*b) :
    ((Counter.value (target q b hb hbq V W U X) : ℤ),
      (Counter.value (temp q b hb hbq V W U X) : ℤ),
      (Counter.value (restored b hb U X) : ℤ)) =
      packedLate ((2 : ℤ)^q) ((2 : ℤ)^b) (X.map ctrl)
        (Counter.value V) (Counter.value W) (Counter.value U) := by
  obtain ⟨hfv,hfw,hlu,_,_,_⟩ := lengths q b hb hbq V W U X hV hW hU
  have hc₀ := CountedPackedParityValue.controls_eq_digit_parities b hb U X.length hU
  have hc₁ := CountedPackedParityValue.controls_eq_digit_parities b hb
    (loaded b hb U X) X.length (hlu.trans hU)
  have he₀ := forward_value q b hb hbq V W (parities b U X.length)
    (by simpa using hV) (by simpa using hW)
  rw [hc₀] at he₀
  change ((Counter.value (firstV q b hb hbq V W U X) : ℤ),
    (Counter.value (firstW q b hb hbq V W U X) : ℤ)) = _ at he₀
  have he₁ := forward_value q b hb hbq (firstV q b hb hbq V W U X)
    (firstW q b hb hbq V W U X) (parities b (loaded b hb U X) X.length)
    (by simpa only [parities_length,hfv] using hV)
    (by simpa only [parities_length,hfw] using hW)
  rw [hc₁] at he₁
  change ((Counter.value (target q b hb hbq V W U X) : ℤ),
    (Counter.value (temp q b hb hbq V W U X) : ℤ)) = _ at he₁
  have hl := load_value b hb U X hU
  change (Counter.value (loaded b hb U X) : ℤ) = _ at hl
  have hr := unload_value b hb (loaded b hb U X) X (hlu.trans hU)
  change (Counter.value (restored b hb U X) : ℤ) = _ at hr
  unfold packedLate
  simp only [List.length_map,← he₀,← hl,← he₁,← hr]


/-- Actual literal blocks supplying the later-source guard. -/
def states (q b : ℕ) (V W U X : List Bool) : List LateDigitState :=
  (List.range X.length).map fun i =>
    ⟨Counter.value (Gather.field V (i*q) q), Counter.value (Gather.field W (i*b) b),
      Counter.value (Gather.field U (i*b) b), ctrl (X.getD i false)⟩

private theorem states_target (q b : ℕ) (V W U X : List Bool) :
    (states q b V W U X).map LateDigitState.v = blockValues V q X.length := by
  simp only [states,List.map_map,blockValues]; rfl
private theorem states_temp (q b : ℕ) (V W U X : List Bool) :
    (states q b V W U X).map LateDigitState.w = blockValues W b X.length := by
  simp only [states,List.map_map,blockValues]; rfl
private theorem states_control (q b : ℕ) (V W U X : List Bool) :
    (states q b V W U X).map LateDigitState.u = blockValues U b X.length := by
  simp only [states,List.map_map,blockValues]; rfl
private theorem states_source (q b : ℕ) (V W U X : List Bool) :
    (states q b V W U X).map LateDigitState.x = X.map ctrl := by
  simp only [states,List.map_map]
  conv_rhs => rw [list_eq_range X,List.map_map]
  rfl

private theorem packed_word (w n : ℕ) (xs : List Bool) (hl : xs.length=n*w) :
    pack ((2 : ℤ)^w) (blockValues xs w n) = (Counter.value xs : ℤ) := by
  rw [← digits_blocks xs w n hl]
  apply pack_digits _ (by positivity) _ _
  constructor
  · positivity
  · rw [pow_blocks,← hl]
    exact_mod_cast Counter.value_lt xs

/-- On the guarded set, the later-source gadget changes only selected target
low bits and literally restores both dirty temporary words. -/
theorem guarded_words (hV : V.length=X.length*q) (hW : W.length=X.length*b)
    (hU : U.length=X.length*b)
    (hgood : ∀ d ∈ states q b V W U X,
      d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    target q b hb hbq V W U X = List.zipWith xor V (toggleMask q X) ∧
      temp q b hb hbq V W U X = W ∧ restored b hb U X = U := by
  have hq : 1 ≤ q := by omega
  have hQ : 2*((2 : ℤ)^(q-1)) = (2 : ℤ)^q := by
    have he : q=(q-1)+1 := by omega
    conv_rhs => rw [he,pow_succ]
    ring
  have he := packedLate_correct ((2 : ℤ)^b) ((2 : ℤ)^(q-1))
    (by have hp : (0 : ℤ)<2^b := by positivity
        omega) (by positivity) (states q b V W U X) hgood
  rw [hQ,states_source,states_target,states_temp,states_control,
    packed_word q X.length V hV,packed_word b X.length W hW,
    packed_word b X.length U hU] at he
  have hv := value_spec q b hb hbq V W U X hV hW hU
  rw [he] at hv
  have hvs : (states q b V W U X).map (fun d => toggle d.v d.x) =
      toggleList (blockValues V q X.length) (X.map ctrl) := by
    rw [← states_target q b V W U X,← states_source q b V W U X]
    simp only [states,List.map_map,toggleList]
    rw [zip_maps]
    rfl
  rw [hvs] at hv
  have htoggle := toggle_word_value q hq V X hV
  rw [digits_blocks V q X.length hV] at htoggle
  obtain ⟨_,_,_,hvt,hwt,hut⟩ := lengths q b hb hbq V W U X hV hW hU
  refine ⟨?_,?_,?_⟩
  · apply CountedPackedGuarded.word_eq_of_length_value
    · rw [hvt,List.length_zipWith,hV,toggleMask_length q hq,min_self]
    · have he : (Counter.value (target q b hb hbq V W U X) : ℤ) =
          (Counter.value (List.zipWith xor V (toggleMask q X)) : ℤ) :=
        (congrArg Prod.fst hv).trans htoggle.symm
      exact_mod_cast he
  · apply CountedPackedGuarded.word_eq_of_length_value _ _ hwt
    have he : (Counter.value (temp q b hb hbq V W U X) : ℤ) =
        (Counter.value W : ℤ) := congrArg (fun z => z.2.1) hv
    exact_mod_cast he
  · apply CountedPackedGuarded.word_eq_of_length_value _ _ hut
    have he : (Counter.value (restored b hb U X) : ℤ) =
        (Counter.value U : ℤ) := congrArg (fun z => z.2.2) hv
    exact_mod_cast he

end
end IntegerMultBounds.Machine.CountedPackedLateData
