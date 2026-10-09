import IntegerMultBounds.Machine.ArbitraryWidthHighExecutionInitialize
import IntegerMultBounds.Machine.ArbitraryWidthHighPaddingSuffix

/-! Every physically copied execution header is bounded by twice the original
payload volume. Canonicality and numeric bounds follow from the real header
contracts and the already proved dimension and padding volume bounds. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighHeaderBounds
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighLayout (originalDescriptor joinedDescriptor)
open ArbitraryWidthHighPrepare (highDepth rounded)
open ArbitraryWidthHighExecutionInitialize (Bounded)
open ArbitraryWidthExecutionPrivateHeadersRoot (exchangeWords)
open ArbitraryWidthExecutionPrivateHeadersMovement (movementWords)
open ArbitraryWidthExecutionPrivateHeadersPadding (paddedWords)

theorem bounded_mono {n : ℕ} {bs : Fin n → List Bool} {V W : ℕ}
    (h : Bounded bs V) (hw : V ≤ W) : Bounded bs W :=
  ⟨h.canonical,fun i => (h.value i).trans hw⟩

theorem root_bounded (v : Descriptor) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hh : RecursiveDimensionBank.Headers v hs) : Bounded hs (volume prime v) :=
  ⟨hh.2,fun i => (hh.1 i).trans_le
    (RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le v hp i)⟩

theorem exchange_bounded (P e G B r : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hr : r ≤ e) (hs : Fin 6 → List Bool) (rs : List Bool)
    (hh : RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs)
    (hv : Counter.value rs = r) (hc : GrowingCounterData.Canonical rs) :
    Bounded (exchangeWords hs rs) (2*volume prime (originalDescriptor P e G B)) := by
  have hp : (originalDescriptor P e G B).Positive :=
    ⟨hP,by change 0 < 1; decide,by change 0 < 1; decide,hG,hB⟩
  have hb := root_bounded _ hp hs hh
  have he := RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le
    (originalDescriptor P e G B) hp 3
  have hrv : Counter.value rs ≤ volume prime (originalDescriptor P e G B) := by
    rw [hv]
    exact hr.trans he
  constructor
  · intro i; induction i using Fin.addCases with
    | left i => simpa only [exchangeWords,Fin.addCases_left] using hb.canonical i
    | right i => simpa only [exchangeWords,Fin.addCases_right] using hc
  · intro i; induction i using Fin.addCases with
    | left i =>
      simp only [exchangeWords,Fin.addCases_left]
      exact (hb.value i).trans (by omega)
    | right i =>
      simp only [exchangeWords,Fin.addCases_right]
      exact hrv.trans (by omega)

theorem movement_bounded (P e G B r : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hr : r ≤ e) (ss op oe rs : List Bool)
    (hss : Counter.value ss = prime^(e-r)*G) (css : GrowingCounterData.Canonical ss)
    (hop : Counter.value op = P*prime^r) (cop : GrowingCounterData.Canonical op)
    (hoe : Counter.value oe = prime^(e-r)*B) (coe : GrowingCounterData.Canonical oe)
    (hrs : Counter.value rs = r) (crs : GrowingCounterData.Canonical rs) :
    Bounded (movementWords ss op oe rs) (2*volume prime (originalDescriptor P e G B)) := by
  obtain ⟨_,he,hvals⟩ := ArbitraryWidthHighDimensions.data_volume_bounds
    prime P G B e r Shared50ModularControl.prime_prime.two_le hr hP hG hB
  have hvol := ArbitraryWidthHighPaddingSuffix.original_volume prime P e G B
  rw [← hvol] at he hvals
  have h3 := hvals 3
  have h4 := hvals 4
  have h5 := hvals 5
  constructor
  · intro i; fin_cases i
    · exact css
    · exact cop
    · exact coe
    · exact FixedBasePowerUntil.counter_canonical 0
    · exact crs
  · intro i; fin_cases i
    · change Counter.value ss ≤ _
      rw [hss]
      have h : prime^(e-r)*G ≤ volume prime (originalDescriptor P e G B) := by
        simpa [ArbitraryWidthHighDimensions.values,Nat.mul_comm] using h4
      omega
    · change Counter.value op ≤ _
      rw [hop]
      change P*prime^r ≤ _ at h3
      omega
    · change Counter.value oe ≤ _
      rw [hoe]
      have h : prime^(e-r)*B ≤ volume prime (originalDescriptor P e G B) := by
        simpa [ArbitraryWidthHighDimensions.values,Nat.mul_comm] using h5
      omega
    · change Counter.value [] ≤ _; simp [Counter.value]
    · change Counter.value rs ≤ _; rw [hrs]; omega

theorem padding_root_bounded (v : Descriptor) (R V : ℕ) (hp : v.Positive) (hR : v.rows ≤ R)
    (ph : Fin 4 → List Bool) (rh : Fin 6 → List Bool)
    (hph : ArbitraryWidthPaddedPiecePadding.Headers v R ph)
    (hrh : RecursiveDimensionBank.Headers (RecursiveRowPadding.withRows v R) rh)
    (hvol : volume prime (RecursiveRowPadding.withRows v R) ≤ V) :
    Bounded (paddedWords ph rh) V := by
  have hRp : 0 < R := lt_of_lt_of_le hp.2.1 hR
  have hpad : (RecursiveRowPadding.withRows v R).Positive :=
    ⟨hp.1,hRp,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩
  have hb := root_bounded _ hpad rh hrh
  have hprefix := (RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le
    (RecursiveRowPadding.withRows v R) hpad 0).trans hvol
  have hrows := (RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le
    (RecursiveRowPadding.withRows v R) hpad 1).trans hvol
  have hlength : RecursiveInterchangeRows.rowLength prime v ≤ V := by
    have houter : 0 < v.beforeRows*R := Nat.mul_pos hp.1 hRp
    have hl := Nat.le_mul_of_pos_left (RecursiveInterchangeRows.rowLength prime v) houter
    have heq : volume prime (RecursiveRowPadding.withRows v R) =
        (v.beforeRows*R)*RecursiveInterchangeRows.rowLength prime v := by
      unfold volume RecursiveRowPadding.withRows RecursiveInterchangeRows.rowLength
      ring
    rw [← heq] at hl
    exact hl.trans hvol
  constructor
  · intro i; induction i using Fin.addCases with
    | left i => simpa only [paddedWords,Fin.addCases_left] using hph.2 i
    | right i => simpa only [paddedWords,Fin.addCases_right] using hrh.2 i
  · intro i; induction i using Fin.addCases with
    | left i =>
      simp only [paddedWords,Fin.addCases_left]
      rw [hph.1]
      fin_cases i
      · exact hprefix
      · exact hR.trans hrows
      · exact hrows
      · exact hlength
    | right i => simpa only [paddedWords,Fin.addCases_right] using (hb.value i).trans hvol

theorem padded_bounded (P e G B : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hr : highDepth prime e ≤ e) (ph : Fin 4 → List Bool) (rh : Fin 6 → List Bool)
    (hph : ArbitraryWidthPaddedPiecePadding.Headers
      (joinedDescriptor prime P e (highDepth prime e) G B) (rounded prime e) ph)
    (hrh : RecursiveDimensionBank.Headers (ArbitraryWidthHighPaddedBudget.descriptor P e G B) rh) :
    Bounded (paddedWords ph rh) (2*volume prime (originalDescriptor P e G B)) := by
  have hp : (joinedDescriptor prime P e (highDepth prime e) G B).Positive :=
    ⟨hP,pow_pos Shared50ModularControl.prime_prime.pos _,by change 0 < 1; decide,hG,hB⟩
  have hR : (joinedDescriptor prime P e (highDepth prime e) G B).rows ≤ rounded prime e := by
    change prime^(2*highDepth prime e) ≤ _
    rw [ArbitraryWidthHighRows.square_power]
    exact ArbitraryWidthHighPrepare.rows_le_rounded prime e Shared50ModularControl.prime_prime.two_le
  exact padding_root_bounded _ _ _ hp hR ph rh hph hrh
    (ArbitraryWidthHighPaddedBudget.volume_le P e G B hr)

end
end IntegerMultBounds.Machine.ArbitraryWidthHighHeaderBounds
