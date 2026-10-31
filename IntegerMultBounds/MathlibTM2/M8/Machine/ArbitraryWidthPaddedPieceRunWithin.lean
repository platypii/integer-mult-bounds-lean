module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceRun
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPiecePlacementWithin

/-! Paid row padding, bounded dispatch, and crop share one padded-volume reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceRunWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding
open ArbitraryWidthPaddedPieceRun

def coefficient : ℕ := max (413+ArbitraryWidthPieceRunWithin.coefficient) 826

theorem runs_within (v : Descriptor) (R' k : ℕ)
    (paddingHeaders : Fin 4 → List Bool) (rootHeaders : Fin 6 → List Bool)
    (hp : v.Positive) (hR : v.rows ≤ R')
    (hpadding : ArbitraryWidthPaddedPiecePadding.Headers v R' paddingHeaders)
    (hroot : RecursiveDimensionBank.Headers (withRows v R') rootHeaders)
    (hwidth : v.width < Machine.width^(k+1)) (hrows : roleCount^k ∣ R')
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : CallReady.Ready f p node scalar st)
    (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free rootHeaders frame)
    (x : Fin (volume prime v) → ZMod 2) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(coefficient*volume prime (withRows v R') : ℕ) ≤
      (bank x paddingHeaders rootHeaders f p node scalar st frame).head j ∧
      (bank x paddingHeaders rootHeaders f p node scalar st frame).head j+
        (coefficient*volume prime (withRows v R') : ℕ) ≤ hi) :
    HoareWithin program
      (fun z => z = bank x paddingHeaders rootHeaders f p node scalar st frame)
      (fun z => z = bank (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)
        paddingHeaders rootHeaders f p node scalar st frame) (cost v R' rootHeaders) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hp' : (withRows v R').Positive :=
    ⟨hp.1,lt_of_lt_of_le hp.2.1 hR,hp.2.2⟩
  let extra := ArbitraryWidthPaddedPiecePlacement.privateBank rootHeaders f p node scalar st frame
  have hpad := hoare_extend_eq
    (ArbitraryWidthPaddedPiecePadding.pad_hoare v R' paddingHeaders hp hR hpadding x) extra
  have hreserve : 413*volume prime (withRows v R')+
      ArbitraryWidthPieceRunWithin.coefficient*volume prime (withRows v R') ≤
      coefficient*volume prime (withRows v R') := by
    have h := Nat.mul_le_mul_right (volume prime (withRows v R'))
      (show 413+ArbitraryWidthPieceRunWithin.coefficient ≤ coefficient from le_max_left _ _)
    rwa [Nat.add_mul] at h
  have hpadWithin := HoareWithin.of_time_heads hpad lo hi (by
    rintro z rfl j
    have hm := hmargin j
    change lo+_ ≤ (bank x paddingHeaders rootHeaders f p node scalar st frame).head j ∧
      (bank x paddingHeaders rootHeaders f p node scalar st frame).head j+_ ≤ hi
    omega)
  have hprepared : ∀ j, lo+(ArbitraryWidthPieceRunWithin.coefficient*volume prime (withRows v R') : ℕ) ≤
      ((ArbitraryWidthPaddedPiecePadding.middle (padArray R' 0 x) paddingHeaders).append extra).head j ∧
      ((ArbitraryWidthPaddedPiecePadding.middle (padArray R' 0 x) paddingHeaders).append extra).head j+
        (ArbitraryWidthPieceRunWithin.coefficient*volume prime (withRows v R') : ℕ) ≤ hi := by
    intro j
    have ht := hpad.head_change j
    have hm := hmargin j
    change lo+_ ≤ ((ArbitraryWidthPaddedPiecePadding.input x paddingHeaders).append extra).head j ∧
      ((ArbitraryWidthPaddedPiecePadding.input x paddingHeaders).append extra).head j+_ ≤ hi at hm
    omega
  have hpiece := ArbitraryWidthPaddedPiecePlacementWithin.runs_within
    (ArbitraryWidthPaddedPiecePadding.middle (padArray R' 0 x) paddingHeaders) (1 : Fin 12)
    (withRows v R') rootHeaders k hp' hroot hwidth hrows
    f p node scalar st ready frame hfree (padArray R' 0 x) rfl rfl lo hi hprepared
  rw [ArbitraryWidthPaddedPiecePadding.middle_source] at hpiece
  have hcrop := hoare_extend_eq (ArbitraryWidthPaddedPiecePadding.crop_hoare v R' paddingHeaders
    hp hR hpadding (Shared50RecursiveNodeRows.transpose (one_dvd R') (padArray R' 0 x))) extra
  rw [cropArray_transpose_padArray] at hcrop
  have hcropReserve := Nat.mul_le_mul_right (volume prime (withRows v R'))
    (show 826 ≤ coefficient from le_max_right _ _)
  have hheads : (bank (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)
      paddingHeaders rootHeaders f p node scalar st frame).head =
      (bank x paddingHeaders rootHeaders f p node scalar st frame).head :=
    Tapes.append_head_congr _ _ extra extra rfl rfl
  have hcropWithin := HoareWithin.of_time_post_heads hcrop lo hi (by
    rintro z rfl j
    change lo+_ ≤ (bank (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)
      paddingHeaders rootHeaders f p node scalar st frame).head j ∧
      (bank (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)
      paddingHeaders rootHeaders f p node scalar st frame).head j+_ ≤ hi
    rw [hheads]
    have hm := hmargin j
    omega)
  exact ((hpadWithin.seq hpiece).seq hcropWithin).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; omega) (fun _ h => h)

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceRunWithin
