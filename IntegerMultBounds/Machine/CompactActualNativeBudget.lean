import IntegerMultBounds.Machine.CompactActualNativeWidth

/-! Actual native stage costs measured in the original polynomial coefficient
volume. The single global padding contributes at most a factor two, and the
role divisor is restored explicitly at descendant depth. Including signed
guard bits and native/Boolean conversion therefore preserves the certified
stage exponent without paying the padding again at every recursive node. -/
namespace IntegerMultBounds.Machine.CompactActualNativeBudget
noncomputable section
open Sizes
open CompactGlobalRowPadding CompactReservationCutoff
open CompactActualStageAllowance CompactActualStageGeometry CompactActualStageInputs
open CompactActualNativeWidth (symbols payload)
open ActivePrefixStageParameters
open ActivePrefixStageNative (cost)

/-- Original unpadded polynomial volume, with actual coefficient precision. -/
def volume (n D : ℕ) := 2^(D*K n)*(b n*2^ℓ n)

/-- Multiplying a descendant's volume by its exact role divisor recovers the
single initial padding. Arithmetic guard bits cost only a fixed factor. -/
theorem charged_volume (c m n D j w A : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hcut : cutoff c m n≤D) (hj : j≤depth m (d n)) (hw : w≤A*b n) :
    (rowsAt c m (d n) (K n) j)*
      (actualShape n c m D (payload n w)).recordWidth*c^j≤12*(A+1)*volume n D := by
  have hreserved := (nonfallback c m n D (cutoff_ready c m n D hc hm hcut).1).2.2
  have hpad := (CompactGlobalReservation.padded_volume c m (d n) D (4*CompactScalarAllowances.guardLog n+6)
    (K n) (payload n w) (by omega) (positive_chunk n) hreserved).2
  have hp := CompactActualNativeWidth.payload_linear n w A (by have := one_le_b n; omega) hw
  calc
    _ = initialRows c m (d n) (K n)*(actualShape n c m D (payload n w)).recordWidth := by
      rw [Nat.mul_right_comm,rowsAt_mul c m (d n) (K n) j (by omega) (positive_chunk n) hj]
    _ ≤ 2*(2^(D*K n)*payload n w) := hpad
    _ ≤ 2*(2^(D*K n)*(6*(A+1)*b n*2^ℓ n)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hp)
    _ = _ := by unfold volume; ring

/-- One uniform fixed native machine has the actual descendant cost row,
including stored-width guards, all conversion, and once-only global padding. -/
theorem eventually_correct (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q Networks.Shared50ModularControl.prime,
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D j w : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hj : j≤depth m (d n)) (_hwlo : b n≤w) (_hwhi : w≤14*b n)
      (v : Stage (actualShape n c m D (payload n w))),
      ∃ h : Ready (actualShape n c m D (payload n w)) v (rowsAt c m (d n) (K n) j),
      let input := inputs v (rowsAt c m (d n) (K n) j) h
      ∃ hp : 1 < input.stage.f → ActivePrefixStageRuntimeData.Packed input 1,
        (cost (B:=symbols n w) 1 input hp : ℝ)*(c^j : ℕ)≤C*(volume n D : ℕ)*
          ((max 1 ((input.stage.f-1)*(actualShape n c m D (payload n w)).guard) : ℕ) : ℝ)^Parameters.tau ∧
        ∀ (xs : ActivePrefixStageFullSelected.Address input → Fin (symbols n w) → Fin 6)
          (_hn : ∀ i k,xs i k≠blank),
          HoareTime P (fun z => z=ActivePrefixStageNative.bank input (CompactActualNativeWidth.triple_capacity n c m D w) xs)
            (fun z => z=ActivePrefixStageNative.bank input (CompactActualNativeWidth.triple_capacity n c m D w)
              (xs ∘ ActivePrefixStageRuntimeSelected.destination input)) (cost (B:=symbols n w) 1 input hp) := by
  obtain ⟨q,P,C,hC,hevent⟩ := CompactActualNativeWidth.eventually_correct c m hc hm
  refine ⟨q,P,180*C,by positivity,?_⟩
  filter_upwards [hevent] with n hn
  intro D j w hcut hD hj hwlo hwhi v
  obtain ⟨h,hp,hcost,hrun⟩ := hn D j w hcut hD hj hwlo v
  refine ⟨h,hp,?_,hrun⟩
  have hvol := charged_volume c m n D j w 14 hc hm hcut hj hwhi
  have hvol' : (((rowsAt c m (d n) (K n) j)*
      (actualShape n c m D (payload n w)).recordWidth*c^j : ℕ) : ℝ)≤180*(volume n D : ℝ) := by
    exact_mod_cast hvol
  let factor : ℝ := ((max 1 ((v.f-1)*(actualShape n c m D (payload n w)).guard) : ℕ) : ℝ)^Parameters.tau
  have hf : 0≤factor := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmul := mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg (α:=ℝ) (c^j))
  change (cost (B:=symbols n w) 1 _ hp : ℝ)*(c^j : ℕ)≤(180*C)*(volume n D : ℕ)*factor
  calc
    _ ≤ (C*((rowsAt c m (d n) (K n) j)*
        (actualShape n c m D (payload n w)).recordWidth : ℕ)*factor)*(c^j : ℕ) := hmul
    _ = C*(((rowsAt c m (d n) (K n) j)*
        (actualShape n c m D (payload n w)).recordWidth*c^j : ℕ) : ℝ)*factor := by push_cast; ring
    _ ≤ C*(180*(volume n D : ℝ))*factor :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol' hC.le) hf
    _ = _ := by ring

end
end IntegerMultBounds.Machine.CompactActualNativeBudget
