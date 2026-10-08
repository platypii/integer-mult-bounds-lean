import IntegerMultBounds.Machine.FlatAffineScalingPayload
import IntegerMultBounds.Machine.FlatControlledShiftMetadata
import IntegerMultBounds.Machine.SharedPayloadPair

/-! A concrete initialized scale followed by an initialized controlled shift.
There are only two physical payload tapes. Each operation has its own metadata
bank, with its unused payload slots blank. Equal-volume reframing changes only
finite indices, never the word on the common tape. -/
namespace IntegerMultBounds.Machine.FlatScaleShiftPair
open Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
noncomputable section
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩
variable {P B b c D : ℕ}

/-- A type-level change of dimensions preserves the entire physical word. -/
def reframe {m n : ℕ} (h : m = n) (a : Fin m → Fin 4) : Fin n → Fin 4 :=
  fun i => a (Fin.cast h.symm i)

theorem reframe_word {m n : ℕ} (h : m = n) (a : Fin m → Fin 4) :
    List.ofFn (reframe h a) = List.ofFn a := by
  subst n
  rfl

def shiftedInput {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (hvolume : P*(modulus b*B) = prime^PrefixAddressData.widthSum (low++0::high) width*(prime^(width 0)*D))
    (a : Fin (P*(modulus b*B)) → Fin 4) :=
  reframe hvolume (FlatAffineScalingArray.array hr a)

/-- The second stage consumes the first stage's literal normalized word. -/
theorem handoff {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (s : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (hvolume : P*(modulus b*B) = prime^PrefixAddressData.widthSum (low++0::high) width*(prime^(width 0)*D))
    (a : Fin (P*(modulus b*B)) → Fin 4) (ws : Fin (c+1) → List Bool)
    (bs qs ns ds es fs : List Bool) :
    SharedPayload.payload (FlatAffineScalingPayload.output (radix := prime) hr a bs qs ns)
      (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r) =
    SharedPayload.payload (RationalPrefixTranslationBootstrap.input s (low++0::high) width ws
      (shiftedInput hr low high width hvolume a) (fun _ => blank) (fun _ => blank) 0 0 ds es fs)
      (FlatControlledShiftPayload.sourceSlot c) (FlatControlledShiftPayload.destSlot c) := by
  rw [FlatAffineScalingPayload.output_payload,FlatControlledShiftPayload.input_payload]
  unfold shiftedInput
  rw [reframe_word]
  unfold FlatAffineScalingPayload.pair FlatArrayNormalize.pair
  congr 1; funext i; fin_cases i <;> rfl

noncomputable def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (s : ℚ) (low high : List (Fin (c+1))) :=
  SharedPayloadPair.program (FlatAffineScalingPayload.program (radix := prime) hr)
    (FlatControlledShiftReady.program (radix := prime) s (low++0::high) (by simp))
    (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r)
    (FlatAffineScalingPayload.slots_distinct r)
    (FlatControlledShiftPayload.sourceSlot c) (FlatControlledShiftPayload.destSlot c)
    (FlatControlledShiftPayload.slots_ne c)

def input {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (s : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (_hvolume : P*(modulus b*B) = prime^PrefixAddressData.widthSum (low++0::high) width*(prime^(width 0)*D))
    (a : Fin (P*(modulus b*B)) → Fin 4) (ws : Fin (c+1) → List Bool)
    (bs qs ns ds es fs : List Bool) :=
  SharedPayloadPair.input (FlatAffineScalingPayload.input (radix := prime) hr a bs qs ns)
    (RationalPrefixTranslationBootstrap.input s (low++0::high) width ws
      (fun _ : Fin (prime^PrefixAddressData.widthSum (low++0::high) width*(prime^(width 0)*D)) => blank) (fun _ => blank) (fun _ => blank) 0 0 ds es fs)
    (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r)
    (FlatControlledShiftPayload.sourceSlot c) (FlatControlledShiftPayload.destSlot c)

def output {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (s : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (hvolume : P*(modulus b*B) = prime^PrefixAddressData.widthSum (low++0::high) width*(prime^(width 0)*D))
    (a : Fin (P*(modulus b*B)) → Fin 4) (ws : Fin (c+1) → List Bool)
    (bs qs ns ds es fs : List Bool) :=
  SharedPayloadPair.output (FlatAffineScalingPayload.output (radix := prime) hr a bs qs ns)
    (FlatControlledShiftReady.output s low high width ws
      (shiftedInput hr low high width hvolume a) (fun _ => blank) (fun _ => blank) 0 0 ds es fs)
    (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r)
    (FlatControlledShiftPayload.sourceSlot c) (FlatControlledShiftPayload.destSlot c)

/-- The permanent source is physical tape zero. -/
def sourceSlot (r : ℚ) (c : ℕ) : Fin ((2+ActualAffineScalingStream.TapeCount r)+FlatControlledShiftPayload.TapeCount c) :=
  Fin.castAdd _ (Fin.castAdd _ (0 : Fin 2))

/-- The permanent scratch is physical tape one. -/
def destSlot (r : ℚ) (c : ℕ) : Fin ((2+ActualAffineScalingStream.TapeCount r)+FlatControlledShiftPayload.TapeCount c) :=
  Fin.castAdd _ (Fin.castAdd _ (1 : Fin 2))

/-- The final whole word is canonical on the original common source; scratch
is blank and both heads are at zero. Every private metadata tape is retained. -/
theorem output_payload {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (s : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (hvolume : P*(modulus b*B) = prime^PrefixAddressData.widthSum (low++0::high) width*(prime^(width 0)*D))
    (a : Fin (P*(modulus b*B)) → Fin 4) (ws : Fin (c+1) → List Bool)
    (bs qs ns ds es fs : List Bool) :
    SharedPayload.payload (output hr s low high width hvolume a ws bs qs ns ds es fs)
      (sourceSlot r c) (destSlot r c) =
      FlatAffineScalingPayload.pair
        (FlatControlledShiftArray.array s low high width (shiftedInput hr low high width hvolume a)) := by
  unfold output SharedPayloadPair.output
  have hp := FlatControlledShiftPayload.output_payload s low high width ws
    (shiftedInput hr low high width hvolume a) (fun _ => blank) (fun _ => blank) 0 0 ds es fs
  rw [hp]
  unfold SharedPayload.payload sourceSlot destSlot
  simp only [Tapes.append,Fin.addCases_left]
  unfold FlatAffineScalingPayload.pair FlatArrayNormalize.pair
  congr 1; funext i; fin_cases i <;> rfl

/-- The initial common source contains exactly the supplied input array. -/
theorem input_payload {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (s : ℚ) (low high : List (Fin (c+1))) (width : Fin (c+1) → ℕ)
    (hvolume : P*(modulus b*B) = prime^PrefixAddressData.widthSum (low++0::high) width*(prime^(width 0)*D))
    (a : Fin (P*(modulus b*B)) → Fin 4) (ws : Fin (c+1) → List Bool)
    (bs qs ns ds es fs : List Bool) :
    SharedPayload.payload (input hr s low high width hvolume a ws bs qs ns ds es fs)
      (sourceSlot r c) (destSlot r c) = FlatAffineScalingPayload.pair a := by
  unfold input SharedPayloadPair.input SharedPayload.bank
  rw [FlatAffineScalingPayload.input_payload]
  unfold SharedPayload.payload sourceSlot destSlot
  simp only [Tapes.append,Fin.addCases_left]
  unfold FlatAffineScalingPayload.pair
  congr 1; funext i; fin_cases i <;> rfl

/-- Actual scale and shift programs, initialized from blank workspace, composed
on the same two tapes. Every setup, return-to-origin pass and join is charged. -/
theorem realizes_hoare {r s : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Shared50AffineCoefficients.Occurs s)
    (low high : List (Fin (c+1))) (hfull : (low++0::high).Perm (List.finRange (c+1)))
    (width : Fin (c+1) → ℕ) (ws : Fin (c+1) → List Bool)
    (hw : ∀ i, Counter.value (ws i) = width i) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (hvolume : P*(modulus b*B) = prime^PrefixAddressData.widthSum (low++0::high) width*(prime^(width 0)*D))
    (a : Fin (P*(modulus b*B)) → Fin 4) (hB : 0 < B) (hP : 0 < P) (hD : 0 < D)
    (bs qs ns ds es fs : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = modulus b) (hn : Counter.value ns = P)
    (hd : Counter.value ds = D) (he : Counter.value es = prime^(width 0))
    (hf : Counter.value fs = prime^PrefixAddressData.widthSum (low++0::high) width)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns) (cd : GrowingCounterData.Canonical ds)
    (ce : GrowingCounterData.Canonical es) (cf : GrowingCounterData.Canonical fs) :
    HoareTime (program hr s low high)
      (fun v => v = input hr s low high width hvolume a ws bs qs ns ds es fs)
      (fun v => v = output hr s low high width hvolume a ws bs qs ns ds es fs)
      ((2942+120*(r.num.natAbs+r.den)+4*c)*(P*(modulus b*B))+29*(c+1)+284) := by
  have hm := FlatAffineScalingPayload.realizes_hoare (radix := prime) hr a hB hP bs qs ns hb hq hn cb cq cn
  have hn := FlatControlledShiftReady.realizes_hoare s (Shared50AffineCoefficients.denominator_bound hs)
    low high hfull width ws hw cw hD (shiftedInput hr low high width hvolume a)
    (fun _ => blank) (fun _ => blank) 0 0 ds es fs hd he hf cd ce cf (by intros; rfl)
  have hh := SharedPayloadPair.pair_hoare hm hn
    (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r)
    (FlatAffineScalingPayload.slots_distinct r)
    (FlatControlledShiftPayload.sourceSlot c) (FlatControlledShiftPayload.destSlot c)
    (FlatControlledShiftPayload.slots_ne c) (handoff hr s low high width hvolume a ws bs qs ns ds es fs)
  apply hh.consequence ?_ (fun _ h => h) ?_
  · rintro v rfl
    unfold input SharedPayloadPair.input
    rw [FlatControlledShiftMetadata.strip_input_eq s (low++0::high) width ws _
      (shiftedInput hr low high width hvolume a)]
  · rw [← hvolume]
    exact le_of_eq (by ring)

end
end IntegerMultBounds.Machine.FlatScaleShiftPair
