import IntegerMultBounds.Machine.CompactNativeRoleConjugatedCaller
import IntegerMultBounds.Machine.CompactNativeRoleConjugatedOutput
import IntegerMultBounds.Machine.CompactNativeRoleGuardedChildCaller
import IntegerMultBounds.Machine.NativePolynomialStageHeaderBudget

/-! Original numeric43 role headers physically synthesize the native codec,
execute a genuine conjugated phase, and restore all original metadata. The
prime-alphabet output is exactly a mapped six-symbol role bank, so actual
lifted binary restoration executes without a conversion or phase callback. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleConjugatedLifecycle
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageFullData (Inputs)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleSourcePorts (external callerTapes)
open CompactNativeRoleConjugatedPorts (encoding)
open CompactNativeRoleConjugatedCaller (order outputCoefficients output_width)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count)
variable {t c : ℕ} {s : Shape}

abbrev privateTapes := CompactNativeConjugatedHeaderBank.tapes

def rawState (v : Stage s) (rows ell p : ℕ) :=
  CompactSpectatorLeafSetup.raw s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val

def preparedState (v : Stage s) (rows ell p : ℕ) :=
  NativePolynomialStageHeaders.prepared s rows ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val

def caller (old : Tapes t 2) (ht : 43<t) (v : Stage s) (rows ell p : ℕ) (payload : Tapes (1+c) 2) :=
  Alphabet.mapTapes encoding (external old ht (rawState v rows ell p) payload)

theorem input_slots (v : Stage s) (rows ell p : ℕ)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows) :
    (NativePolynomialStageShape.inputs v rows ell p hG hGK hr).stage.slots=v.slots := rfl

def resultPayload (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i k,(xs i k).1.length=w ∧ (xs i k).2.length=w)
    (payload : Tapes (1+c) 2) (j : Fin c) :=
  SharedPlacementAlphabet.setTape payload (CompactNativeRoleConjugatedOutput.roleSlot j)
    (SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
      (rows d (outputCoefficients d hslots pc ell xs) (output_width d hslots pc ell w xs hw))))) 0

/-- The retained original source and its head survive the selected role update. -/
theorem result_source_unchanged (old : Tapes t 2) (ht : 43<t)
    (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i k,(xs i k).1.length=w ∧ (xs i k).2.length=w)
    (payload : Tapes (1+c) 2) (j : Fin c) :
    CompactNativeRoleSourcePorts.replaceSource old ht (resultPayload d hslots pc ell w xs hw payload j)=
      CompactNativeRoleSourcePorts.replaceSource old ht payload :=
  CompactNativeRoleConjugatedOutput.source_unchanged old ht payload j _ 0

/-- Every other role or retained source tape, including its head, is unchanged. -/
theorem result_frame (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i k,(xs i k).1.length=w ∧ (xs i k).2.length=w)
    (payload : Tapes (1+c) 2) (j : Fin c) (i : Fin (1+c))
    (hi : i≠CompactNativeRoleConjugatedOutput.roleSlot j) :
    (resultPayload d hslots pc ell w xs hw payload j).head i=payload.head i ∧
    (resultPayload d hslots pc ell w xs hw payload j).tape i=payload.tape i := by
  simp only [resultPayload,SharedPlacementAlphabet.setTape,Function.update_of_ne hi,and_self]


def program {q : ℕ} (P : Program ActivePrefixStageNative.tapes q prime)
    (t c : ℕ) (j : Fin c) (order : ActivePrefixStageHeadersData.Order) (pc : Fin count) :=
  seq (extend (Alphabet.program encoding (CompactNativeRoleGuardedChildCaller.payloadProgram t c)) privateTapes)
    (seq (CompactNativeRoleConjugatedPorts.program P t c j order pc)
      (extend (Alphabet.program encoding (CompactNativeRoleGuardedChildCaller.payloadRestore t c)) privateTapes))

def cost (v : Stage s) (rowsCount ell p phaseTime : ℕ) :=
  NativePolynomialStageHeaders.cost s rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val+
    phaseTime+ButterflyAxisHeadersArithmetic.scheduleCost NativePolynomialStageHeaders.restore
      (preparedState v rowsCount ell p)+2

private theorem numeric {q : ℕ} (M : Program 43 q 2) (old : Tapes t 2) (ht : 43<t)
    (st su : State) (payload : Tapes (1+c) 2) (time : ℕ)
    (h : HoareTime M (fun v => v=ActiveRepairRankHeadersCommands.bank st)
      (fun v => v=ActiveRepairRankHeadersCommands.bank su) time) :
    HoareTime (Placement.placed M (CompactNativeRoleChildHeadersPorts.placement t c))
      (fun v => v=external old ht st payload) (fun v => v=external old ht su payload) time := by
  have hh := Placement.hoare_at h (CompactNativeRoleChildHeadersPorts.placement t c)
    (external old ht st payload) (CompactNativeRoleChildHeadersPorts.active old ht st payload)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,CompactNativeRoleChildHeadersPorts.extra old ht st su payload,
    ←CompactNativeRoleChildHeadersPorts.active old ht su payload,Placement.view]

private theorem lifted {n q time : ℕ} {M : Program n q 2} {v w : Tapes n 2}
    (h : HoareTime M (fun z => z=v) (fun z => z=w) time) :
    HoareTime (Alphabet.program encoding M) (fun z => z=Alphabet.mapTapes encoding v)
      (fun z => z=Alphabet.mapTapes encoding w) time := by
  apply (Alphabet.map_hoare encoding h).consequence _ _ le_rfl
  · rintro z rfl; exact ⟨_,rfl,rfl⟩
  · rintro z ⟨_,rfl,rfl⟩; rfl

/-- All metadata synthesis and restoration starts with original role headers.
The only geometric side condition is genuine packed repair readiness. -/
theorem exists_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    ∀ (t c : ℕ) (old : Tapes t 2) (ht : 43<t) (payload : Tapes (1+c) 2) (j : Fin c)
      (s : Shape) (v : Stage s) (rowsCount ell p : ℕ)
      (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rowsCount)
      (_hpay : s.payload=1) (hslots : v.slots=25^3) (pc : Fin count)
      (hp : ∀ op,1<(NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr).stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr)) → Fin (2^ell) → Coefficient)
      (hw : ∀ i k,(xs i k).1.length=NativePolynomialStageShape.width s p ∧
        (xs i k).2.length=NativePolynomialStageShape.width s p)
      (_hword : payload.tape ⟨j.val+1,by omega⟩=SymbolTripleClean.word
        (List.ofFn (ActivePrefixStageNativeRows.flat
          (rows (NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr) xs hw))))
      (_hhead : payload.head ⟨j.val+1,by omega⟩=0),
      let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
      let hslotsD := (input_slots v rowsCount ell p hG hGK hr).trans hslots
      let out := resultPayload d hslotsD pc ell (NativePolynomialStageShape.width s p) xs hw payload j
      let phaseTime := CompactNativeConjugatedSharedCaller.cost (callerTapes t c) d ell
        (CompactNativeConjugatedPhaseFamily.cost D d hslotsD (order v) pc ell (NativePolynomialStageShape.width s p) hp)
      HoareTime (program P t c j (order v) pc)
        (fun z => z=(caller old ht v rowsCount ell p payload).append (FixedHeaderBankCopy.empty privateTapes))
        (fun z => z=(caller old ht v rowsCount ell p out).append (FixedHeaderBankCopy.empty privateTapes))
        (cost v rowsCount ell p phaseTime) ∧
      (cost v rowsCount ell p phaseTime : ℝ)≤C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactNativeRoleConjugatedCaller.exists_program D
  refine ⟨q,P,C+NativePolynomialStageHeaderBudget.constant+2,by positivity,?_⟩
  intro t c old ht payload j s v rowsCount ell p hG hGK hr hpay hslots pc hp xs hw hword hhead
  let d := NativePolynomialStageShape.inputs v rowsCount ell p hG hGK hr
  have hslotsD : d.stage.slots=25^3 := (input_slots v rowsCount ell p hG hGK hr).trans hslots
  let out := resultPayload d hslotsD pc ell (NativePolynomialStageShape.width s p) xs hw payload j
  have hA : 0<s.axes := lt_of_lt_of_le v.positiveWidth v.widthFits
  have hK : 0<s.chunk := lt_of_le_of_lt (Nat.zero_le _) v.selectedFits
  have hG' : 0<s.guard := hG
  have hsetup := hoare_extend_eq (lifted (numeric _ old ht _ _ payload _
    (NativePolynomialStageHeaders.runs (a:=2) s rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val hG' hA hK)))
    (FixedHeaderBankCopy.empty privateTapes)
  obtain ⟨hphase,hbound⟩ := hP t c old ht payload j s v rowsCount ell p hG hGK hr hslots pc hp xs hw hword hhead
  have hphase' := hphase.consequence (fun _ hz => hz)
    (fun _ hz => by rwa [CompactNativeRoleConjugatedOutput.installed_word] at hz) le_rfl
  have hrestore := hoare_extend_eq (lifted (numeric _ old ht _ _ out _
    (NativePolynomialStageHeaders.restore_runs (a:=2) s rowsCount ell p v.rho v.left v.f v.slots v.right v.source.val v.target.val)))
    (FixedHeaderBankCopy.empty privateTapes)
  constructor
  · exact (hsetup.seq (hphase'.seq hrestore)).consequence (fun _ hz => hz) (fun _ hz => hz)
      (by unfold cost preparedState; omega)
  · have hlife := NativePolynomialStageHeaderBudget.lifecycle_linear v rowsCount ell p hr hA hG' hK hpay
    have hvol := NativePolynomialStageHeaderBudget.expanded_volume s rowsCount ell p
    have hvolume := CompactNativeConjugatedPhaseFamily.volume_le_scale d
    have hsmall : (CompactNativeRoleTransferBudget.volume rowsCount s ell p : ℝ)≤ActivePrefixStageInverseBudget.scale d := by
      have hn : CompactNativeRoleTransferBudget.volume rowsCount s ell p≤
          rowsCount*(NativePolynomialStageShape.shape s ell p).recordWidth := by omega
      exact (Nat.cast_le.mpr hn).trans hvolume
    have hlifeR := Nat.cast_le (α:=ℝ).mpr hlife
    push_cast at hlifeR
    have hpayR := mul_le_mul_of_nonneg_left hsmall
      (Nat.cast_nonneg NativePolynomialStageHeaderBudget.constant : (0 : ℝ)≤NativePolynomialStageHeaderBudget.constant)
    have hunit := ActivePrefixStageInverseBudget.one_le_scale d
    unfold cost preparedState
    push_cast
    dsimp only [d] at hbound hpayR hunit
    linarith only [hlifeR,hpayR,hbound,hunit]

end
end IntegerMultBounds.Machine.CompactNativeRoleConjugatedLifecycle
