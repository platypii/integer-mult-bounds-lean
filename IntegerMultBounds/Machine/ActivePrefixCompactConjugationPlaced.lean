import IntegerMultBounds.Machine.ActivePrefixCompactConjugationSemantics
import IntegerMultBounds.Machine.ActivePrefixCompactConjugationBudget

/-! Both complete physical compact conjugations on arbitrary caller tapes.
Nineteen ports retain all eighteen prepared input words and change only the
full array; every private tape starts and returns blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactConjugationPlaced
noncomputable section
open ActivePrefixCompactConjugationData ActivePrefixCompactConjugationLayout
open ActivePrefixCompactConjugationMiddle (bank)
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

abbrev count (kind : Kind) := 19+swapCount+privateCount kind
def ports (kind : Kind) (i : Fin 19) := Fin.castAdd (privateCount kind) (Fin.castAdd swapCount i)
theorem ports_injective (kind : Kind) : Function.Injective (ports kind) :=
  (Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)

def program (kind : Kind) (focus : Fin 19 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixCompactConjugationRun.program kind) (CleanSubbank.placement (ports kind) focus hf)
def result {m : ℕ} (caller : Tapes t prime) (focus : Fin 19 → Fin t) (x : Fin m → Bool) :=
  setTape caller (focus 18) (ActiveTargetRotation.word x) 0

theorem native_payload (kind : Kind) (v : Tapes 19 prime) :
    SharedBank.payload (bank kind v) (ports kind)=v := by
  change SharedBank.payload ((v.append (SharedBank.empty swapCount prime)).append
    (SharedBank.empty (privateCount kind) prime))
    (fun i => Fin.castAdd (privateCount kind) (Fin.castAdd swapCount i))=_
  rw [SharedBankFrames.payload_append_left,SharedBankFrames.payload_append_left]
  rfl

theorem native_clean (kind : Kind) (v : Tapes 19 prime) :
    SharedBank.strip (bank kind v) (ports kind)=SharedBank.empty (count kind) prime := by
  change SharedBank.strip ((v.append (SharedBank.empty swapCount prime)).append
    (SharedBank.empty (privateCount kind) prime))
    (fun i => Fin.castAdd (privateCount kind) (Fin.castAdd swapCount i))=_
  rw [SharedBankFrames.strip_append_left,SharedBankFrames.strip_append_left]
  have h : SharedBank.strip v (fun i : Fin 19 => i)=SharedBank.empty 19 prime := by
    apply congrArg₂ Tapes.mk
    · funext i; simp
    · funext i; simp
  rw [h,SharedBankFrames.empty_append,SharedBankFrames.empty_append]

theorem native_output (kind : Kind) {m n : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    bank kind (base gs bw hs rs bs y)=setTape (bank kind (base gs bw hs rs bs x))
      (ports kind 18) (ActiveTargetRotation.word y) 0 := by
  change ((base gs bw hs rs bs y).append (SharedBank.empty swapCount prime)).append
    (SharedBank.empty (privateCount kind) prime) =
    setTape (((base gs bw hs rs bs x).append (SharedBank.empty swapCount prime)).append
      (SharedBank.empty (privateCount kind) prime))
      (Fin.castAdd (privateCount kind) (Fin.castAdd swapCount (18 : Fin 19))) _ 0
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,base_set]

theorem runs (kind : Kind) (side : Side) (caller : Tapes t prime) (focus : Fin 19 → Fin t)
    (hf : Function.Injective focus) (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤sourceRoom side s p) (rows : ℕ) (hrows : 0<rows)
    (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hrecord : s.bits+1≤s.payload)
    (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s p.n rows i)
    (gc : ∀ i, GrowingCounterData.Canonical (gs i))
    (gb : Counter.value bw=p.b) (cb : GrowingCounterData.Canonical bw)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixParityOnlyBank.values (shape side s p offset hfit) i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=suffix s p) (cs : GrowingCounterData.Canonical bs)
    (x : ActivePrefixCompactSwapData.Array s rows (p.n*p.b))
    (hsrc : SharedBank.payload caller focus=base gs bw hs rs bs x) :
    HoareTime (program kind focus hf) (fun v => v=CleanSubbank.bank (s := count kind) caller)
      (fun v => v=CleanSubbank.bank (s := count kind) (result caller focus
        (ActivePrefixCompactConjugationRun.result kind s (shape side s p offset hfit) rows (p.n*p.b)
          (suffix s p) (alignment side s p offset hfit rows) x)))
      (ActivePrefixCompactConjugationRun.cost kind s rows (p.n*p.b)) := by
  refine CleanSubbank.realizes _ (ports kind) focus (ports_injective kind) hf caller (result caller focus _)
    _ _ _ ?_ ?_ (native_clean kind _) (native_clean kind _) ?_
    (ActivePrefixCompactConjugationLayout.runs kind side s p offset hfit rows hrows hK hd hg hrecord
      gs bw hs rs bs gv gc gb cb hv hc hr cr hb cs x)
  · rw [native_payload,hsrc]
  · rw [native_output kind gs bw hs rs bs x]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ (ports_injective kind),
      CompactGadgetReservationPlacement.payload_set _ _ hf,native_payload,hsrc]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem frame {m : ℕ} (caller : Tapes t prime) (focus : Fin 19 → Fin t) (x : Fin m → Bool)
    (i : Fin t) (hi : i≠focus 18) :
    (result caller focus x).head i=caller.head i ∧ (result caller focus x).tape i=caller.tape i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixCompactConjugationPlaced
