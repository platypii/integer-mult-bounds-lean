import IntegerMultBounds.Machine.ActivePrefixCompactConjugationData

/-! Concrete pure and negative load branches on the same caller geometry.
The surrounding interchange workspace is framed, and each load's complete
private workspace is clean at both endpoints. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactConjugationMiddle
noncomputable section
open ActivePrefixCompactConjugationData
open ActivePrefixParityOnlyBank (Shape values)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)

def focus (i : Fin 11) : Fin (19+swapCount) := Fin.castAdd swapCount (loadFocus i)
theorem focus_injective : Function.Injective focus := (Fin.castAdd_injective _ _).comp load_injective

def stateCount {t k : ℕ} (_ : Program t k prime) := k
def states : Kind → ℕ
  | .parity => stateCount (ActivePrefixCompactParityLoadPlaced.program (a := prime) focus focus_injective)
  | .negative => stateCount (ActivePrefixCompactNegativeLoadPlaced.program (a := prime) focus focus_injective)

def program : (kind : Kind) → Program (19+swapCount+privateCount kind) (states kind) prime
  | .parity => ActivePrefixCompactParityLoadPlaced.program focus focus_injective
  | .negative => ActivePrefixCompactNegativeLoadPlaced.program focus focus_injective

def middleBank (caller : Tapes 19 prime) := CleanSubbank.bank (s := swapCount) caller
def bank (kind : Kind) (caller : Tapes 19 prime) := CleanSubbank.bank (s := privateCount kind) (middleBank caller)

theorem sources (s : Shape) (rows B : ℕ) (gs : Fin 7 → List Bool) (b : List Bool)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : ActivePrefixCompactParityLoadData.Array s rows B) :
    SharedBank.payload (middleBank (base gs b hs rs bs x)) focus=loadSources s rows B hs rs bs x := by
  change SharedBank.payload ((base gs b hs rs bs x).append (SharedBank.empty swapCount prime))
    (fun i => Fin.castAdd swapCount (loadFocus i))=_
  rw [SharedBankFrames.payload_append_left,load_sources]

theorem output (kind : Kind) (s : Shape) (rows B : ℕ) (gs : Fin 7 → List Bool) (b : List Bool)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : ActivePrefixCompactParityLoadData.Array s rows B) :
    setTape (middleBank (base gs b hs rs bs x)) (focus 10) (ActiveTargetRotation.word (loadResult kind s rows B x)) 0=
      middleBank (base gs b hs rs bs (loadResult kind s rows B x)) := by
  change setTape ((base gs b hs rs bs x).append (SharedBank.empty swapCount prime))
    (Fin.castAdd swapCount (18 : Fin 19)) _ 0=_
  rw [SharedPlacementAlphabet.setTape_append_left,base_set]
  rfl

theorem runs (kind : Kind) (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (habs : s.W+1≤2^(s.n*s.b)*B) (gs : Fin 7 → List Bool) (b : List Bool)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : ActivePrefixCompactParityLoadData.Array s rows B)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program kind) (fun v => v=bank kind (base gs b hs rs bs x))
      (fun v => v=bank kind (base gs b hs rs bs (loadResult kind s rows B x)))
      (constant kind*ActivePrefixCompactParityLoadData.volume s rows B) := by
  cases kind with
  | parity =>
    have h := ActivePrefixCompactParityLoadPlaced.runs (middleBank (base gs b hs rs bs x)) focus focus_injective
      s rows B hrows hB habs hs rs bs x (sources s rows B gs b hs rs bs x) hv hc hr cr hb cb
    change HoareTime _ _ (fun v => v=CleanSubbank.bank (s := 60)
      (setTape _ (focus 10) (ActiveTargetRotation.word (loadResult .parity s rows B x)) 0)) _ at h
    rw [output] at h
    exact h
  | negative =>
    have h := ActivePrefixCompactNegativeLoadPlaced.runs (middleBank (base gs b hs rs bs x)) focus focus_injective
      s rows B hrows hB habs hs rs bs x
      (by rw [negative_sources]; exact sources s rows B gs b hs rs bs x) hv hc hr cr hb cb
    change HoareTime _ _ (fun v => v=CleanSubbank.bank (s := 75)
      (setTape _ (focus 10) (ActiveTargetRotation.word (loadResult .negative s rows B x)) 0)) _ at h
    rw [output] at h
    exact h

end
end IntegerMultBounds.Machine.ActivePrefixCompactConjugationMiddle
