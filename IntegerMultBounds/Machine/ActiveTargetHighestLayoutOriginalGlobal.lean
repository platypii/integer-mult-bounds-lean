import IntegerMultBounds.Machine.ActiveTargetHighestLayoutGlobal
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalPlaced

/-! Original14-header physical highest-bit execution, expressed on the
literal original full-array type rather than a separately supplied rectangle. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalGlobal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters)
open ActiveTargetHighestPairData
open ActiveTargetHighestPairLayoutGeometry
open ActiveTargetHighestLayoutGlobal
open ActiveTargetHighestLayoutOriginalPlaced
open ActiveTargetHighestLayoutHeadersGeometry
open ActivePrefixLayoutHeadersGeometry (inputs)
open ActivePrefixDirtyControlConjugationData (FullArray)
open Networks.Shared50ModularControl (prime)
variable {t : ℕ}

theorem word_view {m n : ℕ} (h : m=n) (x : Fin m → Bool) :
    ActiveTargetRotation.word (a := prime) (view h x)=ActiveTargetRotation.word x := by subst n; rfl

theorem sources_view {m n : ℕ} (h : m=n) (hs : Fin 14 → List Bool) (x : Fin m → Bool) :
    sources hs (view h x)=sources hs x := by subst n; rfl

theorem earlier_runs (v : Tapes t prime) (focus : Fin 15 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (p : Parameters s) (offset rows : ℕ)
    (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset)
    (hH : 1≤s.H) (hr : 0<rows) (hrecord : s.bits+1≤s.payload)
    (hs : Fin 14 → List Bool) (array : FullArray s rows)
    (hsrc : SharedBank.payload v focus=sources hs array)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues (inputs s p offset rows) i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (earlierProgram focus hf)
      (fun w => w=CleanSubbank.bank (s := ActiveTargetHighestLayoutOriginalData.count) v)
      (fun w => w=CleanSubbank.bank (s := ActiveTargetHighestLayoutOriginalData.count)
        (SharedPlacementAlphabet.setTape v (focus 14)
          (ActiveTargetRotation.word (earlyAction s p offset rows hfit hsource hH hr (by omega) array)) 0))
      (ActiveTargetHighestLayoutOriginalRun.earlierCost (inputs s p offset rows)
        (early s p offset rows hfit hsource hH hr (by omega))) := by
  have hp : 0<s.payload := by omega
  let g := early s p offset rows hfit hsource hH hr hp
  let he := early_volume s p offset rows hfit hsource hH hr hp
  have ha : W g+6≤2*suffix g := ActiveTargetHighestPairBudget.absorbed g
    (by change ActiveTargetHighestPairBudget.bits g+1≤s.payload; rw [early_bits]; exact hrecord)
  have h := ActiveTargetHighestLayoutOriginalPlaced.earlier_runs v focus hf (inputs s p offset rows)
    (early_valid s p offset rows hfit hsource) g (early_values s p offset rows hfit hsource hH hr hp)
    hs (view he.symm array) (by rw [sources_view]; exact hsrc) hv hc ha
  simpa only [earlyAction,word_view] using h

theorem later_runs (v : Tapes t prime) (focus : Fin 15 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (p : Parameters s) (offset rows : ℕ)
    (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (hH : 1≤s.H) (hr : 0<rows) (hrecord : s.bits+1≤s.payload)
    (hs : Fin 14 → List Bool) (array : FullArray s rows)
    (hsrc : SharedBank.payload v focus=sources hs array)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues (inputs s p offset rows) i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (laterProgram focus hf)
      (fun w => w=CleanSubbank.bank (s := ActiveTargetHighestLayoutOriginalData.count) v)
      (fun w => w=CleanSubbank.bank (s := ActiveTargetHighestLayoutOriginalData.count)
        (SharedPlacementAlphabet.setTape v (focus 14)
          (ActiveTargetRotation.word (lateAction s p offset rows hfit hbefore hH hr (by omega) array)) 0))
      (ActiveTargetHighestLayoutOriginalRun.laterCost (inputs s p offset rows)
        (late s p offset rows hfit hbefore hH hr (by omega))) := by
  have hp : 0<s.payload := by omega
  let g := late s p offset rows hfit hbefore hH hr hp
  let he := late_volume s p offset rows hfit hbefore hH hr hp
  have ha : W g+6≤2*suffix g := ActiveTargetHighestPairBudget.absorbed g
    (by change ActiveTargetHighestPairBudget.bits g+1≤s.payload; rw [late_bits]; exact hrecord)
  have h := ActiveTargetHighestLayoutOriginalPlaced.later_runs v focus hf (inputs s p offset rows)
    (late_valid s p offset rows hfit hbefore) g (late_values s p offset rows hfit hbefore hH hr hp)
    hs (view he.symm array) (by rw [sources_view]; exact hsrc) hv hc ha
  have hw : ActiveTargetRotation.word (a := prime)
      (lateAction s p offset rows hfit hbefore hH hr hp array)=
      ActiveTargetRotation.word (later g (view he.symm array)) := word_view he _
  rw [hw]
  exact h

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalGlobal
