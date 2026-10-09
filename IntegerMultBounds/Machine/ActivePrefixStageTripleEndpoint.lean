import IntegerMultBounds.Machine.ActivePrefixStageTripleTransport
import IntegerMultBounds.Machine.ActivePrefixStageRuntimeInverseRun

/-! The complete all-width stage returns an explicit literal native-symbol
encoding, including arbitrary spectators. The output representation is derived
from the actual destination action, rather than supplied as a codec premise. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageTripleEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixDirtyControlGlobalSwap (index)
open ActivePrefixStageRuntimeSelected (destination)
open ActivePrefixStageRuntimeData (result)
open ActivePrefixStageTripleTransport
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape} {B K : ℕ}

/-- Address involution follows from the proved involution of the actual array
endpoint, using a distinguishing Boolean array. -/
theorem destination_involutive (d : Inputs s) : Function.Involutive (destination d) := by
  intro i
  let x : Array s d.rows := fun k => decide (k=index s (geometry d) i)
  have h1 := ActivePrefixStageRuntimeSelected.entry d x i
  have h2 := ActivePrefixStageRuntimeSelected.entry d (result d x) (destination d i)
  rw [ActivePrefixStageRuntimeInverseRun.involutive d x] at h2
  have he : x (index s (geometry d) (destination d (destination d i)))=true := by
    rw [h2,h1]
    simp [x]
  have hk : index s (geometry d) (destination d (destination d i))=index s (geometry d) i :=
    of_decide_eq_true he
  exact (equiv d).injective hk

theorem pullback (d : Inputs s) (x : Array s d.rows) (i : Address d) :
    result d x (index s (geometry d) i)=x (index s (geometry d) (destination d i)) := by
  have h := ActivePrefixStageRuntimeSelected.entry d x (destination d i)
  rw [destination_involutive d i] at h
  exact h

theorem destination_base (d : Inputs s) (i : Address d) :
    destination d (base d i)=base d (destination d i) := destination_payload d i _

theorem destination_payload_eq (d : Inputs s) (i : Address d) :
    (destination d i).payload=i.payload := by
  have h := congrArg CompactActiveTargetLayout.Address.payload (ActivePrefixStageRuntimeSelected.fields d i)
  exact h

/-- Exact whole-array output representation. It includes the same arbitrary
spectator words transported by the original address action. -/
theorem result_encoded (d : Inputs s) (h : s.payload=B*3+K)
    (xs : Address d → Fin B → Fin 6) (tail : Address d → Fin K → Bool) :
    result d (encodedArray d h xs tail)=
      encodedArray d h (xs ∘ destination d) (tail ∘ destination d) := by
  funext k
  have hi : index s (geometry d) ((equiv d).symm k)=k := (equiv d).apply_symm_apply k
  rw [←hi,pullback,encoded_entry,encoded_entry]
  rw [destination_payload_eq,←destination_base]
  rfl

/-- The fixed physical stage returns the derived encoded endpoint with the
same certified stage cost; no output word or branch result is supplied. -/
theorem runs (D : ℕ) (d : Inputs s) (h : s.payload=B*3+K)
    (xs : Address d → Fin B → Fin 6) (tail : Address d → Fin K → Bool)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D) :
    HoareTime ActivePrefixStageRuntimeProgram.program
      (fun v => v=ActivePrefixStageRuntimeProgram.bank d (encodedArray d h xs tail))
      (fun v => v=ActivePrefixStageRuntimeProgram.bank d
        (encodedArray d h (xs ∘ destination d) (tail ∘ destination d)))
      (ActivePrefixStageRuntimeData.cost D d hp) := by
  have hr := ActivePrefixStageRuntimeRun.runs D d (encodedArray d h xs tail) hp
  rw [result_encoded] at hr
  exact hr

/-- Nonblank native coefficient interiors remain nonblank at every actual
output address, which supplies the physical decoder's rewind prerequisite. -/
theorem result_native_nonblank (d : Inputs s)
    (xs : Address d → Fin B → Fin 6) (hn : ∀ i j,xs i j≠blank) :
    ∀ i j,(xs ∘ destination d) i j≠blank := by
  intro i j
  exact hn (destination d i) j

end
end IntegerMultBounds.Machine.ActivePrefixStageTripleEndpoint
