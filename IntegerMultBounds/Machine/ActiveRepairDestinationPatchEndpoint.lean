import IntegerMultBounds.Machine.ActiveRepairDestinationPatchGeometry

/-! Full physical destination-rank endpoint, from the real short record counter.
The record's physical payload width is separate from this payload-one address. -/
namespace IntegerMultBounds.Machine.ActiveRepairDestinationPatchEndpoint
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankFieldsGeometry ActiveRepairDestinationPatchGeometry
open BinaryAddressTableData (row)

def headerValues (s : Shape) (w m before after rho : ℕ) : Fin 7 → ℕ :=
  ![0,s.bits+rho,targetStart s after,m,tStart s w m before after,w,uStart s w m before after]

variable (s : Shape) (w m before after rows rho : ℕ) (hw : w≤s.H)
variable (ha : before+m+after=s.active*s.chunk) (hp : s.payload=1) (hr : rows≤2^rho)
variable (x : Address s w m before after rows) (cs : List Bool)
variable (hc : Counter.value cs=(index s w m before after rows hw ha x).val)
variable (v : Fin (2^m)) (t u : Fin (2^w))

include hw ha hp hr hc in
 theorem runs (hs : Fin 7 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=headerValues s w m before after rho i)
    (hcan : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime ActiveRepairDestinationPatchRun.program
      (fun z => z=CleanSubbank.bank (s := 9)
        (ActiveRepairDestinationPatchRun.bank cs (row m v.val) (row w t.val) (row w u.val)
          (fun _ => blank) hs))
      (fun z => z=CleanSubbank.bank (s := 9)
        (ActiveRepairDestinationPatchRun.bank cs (row m v.val) (row w t.val) (row w u.val)
          (ActiveRepairDestinationPatchRun.word
            (encode s w m before after rows rho (replaced s w m before after rows x v t u))) hs))
      (800*(s.bits+rho+1)+3) := by
  have hf := fields_fit s w m before after rho hw ha
  have h := ActiveRepairDestinationPatchRun.runs_linear cs (row m v.val) (row w t.val) (row w u.val) hs
    (s.bits+rho) (targetStart s after) (tStart s w m before after) (uStart s w m before after)
    (hv 0) (hv 1) (hv 2) (by simpa [headerValues] using hv 3) (hv 4) (by simpa [headerValues] using hv 5) (hv 6)
    (by simp) (by simpa using hf.1) (by simpa using hf.2.1) (by simpa using hf.2.2) hcan
  rw [destination_eq_encode s w m before after rows rho hw ha hp hr x cs hc v t u] at h
  exact h

include hw ha hp hr hc in
 theorem generated_value :
    Counter.value (ActiveRepairDestinationPatchRun.destination cs (row m v.val) (row w t.val) (row w u.val)
      (s.bits+rho) (targetStart s after) (tStart s w m before after) (uStart s w m before after))=
        (index s w m before after rows hw ha (replaced s w m before after rows x v t u)).val :=
  destination_value s w m before after rows rho hw ha hp hr x cs hc v t u

include hw ha hp hr hc in
 theorem generated_word :
    ActiveRepairDestinationPatchRun.destination cs (row m v.val) (row w t.val) (row w u.val)
      (s.bits+rho) (targetStart s after) (tStart s w m before after) (uStart s w m before after)=
        row (s.bits+rho) (index s w m before after rows hw ha (replaced s w m before after rows x v t u)).val := by
  apply CountedPackedGuarded.word_eq_of_length_value
  · simp
  · rw [generated_value s w m before after rows rho hw ha hp hr x cs hc v t u]
    have hb := Counter.value_lt (encode s w m before after rows rho
      (replaced s w m before after rows x v t u))
    rw [encode_length s w m before after rows rho hw ha,
      encode_value s w m before after rows rho hw ha hp hr] at hb
    exact (BinaryAddressTableData.row_rank _ _ hb).symm

end
end IntegerMultBounds.Machine.ActiveRepairDestinationPatchEndpoint
