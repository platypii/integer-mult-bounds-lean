import IntegerMultBounds.Machine.ActiveRepairEarlyKeyData

/-! One fixed machine computes a conditional full early-repair key from the
genuine short original rank, then erases all nine generated caller words. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyRun
noncomputable section
open ActiveRepairEarlyKeyData
open ActiveRepairEarlyKeyData.Data
open ActiveRepairRankFieldsBank (offsetSlot widthSlot)

structure Valid (d : Data) : Prop where
  hv0 : ∀ i, Counter.value (d.hs (offsetSlot i))=d.starts i
  hv1 : ∀ i, Counter.value (d.hs (widthSlot i))=d.widths i
  hc : ∀ i, GrowingCounterData.Canonical (d.hs i)
  hbq3 : d.b+3≤d.q
  hwidth : d.widths 3=d.f*d.q
  hV : d.widths 0=d.n*d.q
  hT : d.widths 1=d.n*d.b
  hU : d.widths 2=d.n*d.b
  hnf : d.n+1=d.f
  hr : d.rho<d.q
  sv : ∀ i, Counter.value (d.ss i)=SelectedSourceBitsRun.values d.q d.n d.rho d.f i
  sc : ∀ i, GrowingCounterData.Canonical (d.ss i)
  bv : Counter.value d.bs=d.b
  bc : GrowingCounterData.Canonical d.bs
  hfit : ∀ i, d.starts i+d.widths i≤d.A
  pz : Counter.value (d.ph 0)=0
  pA : Counter.value (d.ph 1)=d.A
  psv : Counter.value (d.ph 2)=d.sv
  pv : Counter.value (d.ph 3)=d.widths 0
  pst : Counter.value (d.ph 4)=d.st
  pt : Counter.value (d.ph 5)=d.widths 1
  psu : Counter.value (d.ph 6)=d.su
  pc : ∀ i, GrowingCounterData.Canonical (d.ph i)
  fv : d.sv+d.widths 0≤d.A
  ft : d.st+d.widths 1≤d.A
  fu : d.su+d.widths 2≤d.A

theorem lengths (d : Data) (h : Valid d) :
    d.target.length=d.widths 0 ∧ d.recoveredT.length=d.widths 1 ∧
    d.U.length=d.recoveredT.length := by
  have hz : d.Z.length=d.n := SelectedSourceBitsData.selected_length _ _ _ _
  have hv : d.V.length=d.Z.length*d.q := by simp [V,hz,h.hV]
  have ht : d.T.length=d.Z.length*d.b := by simp [T,hz,h.hT]
  rcases PackedInverse.lengths d.q d.b d.hb d.hbq d.V d.T d.Z hv ht with
    ⟨_,_,_,_,_,_,_,hw,_,hv'⟩
  have ht' : d.target.length=d.widths 0 := by
    rw [target,CountedIdealToggle.word_length _ _ d.Z (by have := d.hbq; omega) hv',hv',hz,h.hV]
  have hw' : d.recoveredT.length=d.widths 1 := by simpa [recoveredT,hz,h.hT] using hw
  exact ⟨ht',hw',by simp [U,hw',h.hU,h.hT]⟩

def sourceProgram := ActiveRepairEarlyKeyPlacement.program (s := 30)
  ActiveRepairEarlySourceRun.program sourceFocus source_injective
def patchProgram := ActiveRepairEarlyKeyPatch.program patchFocus patch_injective
def appendProgram := ActiveRepairEarlyKeyAppend.program appendFocus append_injective
def program := seq (seq (seq sourceProgram patchProgram) appendProgram)
  ActiveRepairEarlyKeyCleanup.program

theorem source_runs (d : Data) (h : Valid d) :
    HoareTime sourceProgram (fun z => z=CleanSubbank.bank (s := 52) d.input)
      (fun z => z=CleanSubbank.bank (s := 52) d.computed) (27600*(d.A+1)+5) := by
  have hh := ActiveRepairEarlySourceRun.runs_linear d.cs d.starts d.widths d.hs d.ss d.bs
    h.hv0 h.hv1 h.hc d.q d.b d.rho d.n d.f d.A d.hb d.hbq h.hbq3 h.hwidth h.hV h.hT
    h.hnf h.hr h.sv h.sc h.bv h.bc h.hfit
  have hp := ActiveRepairEarlyKeyPlacement.runs (c := 22) (s := 30)
    ActiveRepairEarlySourceRun.program d.input sourceFocus source_injective
    d.sourceInput d.sourceOutput _ (source_payload d) hh
  have he : ActiveRepairEarlyKeyPlacement.install d.input sourceFocus d.sourceOutput=d.computed :=
    ActiveRepairEarlyKeyPlacement.install_append _ _ _
  rw [he] at hp
  exact hp

theorem patch_runs (d : Data) (h : Valid d) :
    HoareTime patchProgram (fun z => z=CleanSubbank.bank (s := 52) d.computed)
      (fun z => z=CleanSubbank.bank (s := 52) d.patched) (800*(d.A+1)+3) := by
  obtain ⟨hv,ht,hu⟩ := lengths d h
  have hp := ActiveRepairEarlyKeyPatch.runs d.computed patchFocus patch_injective
    d.cs d.target d.recoveredT d.U d.ph (patch_payload d) d.A d.sv d.st d.su
    h.pz h.pA h.psv (by rw [hv]; exact h.pv) h.pst (by rw [ht]; exact h.pt) h.psu hu
    (by rw [hv]; exact h.fv) (by rw [ht]; exact h.ft) (by simpa [U] using h.fu) h.pc
  change HoareTime patchProgram _ (fun z => z=CleanSubbank.bank (s := 52)
    (ActiveRepairEarlyKeyPlacement.install d.computed patchFocus
      (ActiveRepairDestinationPatchRun.bank d.cs d.target d.recoveredT d.U
        (ActiveRepairDestinationPatchRun.word d.destination) d.ph))) _ at hp
  rw [patched_install] at hp
  exact hp

theorem append_runs (d : Data) :
    HoareTime appendProgram (fun z => z=CleanSubbank.bank (s := 52) d.patched)
      (fun z => z=CleanSubbank.bank (s := 52) d.written) (3*d.A+18) := by
  have hp := ActiveRepairEarlyKeyAppend.runs d.patched appendFocus append_injective
    d.flag d.destination (append_payload d)
  rw [written_install] at hp
  simpa only [appendProgram,destination,ActiveRepairDestinationPatchRun.destination_length] using hp

theorem cleanup_cost (d : Data) (h : Valid d) :
    ActiveRepairEarlyKeyCleanup.cost ActiveRepairEarlyKeyCleanup.slots d.words≤100*(d.A+1) := by
  have hv := h.hfit 0
  have ht := h.hfit 1
  have hu := h.hfit 2
  have hx := h.hfit 3
  have hz : d.Z.length≤d.A := by
    rw [Z,SelectedSourceBitsData.selected_length]
    have hq : 0<d.q := by have := d.hbq; omega
    have hnq : d.n*d.q≤d.A := by rw [h.hV] at hv; omega
    exact (Nat.le_mul_of_pos_right d.n hq).trans hnq
  obtain ⟨hvl,htl,_⟩ := lengths d h
  have hd : d.destination.length=d.A := ActiveRepairDestinationPatchRun.destination_length _ _ _ _ _ _ _ _
  simp only [ActiveRepairEarlyKeyCleanup.cost,ActiveRepairEarlyKeyCleanup.slots,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,words]
  norm_num only [Fin.reduceEq,ite_true,ite_false,List.length_singleton]
  simp only [V,T,U,X,Gather.field_length] at *
  omega

theorem runs_linear (d : Data) (h : Valid d) :
    HoareTime program (fun z => z=CleanSubbank.bank (s := 52) d.input)
      (fun z => z=CleanSubbank.bank (s := 52) d.output) (29000*(d.A+1)) := by
  have hc := ActiveRepairEarlyKeyCleanup.runs_shared d.written d.words
    (cleanup_tapes d) (cleanup_heads d)
  rw [cleanup_output] at hc
  have hh := (((source_runs d h).seq (patch_runs d h)).seq (append_runs d)).seq hc
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by have := cleanup_cost d h; omega)

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyRun
