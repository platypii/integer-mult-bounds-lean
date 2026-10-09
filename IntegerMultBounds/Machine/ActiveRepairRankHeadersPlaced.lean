import IntegerMultBounds.Machine.ActiveRepairRankHeadersEndpoint

/-! Physical repair-header generation and erasure on arbitrary caller ports.
Ten originals and fifteen generated outputs are selected; all private native
storage returns blank, and arbitrary caller spectators retain tape and head. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankHeadersPlaced
noncomputable section
open ActiveRepairRankHeadersCommands ActiveRepairRankHeadersData
variable {a t : ℕ}

def ports : Fin 25 → Fin 43 := Fin.castAdd 18
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _

def installed (caller : Tapes t a) (focus : Fin 25 → Fin t) (v : Tapes 25 a) : Tapes t a :=
  ⟨fun i => if h : ∃ j, focus j=i then v.head h.choose else caller.head i,
   fun i => if h : ∃ j, focus j=i then v.tape h.choose else caller.tape i⟩

theorem installed_payload (caller : Tapes t a) (focus : Fin 25 → Fin t)
    (hf : Function.Injective focus) (v : Tapes 25 a) :
    SharedBank.payload (installed caller focus v) focus=v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [installed]
  all_goals split_ifs with h
  all_goals first | rw [hf h.choose_spec] | exact (h ⟨i,rfl⟩).elim

theorem installed_frame (caller : Tapes t a) (focus : Fin 25 → Fin t) (v : Tapes 25 a) :
    SharedBank.strip caller focus=SharedBank.strip (installed caller focus v) focus := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [installed]
  all_goals split_ifs <;> rfl

def sources (hs : Fin 10 → List Bool) :=
  SharedBank.payload (ActiveRepairRankHeadersRun.input (a := a) hs) ports
def outputs (side : SourceSide) (d : Widths) :=
  SharedBank.payload (bank (a := a) (finished side d)) ports

def result (caller : Tapes t a) (focus : Fin 25 → Fin t) (side : SourceSide) (d : Widths) :=
  installed caller focus (outputs side d)
def restored (caller : Tapes t a) (focus : Fin 25 → Fin t) (hs : Fin 10 → List Bool) :=
  installed caller focus (sources hs)
def program (side : SourceSide) (focus : Fin 25 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveRepairRankHeadersRun.program (a := a) side)
    (CleanSubbank.placement ports focus hf)
def cleanupProgram (focus : Fin 25 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveRepairRankHeadersRun.cleanupProgram (a := a))
    (CleanSubbank.placement ports focus hf)

private theorem strip_eq (v : Tapes 43 a)
    (hv : ∀ i : Fin 43, 25 ≤ i.val → v.head i=0 ∧ v.tape i=fun _ => blank) :
    SharedBank.strip v ports=SharedBank.empty 43 a := by
  have hex (i : Fin 43) : (∃ j, ports j=i) ↔ i.val<25 := by
    constructor
    · rintro ⟨j,rfl⟩; exact j.isLt
    · intro h; exact ⟨⟨i.val,h⟩,Fin.ext rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i.val<25
  all_goals simp only [hex,hi,↓reduceIte]
  · exact (hv i (by omega)).1
  · exact (hv i (by omega)).2

theorem input_clean (hs : Fin 10 → List Bool) :
    SharedBank.strip (ActiveRepairRankHeadersRun.input (a := a) hs) ports=SharedBank.empty 43 a := by
  apply strip_eq
  intro i hi
  fin_cases i <;> simp only at hi
  all_goals first | omega | exact ⟨rfl,rfl⟩

theorem output_clean (side : SourceSide) (d : Widths) :
    SharedBank.strip (bank (a := a) (finished side d)) ports=SharedBank.empty 43 a := by
  apply strip_eq
  intro i hi
  fin_cases i <;> simp only at hi
  all_goals first | omega | exact ⟨rfl,rfl⟩

theorem produces (caller : Tapes t a) (focus : Fin 25 → Fin t) (hf : Function.Injective focus)
    (side : SourceSide) (d : Widths) (hw : d.w≤d.H)
    (hs : Fin 10 → List Bool) (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hb : ∀ i, originalValues d i≤d.addressBits) :
    HoareTime (program side focus hf) (fun v => v=CleanSubbank.bank (s := 43) caller)
      (fun v => v=CleanSubbank.bank (s := 43) (result caller focus side d))
      (constant*(d.addressBits+1)) := by
  apply CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus side d)
    _ _ _ hsrc.symm
  · exact (installed_payload caller focus hf (outputs side d)).symm
  · exact input_clean hs
  · exact output_clean side d
  · exact installed_frame caller focus _
  · exact ActiveRepairRankHeadersRun.produces side d hw hs hv hc hb

theorem cleans (caller : Tapes t a) (focus : Fin 25 → Fin t) (hf : Function.Injective focus)
    (side : SourceSide) (d : Widths) (hs : Fin 10 → List Bool)
    (hsrc : SharedBank.payload caller focus=outputs side d)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hb : ∀ i, originalValues d i≤d.addressBits) :
    HoareTime (cleanupProgram focus hf) (fun v => v=CleanSubbank.bank (s := 43) caller)
      (fun v => v=CleanSubbank.bank (s := 43) (restored caller focus hs))
      (ActiveRepairRankHeadersRun.cleanupConstant*(d.addressBits+1)) := by
  apply CleanSubbank.realizes _ ports focus ports_injective hf caller (restored caller focus hs)
    _ _ _ hsrc.symm
  · exact (installed_payload caller focus hf (sources hs)).symm
  · exact output_clean side d
  · exact input_clean hs
  · exact installed_frame caller focus _
  · exact ActiveRepairRankHeadersRun.cleans side d hs hv hc hb

theorem frame (caller : Tapes t a) (focus : Fin 25 → Fin t) (side : SourceSide) (d : Widths)
    (i : Fin t) (hi : ¬∃ j, focus j=i) :
    (result caller focus side d).head i=caller.head i ∧
    (result caller focus side d).tape i=caller.tape i := by
  simp only [result,installed,hi,↓reduceDIte]
  exact ⟨trivial,trivial⟩

theorem restored_eq (caller : Tapes t a) (focus : Fin 25 → Fin t) (_hf : Function.Injective focus)
    (hs : Fin 10 → List Bool) (hsrc : SharedBank.payload caller focus=sources hs) :
    restored caller focus hs=caller := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals split_ifs with h
  · have he := congrFun (congrArg Tapes.head hsrc) h.choose
    simpa only [SharedBank.payload,h.choose_spec] using he.symm
  · rfl
  · have he := congrFun (congrArg Tapes.tape hsrc) h.choose
    simpa only [SharedBank.payload,h.choose_spec] using he.symm
  · rfl

theorem result_payload (caller : Tapes t a) (focus : Fin 25 → Fin t) (hf : Function.Injective focus)
    (side : SourceSide) (d : Widths) :
    SharedBank.payload (result caller focus side d) focus=outputs side d :=
  installed_payload caller focus hf _

theorem originals_retained (caller : Tapes t a) (focus : Fin 25 → Fin t)
    (hf : Function.Injective focus) (side : SourceSide) (d : Widths)
    (hs : Fin 10 → List Bool) (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (j : Fin 10) :
    (result caller focus side d).head (focus (Fin.castAdd 15 j))=caller.head (focus (Fin.castAdd 15 j)) ∧
    (result caller focus side d).tape (focus (Fin.castAdd 15 j))=caller.tape (focus (Fin.castAdd 15 j)) := by
  have hout := result_payload caller focus hf side d
  have he : (ActiveRepairRankHeadersRun.input (a := a) hs).head (ports (Fin.castAdd 15 j))=
      (bank (a := a) (finished side d)).head (ports (Fin.castAdd 15 j)) ∧
      (ActiveRepairRankHeadersRun.input (a := a) hs).tape (ports (Fin.castAdd 15 j))=
      (bank (a := a) (finished side d)).tape (ports (Fin.castAdd 15 j)) := by
    have h := ActiveRepairRankHeadersEndpoint.originals_retained (a := a) side d hs hv hc j
    fin_cases j <;> exact ⟨h.2.symm,h.1.symm⟩
  have hoh := congrFun (congrArg Tapes.head hout) (Fin.castAdd 15 j)
  have hot := congrFun (congrArg Tapes.tape hout) (Fin.castAdd 15 j)
  have hih := congrFun (congrArg Tapes.head hsrc) (Fin.castAdd 15 j)
  have hit := congrFun (congrArg Tapes.tape hsrc) (Fin.castAdd 15 j)
  exact ⟨hoh.trans (he.1.symm.trans hih.symm),hot.trans (he.2.symm.trans hit.symm)⟩

end
end IntegerMultBounds.Machine.ActiveRepairRankHeadersPlaced
