import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersEndpoint

/-! Physical repair-header generation and erasure on arbitrary caller ports.
Fourteen originals and ten generated outputs are selected; all private native
storage returns blank, and arbitrary caller spectators retain tape and head. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutHeadersPlaced
noncomputable section
open ActiveRepairRankHeadersCommands ActivePrefixLayoutHeadersData
variable {a t : ℕ}

def ports : Fin 24 → Fin 43 := Fin.castAdd 19
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _

def installed (caller : Tapes t a) (focus : Fin 24 → Fin t) (v : Tapes 24 a) : Tapes t a :=
  ⟨fun i => if h : ∃ j, focus j=i then v.head h.choose else caller.head i,
   fun i => if h : ∃ j, focus j=i then v.tape h.choose else caller.tape i⟩

theorem installed_payload (caller : Tapes t a) (focus : Fin 24 → Fin t)
    (hf : Function.Injective focus) (v : Tapes 24 a) :
    SharedBank.payload (installed caller focus v) focus=v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [installed]
  all_goals split_ifs with h
  all_goals first | rw [hf h.choose_spec] | exact (h ⟨i,rfl⟩).elim

theorem installed_frame (caller : Tapes t a) (focus : Fin 24 → Fin t) (v : Tapes 24 a) :
    SharedBank.strip caller focus=SharedBank.strip (installed caller focus v) focus := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [installed]
  all_goals split_ifs <;> rfl

def sources (hs : Fin 14 → List Bool) :=
  SharedBank.payload (ActivePrefixLayoutHeadersEndpoint.input (a := a) hs) ports
def outputs (mode : Mode) (d : Inputs) :=
  SharedBank.payload (bank (a := a) (finished mode d)) ports

def result (caller : Tapes t a) (focus : Fin 24 → Fin t) (mode : Mode) (d : Inputs) :=
  installed caller focus (outputs mode d)
def restored (caller : Tapes t a) (focus : Fin 24 → Fin t) (hs : Fin 14 → List Bool) :=
  installed caller focus (sources hs)
def program (mode : Mode) (focus : Fin 24 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixLayoutHeadersRun.program (a := a) mode)
    (CleanSubbank.placement ports focus hf)
def cleanupProgram (focus : Fin 24 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixLayoutHeadersRun.cleanupProgram (a := a))
    (CleanSubbank.placement ports focus hf)

private theorem strip_eq (v : Tapes 43 a)
    (hv : ∀ i : Fin 43, 24 ≤ i.val → v.head i=0 ∧ v.tape i=fun _ => blank) :
    SharedBank.strip v ports=SharedBank.empty 43 a := by
  have hex (i : Fin 43) : (∃ j, ports j=i) ↔ i.val<24 := by
    constructor
    · rintro ⟨j,rfl⟩; exact j.isLt
    · intro h; exact ⟨⟨i.val,h⟩,Fin.ext rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i.val<24
  all_goals simp only [hex,hi,↓reduceIte]
  · exact (hv i (by omega)).1
  · exact (hv i (by omega)).2

theorem input_clean (hs : Fin 14 → List Bool) :
    SharedBank.strip (ActivePrefixLayoutHeadersEndpoint.input (a := a) hs) ports=SharedBank.empty 43 a := by
  apply strip_eq
  intro i hi
  fin_cases i <;> simp only at hi
  all_goals first | omega | exact ⟨rfl,rfl⟩

theorem output_clean (mode : Mode) (d : Inputs) :
    SharedBank.strip (bank (a := a) (finished mode d)) ports=SharedBank.empty 43 a := by
  apply strip_eq
  intro i hi
  fin_cases i <;> simp only at hi
  all_goals first | omega | exact ⟨rfl,rfl⟩

theorem produces (caller : Tapes t a) (focus : Fin 24 → Fin t) (hf : Function.Injective focus)
    (mode : Mode) (d : Inputs) (hw : d.w≤d.H)
    (hs : Fin 14 → List Bool) (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (A : ℕ) (hA : 0<A) (hp : 0<d.payload)
    (ho : ∀ i, originalValues d i≤A) (hS : suffix mode d≤A) :
    HoareTime (program mode focus hf) (fun v => v=CleanSubbank.bank (s := 43) caller)
      (fun v => v=CleanSubbank.bank (s := 43) (result caller focus mode d))
      (ActivePrefixLayoutHeadersBudget.constant*A) := by
  apply CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus mode d)
    _ _ _ hsrc.symm
  · exact (installed_payload caller focus hf (outputs mode d)).symm
  · exact input_clean hs
  · exact output_clean mode d
  · exact installed_frame caller focus _
  · exact ActivePrefixLayoutHeadersEndpoint.produces mode d hw hs hv hc A hA hp ho hS

theorem cleans (caller : Tapes t a) (focus : Fin 24 → Fin t) (hf : Function.Injective focus)
    (mode : Mode) (d : Inputs) (hs : Fin 14 → List Bool)
    (hsrc : SharedBank.payload caller focus=outputs mode d)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (A : ℕ) (hA : 0<A) (ho : ∀ i, originalValues d i≤A) (hS : suffix mode d≤A) :
    HoareTime (cleanupProgram focus hf) (fun v => v=CleanSubbank.bank (s := 43) caller)
      (fun v => v=CleanSubbank.bank (s := 43) (restored caller focus hs))
      (ActivePrefixLayoutHeadersBudget.cleanupConstant*A) := by
  apply CleanSubbank.realizes _ ports focus ports_injective hf caller (restored caller focus hs)
    _ _ _ hsrc.symm
  · exact (installed_payload caller focus hf (sources hs)).symm
  · exact output_clean mode d
  · exact input_clean hs
  · exact installed_frame caller focus _
  · exact ActivePrefixLayoutHeadersEndpoint.cleans mode d hs hv hc A hA ho hS

theorem frame (caller : Tapes t a) (focus : Fin 24 → Fin t) (mode : Mode) (d : Inputs)
    (i : Fin t) (hi : ¬∃ j, focus j=i) :
    (result caller focus mode d).head i=caller.head i ∧
    (result caller focus mode d).tape i=caller.tape i := by
  simp only [result,installed,hi,↓reduceDIte]
  exact ⟨trivial,trivial⟩

theorem restored_eq (caller : Tapes t a) (focus : Fin 24 → Fin t) (_hf : Function.Injective focus)
    (hs : Fin 14 → List Bool) (hsrc : SharedBank.payload caller focus=sources hs) :
    restored caller focus hs=caller := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals split_ifs with h
  · have he := congrFun (congrArg Tapes.head hsrc) h.choose
    simpa only [SharedBank.payload,h.choose_spec] using he.symm
  · rfl
  · have he := congrFun (congrArg Tapes.tape hsrc) h.choose
    simpa only [SharedBank.payload,h.choose_spec] using he.symm
  · rfl

theorem result_payload (caller : Tapes t a) (focus : Fin 24 → Fin t) (hf : Function.Injective focus)
    (mode : Mode) (d : Inputs) :
    SharedBank.payload (result caller focus mode d) focus=outputs mode d :=
  installed_payload caller focus hf _

theorem originals_retained (caller : Tapes t a) (focus : Fin 24 → Fin t)
    (hf : Function.Injective focus) (mode : Mode) (d : Inputs)
    (hs : Fin 14 → List Bool) (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (j : Fin 14) :
    (result caller focus mode d).head (focus (Fin.castAdd 10 j))=caller.head (focus (Fin.castAdd 10 j)) ∧
    (result caller focus mode d).tape (focus (Fin.castAdd 10 j))=caller.tape (focus (Fin.castAdd 10 j)) := by
  have hout := result_payload caller focus hf mode d
  have he : (ActivePrefixLayoutHeadersEndpoint.input (a := a) hs).head (ports (Fin.castAdd 10 j))=
      (bank (a := a) (finished mode d)).head (ports (Fin.castAdd 10 j)) ∧
      (ActivePrefixLayoutHeadersEndpoint.input (a := a) hs).tape (ports (Fin.castAdd 10 j))=
      (bank (a := a) (finished mode d)).tape (ports (Fin.castAdd 10 j)) := by
    have h := ActivePrefixLayoutHeadersEndpoint.originals_retained (a := a) mode d hs hv hc j
    fin_cases j <;> exact ⟨h.1.symm,h.2.symm⟩
  have hoh := congrFun (congrArg Tapes.head hout) (Fin.castAdd 10 j)
  have hot := congrFun (congrArg Tapes.tape hout) (Fin.castAdd 10 j)
  have hih := congrFun (congrArg Tapes.head hsrc) (Fin.castAdd 10 j)
  have hit := congrFun (congrArg Tapes.tape hsrc) (Fin.castAdd 10 j)
  exact ⟨hoh.trans (he.1.symm.trans hih.symm),hot.trans (he.2.symm.trans hit.symm)⟩

/-- The ten consumer words are physically present and their heads are at one. -/
theorem headers (caller : Tapes t a) (focus : Fin 24 → Fin t) (hf : Function.Injective focus)
    (mode : Mode) (d : Inputs) (j : Fin 10) :
    (result caller focus mode d).tape (focus (Fin.natAdd 14 j))=
      RadixZeroFill.encodedBinary (ActivePrefixLayoutHeadersEndpoint.words mode d j) ∧
    (result caller focus mode d).head (focus (Fin.natAdd 14 j))=1 := by
  have h := result_payload caller focus hf mode d
  have ht := congrFun (congrArg Tapes.tape h) (Fin.natAdd 14 j)
  have hh := congrFun (congrArg Tapes.head h) (Fin.natAdd 14 j)
  have ho := ActivePrefixLayoutHeadersEndpoint.outputs (a := a) mode d j
  exact ⟨ht.trans ho.1,hh.trans ho.2⟩

end
end IntegerMultBounds.Machine.ActivePrefixLayoutHeadersPlaced
