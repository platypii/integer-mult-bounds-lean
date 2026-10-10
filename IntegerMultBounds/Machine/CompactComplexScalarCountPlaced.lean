import IntegerMultBounds.Machine.CompactComplexScalarCountHeaders

/-! Count construction runs directly on original caller descriptors and one
fresh permanent count port. Every other caller tape and all private storage
are retained or restored, with no copied count supplied to the constructor. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarCountPlaced
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorLeafSetup (raw)
open ActiveRepairRankHeadersCommands (bank)
open CompactComplexScalarCountHeaders (finished)
open SharedPlacementAlphabet (setTape)
variable {k : ℕ}

def ports : Fin 16 → Fin 43 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,17,18,27]
theorem ports_injective : Function.Injective ports := by decide

def output (common : Fin 16 → Fin k) (v : Tapes k 2) (N : ℕ) :=
  setTape v (common 15) (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits N)) 1

def program (common : Fin 16 → Fin k) (hc : Function.Injective common) :=
  Placement.placed CompactComplexScalarCountHeaders.program (CleanSubbank.placement ports common hc)

private theorem selected_iff (i : Fin 43) :
    (∃ j,ports j=i) ↔ i.val<13 ∨ i.val=17 ∨ i.val=18 ∨ i.val=27 := by
  constructor
  · rintro ⟨j,rfl⟩
    fin_cases j <;> simp [ports]
  · rintro (h|h|h|h)
    · refine ⟨⟨i.val,by omega⟩,?_⟩
      have hl (j : Fin 13) : (ports ⟨j.val,by omega⟩).val=j.val := by
        fin_cases j <;> rfl
      exact Fin.ext (hl ⟨i.val,h⟩)
    · exact ⟨13,Fin.ext h.symm⟩
    · exact ⟨14,Fin.ext h.symm⟩
    · exact ⟨15,Fin.ext h.symm⟩

private theorem strip_bank (st : ActiveRepairRankHeadersCommands.State)
    (hn : ∀ i:Fin 28, ¬(i.val<13 ∨ i.val=17 ∨ i.val=18 ∨ i.val=27) → st i=none) :
    SharedBank.strip (bank (a:=2) st) ports=SharedBank.empty 43 2 := by
  have hp (i : Fin 43) :
      (SharedBank.strip (bank (a:=2) st) ports).head i=0 ∧
      (SharedBank.strip (bank (a:=2) st) ports).tape i=(fun _ => blank) := by
    by_cases hi : ∃ j,ports j=i
    · simp only [SharedBank.strip,hi,↓reduceIte,and_self]
    · induction i using Fin.addCases (m:=28) (n:=15) with
      | left i =>
        have hnone := hn i (by simpa only [selected_iff,Fin.val_castAdd] using hi)
        simp only [SharedBank.strip,hi,↓reduceIte,bank,CleanSubbank.bank,Tapes.append,
          Fin.addCases_left,ActiveRepairRankHeadersCommands.caller,hnone,Option.isSome_none,
          Bool.false_eq_true,↓reduceIte,and_self]
      | right i =>
        simp only [SharedBank.strip,hi,↓reduceIte,bank,CleanSubbank.bank,Tapes.append,
          Fin.addCases_right,SharedBank.empty,and_self]
  apply congrArg₂ Tapes.mk
  · funext i; exact (hp i).1
  · funext i; exact (hp i).2

private theorem strip_input (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    SharedBank.strip (bank (a:=2) (raw s rows ell p rho left count slots right source target)) ports=
      SharedBank.empty 43 2 := by
  apply strip_bank
  intro i hi
  fin_cases i <;> simp_all [raw]

private theorem strip_output (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    SharedBank.strip (bank (a:=2) (finished s rows ell p rho left count slots right source target)) ports=
      SharedBank.empty 43 2 := by
  apply strip_bank
  intro i hi
  have hn : i≠27 := by intro he; subst i; exact hi (by simp)
  simp only [finished,ActiveRepairRankHeadersCommands.put,Function.update_of_ne hn]
  fin_cases i <;> simp_all [raw]

private theorem output_payload (common : Fin 16 → Fin k) (hc : Function.Injective common)
    (v : Tapes k 2) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hi : SharedBank.payload (bank (a:=2) (raw s rows ell p rho left count slots right source target)) ports=
      SharedBank.payload v common) :
    SharedBank.payload (bank (a:=2) (finished s rows ell p rho left count slots right source target)) ports=
      SharedBank.payload (output common v (rows*2^s.bits*2^ell)) common := by
  have hin (j : Fin 16) :
      (bank (a:=2) (raw s rows ell p rho left count slots right source target)).head (ports j)=v.head (common j) ∧
      (bank (a:=2) (raw s rows ell p rho left count slots right source target)).tape (ports j)=v.tape (common j) :=
    ⟨congrFun (congrArg Tapes.head hi) j,congrFun (congrArg Tapes.tape hi) j⟩
  have he := CompactComplexScalarCountHeaders.endpoint s rows ell p rho left count slots right source target
  apply congrArg₂ Tapes.mk
  · funext j
    by_cases hj : j=15
    · subst j; simpa [ports,output,setTape] using he.1
    · have hp : (ports j).val≠27 := by
        intro h; apply hj; apply ports_injective; apply Fin.ext; exact h
      have hn : common j≠common 15 := by intro h; exact hj (hc h)
      change _=(output common v _).head (common j)
      simp only [output,setTape,Function.update_of_ne hn]
      exact (he.2.2 (ports j) hp).1.trans (hin j).1
  · funext j
    by_cases hj : j=15
    · subst j; simpa [ports,output,setTape] using he.2.1
    · have hp : (ports j).val≠27 := by
        intro h; apply hj; apply ports_injective; apply Fin.ext; exact h
      have hn : common j≠common 15 := by intro h; exact hj (hc h)
      change _=(output common v _).tape (common j)
      simp only [output,setTape,Function.update_of_ne hn]
      exact (he.2.2 (ports j) hp).2.trans (hin j).2

private theorem frame (common : Fin 16 → Fin k) (v : Tapes k 2) (N : ℕ) :
    SharedBank.strip v common=SharedBank.strip (output common v N) common := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j,common j=i
    · simp [hi]
    · have hn : i≠common 15 := by intro h; exact hi ⟨15,h.symm⟩
      simp [hi,output,setTape,Function.update_of_ne hn]
  · funext i
    by_cases hi : ∃ j,common j=i
    · simp [hi]
    · have hn : i≠common 15 := by intro h; exact hi ⟨15,h.symm⟩
      simp [hi,output,setTape,Function.update_of_ne hn]

theorem runs (common : Fin 16 → Fin k) (hc : Function.Injective common) (v : Tapes k 2)
    (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (hi : SharedBank.payload (bank (a:=2) (raw s rows ell p rho left count slots right source target)) ports=
      SharedBank.payload v common) :
    HoareTime (program common hc) (fun z => z=CleanSubbank.bank (s:=43) v)
      (fun z => z=CleanSubbank.bank (s:=43) (output common v (rows*2^s.bits*2^ell)))
      (ButterflyAxisHeadersArithmetic.scheduleCost CompactComplexScalarCountHeaders.schedule
        (raw s rows ell p rho left count slots right source target)) :=
  CleanSubbank.realizes _ ports common ports_injective hc v _ _ _ _ hi
    (output_payload common hc v s rows ell p rho left count slots right source target hi)
    (strip_input s rows ell p rho left count slots right source target)
    (strip_output s rows ell p rho left count slots right source target)
    (frame common v _) (CompactComplexScalarCountHeaders.runs _ _ _ _ _ _ _ _ _ _ _ hr hG hA hK)

theorem output_count (common : Fin 16 → Fin k) (v : Tapes k 2) (N : ℕ) :
    (output common v N).head (common 15)=1 ∧
    (output common v N).tape (common 15)=RadixZeroFill.encodedBinary
      (RecursiveChildQuotientsConstant.bits N) := by
  simp [output,setTape]

theorem output_outside (common : Fin 16 → Fin k) (v : Tapes k 2) (N : ℕ)
    (i : Fin k) (hi : i≠common 15) :
    (output common v N).head i=v.head i ∧ (output common v N).tape i=v.tape i := by
  simp [output,setTape,Function.update_of_ne hi]

theorem output_native_count {s : Shape} (common : Fin 16 → Fin k) (v : Tapes k 2)
    (inp : ActivePrefixStageFullData.Inputs s) (ell : ℕ) :
    (output common v (inp.rows*2^s.bits*2^ell)).head (common 15)=1 ∧
    (output common v (inp.rows*2^s.bits*2^ell)).tape (common 15)=RadixZeroFill.encodedBinary
      (RecursiveChildQuotientsConstant.bits (ActivePrefixStageTripleWords.count inp*2^ell)) := by
  rw [CompactComplexScalarCountHeaders.native_count]
  exact output_count common v _

end
end IntegerMultBounds.Machine.CompactComplexScalarCountPlaced
