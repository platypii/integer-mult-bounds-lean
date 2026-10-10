import IntegerMultBounds.Machine.CompactComplexScalarDenominatorSequence
import IntegerMultBounds.Machine.RawLinearCombinationComplexDenominatorPlaced
import IntegerMultBounds.Machine.CompactComplexNativeRoleBridge
import IntegerMultBounds.Machine.CompactComplexRolePhaseSite

/-! Actual named scalar wires share the existing permanent role tapes.
The count and true live denominator occupy separate persistent storage ports;
no source copying or equality between independently prepared banks is used. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarRolePorts
noncomputable section
open CompactComplexScalarRowBlock (wireCount wires_pos)
open CompactComplexScalarPolynomialSequence (rows scratch scratch_fits execute)
open CompactComplexScalarIntegerRows (RowIndex wireIndex)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
open CompactComplexControllerNativeFrame (tapes storageSlot)
open ButterflyStreamData (Coefficient)
open RecursiveChildQuotientsConstant (bits)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates

/-- Both enumerations name the same genuine network wire. -/
def roleIndex : Fin wireCount ≃ Fin roleCount := wireIndex.symm.trans roleEncoding

private def bankPorts {c R s : ℕ} (roles : Fin c → Fin R) (storedPorts : Fin 2 → Fin s) :
    Fin (c+2) → Fin (tapes s+R) :=
  Fin.addCases (fun j => Fin.natAdd (tapes s) (roles j))
    (fun j => Fin.castAdd R (storageSlot (storedPorts j)))

private theorem bankPorts_injective {c R s : ℕ} (roles : Fin c → Fin R)
    (storedPorts : Fin 2 → Fin s) (hr : Function.Injective roles) (hm : Function.Injective storedPorts) :
    Function.Injective (bankPorts roles storedPorts) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [bankPorts,Fin.addCases_left] at h
      exact congrArg (Fin.castAdd 2) (hr (Fin.natAdd_injective _ _ h))
    | right j =>
      have hv := congrArg Fin.val h
      simp only [bankPorts,Fin.addCases_left,Fin.addCases_right,storageSlot,
        Fin.val_natAdd,Fin.val_castAdd,tapes] at hv
      have := (storedPorts j).isLt
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have hv := congrArg Fin.val h
      simp only [bankPorts,Fin.addCases_left,Fin.addCases_right,storageSlot,
        Fin.val_natAdd,Fin.val_castAdd,tapes] at hv
      have := (storedPorts i).isLt
      omega
    | right j =>
      have hv := congrArg Fin.val h
      simp only [bankPorts,Fin.addCases_right,storageSlot,Fin.val_natAdd,Fin.val_castAdd] at hv
      have he : storedPorts i=storedPorts j := Fin.ext (by omega)
      exact congrArg (Fin.natAdd c) (hm he)

def ledgerPorts (hs : 7<s) (header : Fin s) : Fin 2 → Fin s := ![header,⟨7,hs⟩]

private theorem ledger_injective (hs : 7<s) (header : Fin s) (hh : header.val≠7) :
    Function.Injective (ledgerPorts hs header) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl | (have hv := congrArg Fin.val h; simp [ledgerPorts] at hv; omega)

def common (hs : 7<s) (header : Fin s) := bankPorts roleIndex (ledgerPorts hs header)

theorem common_injective (hs : 7<s) (header : Fin s) (hh : header.val≠7) :
    Function.Injective (common hs header) :=
  bankPorts_injective _ _ roleIndex.injective (ledger_injective hs header hh)

theorem source_port (hs : 7<s) (header : Fin s) (j : Fin wireCount) :
    common hs header (Fin.castAdd 2 j)=CompactComplexNativeRoleBridge.roleSlot (roleIndex j) := by
  simp only [common,bankPorts,Fin.addCases_left,CompactComplexNativeRoleBridge.roleSlot]

theorem count_port (hs : 7<s) (header : Fin s) :
    common hs header (Fin.natAdd wireCount (0 : Fin 2))=Fin.castAdd roleCount (storageSlot header) := by
  simp only [common,bankPorts,Fin.addCases_right,ledgerPorts,Matrix.cons_val_zero]

theorem live_port (hs : 7<s) (header : Fin s) :
    common hs header (Fin.natAdd wireCount (1 : Fin 2))=
      Fin.castAdd roleCount (storageSlot ⟨7,hs⟩) := by
  simp only [common,bankPorts,Fin.addCases_right,ledgerPorts,Matrix.cons_val_one,Matrix.cons_val_zero]

abbrev publicTapes (s : ℕ) := tapes s+roleCount
abbrev privateTapes := RawLinearCombinationComplexDenominatorPlaced.localCount wireCount scratch

abbrev Ready {n : ℕ} (hs : 7<s) (header : Fin s) (v : Tapes (publicTapes s) 2)
    (data : Fin wireCount → Fin n → Coefficient) (d : ℕ) :=
  RawLinearCombinationComplexDenominatorPlaced.Ready (common hs header) v data (bits n) d

/-- Existing native row serialization is literally the scalar stream word;
flattening only names the same positions and performs no tape operation. -/
theorem native_word {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
    (inp : ActivePrefixStageFullData.Inputs sh)
    (xs : Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :
    ButterflyStreamData.full (fun _ => blank) 0 (ActivePrefixStageNativePolynomial.flattenArray xs)=
      SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
        (ActivePrefixStageNativePolynomial.rows inp xs hw))) := by
  rw [ActivePrefixStageNativePolynomial.serialized_rows inp xs hw]
  rfl

theorem ready_native {sh : CompactGadgetReservationShape.Shape} {R w : ℕ}
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s)
    (v : Tapes (publicTapes s) 2)
    (xs : Fin wireCount → Fin (ActivePrefixStageTripleWords.count inp) → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w) (d : ℕ)
    (hsource : ∀ a,v.head (CompactComplexNativeRoleBridge.roleSlot (roleIndex a))=0 ∧
      v.tape (CompactComplexNativeRoleBridge.roleSlot (roleIndex a))=
        SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
          (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hcount : v.head (Fin.castAdd roleCount (storageSlot header))=1 ∧
      v.tape (Fin.castAdd roleCount (storageSlot header))=
        RadixZeroFill.encodedBinary (bits (ActivePrefixStageTripleWords.count inp*R)))
    (hlive : v.head (Fin.castAdd roleCount (storageSlot ⟨7,hs⟩))=1 ∧
      v.tape (Fin.castAdd roleCount (storageSlot ⟨7,hs⟩))=RadixZeroFill.encodedBinary (bits d)) :
    Ready hs header v (fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)) d := by
  refine ⟨?_,?_,?_⟩
  · intro a
    rw [source_port]
    exact ⟨(hsource a).1,(hsource a).2.trans (native_word inp (xs a) (hw a)).symm⟩
  · simpa only [count_port] using hcount
  · simpa only [live_port] using hlive

private def compiled {c S k : ℕ} {ι : Type*} (hc : 0<c)
    (es : ι → Fin c → RadixLinearCombinationRefresh.Expr c)
    (hs : ∀ r j,RadixLinearCombinationRefresh.Size (es r j)≤S) (ops : List ι)
    (common : Fin (c+2) → Fin k) (hinj : Function.Injective common) :
    Σ q,Program (k+RawLinearCombinationComplexDenominatorPlaced.localCount c S) q 2 :=
  ⟨_,RawLinearCombinationComplexDenominatorPlaced.program hc es hs ops common hinj⟩

private def callerBank {c S k : ℕ} (v : Tapes k 2) :
    Tapes (k+RawLinearCombinationComplexDenominatorPlaced.localCount c S) 2 :=
  CleanSubbank.bank v

def readyBank (v : Tapes (publicTapes s) 2) := callerBank (c:=wireCount) (S:=scratch) v

def program (hs : 7<s) (header : Fin s) (hh : header.val≠7) (ops : List RowIndex) :=
  compiled wires_pos rows scratch_fits ops
    (common hs header) (common_injective hs header hh)

abbrev output {n : ℕ} (hs : 7<s) (header : Fin s) (v : Tapes (publicTapes s) 2)
    (data : Fin wireCount → Fin n → Coefficient) (d : ℕ) :=
  RawLinearCombinationComplexDenominatorPlaced.output (S:=scratch) (common hs header) v data (bits n) d

private theorem placed_runs {c S k n : ℕ} {ι : Type*} (hc : 0<c)
    (es : ι → Fin c → RadixLinearCombinationRefresh.Expr c)
    (hs : ∀ r j,RadixLinearCombinationRefresh.Size (es r j)≤S) (ops : List ι)
    (common : Fin (c+2) → Fin k) (hinj : Function.Injective common)
    (v : Tapes k 2) (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (bs : List Bool) (hn : Counter.value bs=n) (d : ℕ)
    (hr : RawLinearCombinationComplexDenominatorPlaced.Ready common v data bs d) :
    HoareTime (compiled hc es hs ops common hinj).2
      (fun z => z=callerBank (c:=c) (S:=S) v)
      (fun z => z=callerBank (c:=c) (S:=S)
        (RawLinearCombinationComplexDenominatorPlaced.output (S:=S) common v
          (RawLinearCombinationComplexRowSequence.execute hc es ops data) bs (d+ops.length)))
      (RawLinearCombinationComplexDenominatorSequence.cost es n w bs ops d) :=
  RawLinearCombinationComplexDenominatorPlaced.runs hc es hs ops common hinj v data w hw bs hn d hr

/-- The genuine scalar streams execute directly on their existing role tapes,
with count and storage7 shared and all remaining permanent tapes framed. -/
theorem runs {n : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7) (ops : List RowIndex)
    (v : Tapes (publicTapes s) 2) (data : Fin wireCount → Fin n → Coefficient) (w d : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (hready : Ready hs header v data d) :
    HoareTime (program hs header hh ops).2
      (fun z => z=readyBank v)
      (fun z => z=readyBank
        (output hs header v (execute ops data) (d+ops.length)))
      (CompactComplexScalarDenominatorSequence.cost ops n w d) := by
  have h := placed_runs wires_pos rows scratch_fits ops
    (common hs header) (common_injective hs header hh) v data w hw (bits n)
    (RecursiveChildQuotientsConstant.bits_value n) d hready
  exact h.consequence (fun _ h => h) (fun _ h => h)
    (CompactComplexScalarDenominatorSequence.cost_bound ops n w d)

theorem output_ready {n : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (publicTapes s) 2) (data : Fin wireCount → Fin n → Coefficient) (d : ℕ) :
    Ready hs header (output hs header v data d) data d :=
  RawLinearCombinationComplexDenominatorPlaced.output_ready (common hs header)
    (common_injective hs header hh) v data (bits n) d

/-- The completed actual scalar data and controller storage7 have the same
physical denominator; the coefficient count and heads are retained as well. -/
theorem output_live {n : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (publicTapes s) 2) (data : Fin wireCount → Fin n → Coefficient) (d : ℕ) :
    (output hs header v data d).head (Fin.castAdd roleCount (storageSlot ⟨7,hs⟩))=1 ∧
    (output hs header v data d).tape (Fin.castAdd roleCount (storageSlot ⟨7,hs⟩))=
      RadixZeroFill.encodedBinary (bits d) := by
  have h := (output_ready hs header hh v data d).2.2
  simpa only [live_port] using h

theorem output_outside {n : ℕ} (hs : 7<s) (header : Fin s)
    (v : Tapes (publicTapes s) 2) (data : Fin wireCount → Fin n → Coefficient) (d : ℕ)
    (i : Fin (publicTapes s)) (hi : ¬∃ j,common hs header j=i) :
    (output hs header v data d).head i=v.head i ∧
      (output hs header v data d).tape i=v.tape i :=
  RawLinearCombinationComplexDenominatorPlaced.output_outside (common hs header) v data (bits n) d i hi

end
end IntegerMultBounds.Machine.CompactComplexScalarRolePorts
