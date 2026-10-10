import IntegerMultBounds.Machine.CompactComplexScalarCountRootBank
import IntegerMultBounds.Machine.SharedBankFamily

/-! Original-header count setup, actual scalar row execution, and physical
count erasure form one clean fixed block on the same permanent caller bank. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarCountLifecycle
noncomputable section
open SharedBankStageInput (raw)
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexScalarCountRootBank (countSlot)
open CompactComplexScalarIntegerRows (RowIndex)
open ButterflyStreamData (Coefficient)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates
  CompactComplexScalarRolePorts.program CompactComplexScalarCountRootBank.program


private def assemble {k x y q r t : ℕ} (setup : Program (k+x) q 2)
    (scalar : Program (k+y) r 2) (erase : Program k t 2) :=
  seq (seq (SharedBankFamily.padProgram setup (by omega : k+x≤k+x+y))
    (SharedBankFamily.padProgram scalar (by omega : k+y≤k+x+y)))
    (SharedBankFamily.padProgram erase (by omega : k≤k+x+y))


private theorem raw_self {k : ℕ} (v : Tapes k 2) : raw v k=v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [dite_eq_left i.isLt]


private theorem compose {k x y q r t A B C : ℕ}
    (setup : Program (k+x) q 2) (scalar : Program (k+y) r 2) (erase : Program k t 2)
    (v0 v1 v2 v3 : Tapes k 2)
    (h0 : HoareTime setup (fun z => z=CleanSubbank.bank (s:=x) v0)
      (fun z => z=CleanSubbank.bank (s:=x) v1) A)
    (h1 : HoareTime scalar (fun z => z=CleanSubbank.bank (s:=y) v1)
      (fun z => z=CleanSubbank.bank (s:=y) v2) B)
    (h2 : HoareTime erase (fun z => z=v2) (fun z => z=v3) C) :
    HoareTime (assemble setup scalar erase) (fun z => z=raw v0 (k+x+y))
      (fun z => z=raw v3 (k+x+y)) (A+B+C+2) := by
  have h0' := SharedBankFamily.pad_clean_realizes (by omega : k+x≤k+x+y) v0 v1 A h0
  have h1' := SharedBankFamily.pad_clean_realizes (by omega : k+y≤k+x+y) v1 v2 B h1
  have h2r : HoareTime erase (fun z => z=raw v2 k) (fun z => z=raw v3 k) C := by
    simpa only [raw_self] using h2
  have h2' := SharedBankFamily.pad_realizes (by omega : k≤k+x+y) (le_refl k) v2 v3 C h2r
  exact ((h0'.seq h1').seq h2').consequence (fun _ h => h) (fun _ h => h) (by omega)


abbrev publicTapes (s : ℕ) := CompactComplexControllerNativeFrame.tapes (s+43)+CompactComplexRolePhaseSite.roleCount
abbrev privateTapes := RawLinearCombinationComplexDenominatorPlaced.localCount
  CompactComplexScalarRowBlock.wireCount CompactComplexScalarPolynomialSequence.scratch
abbrev totalTapes (s : ℕ) := publicTapes s+43+privateTapes

theorem liveProof (hs : 7<s) : 7<s+43 := by omega
def storedHeader (header : Fin s) : Fin (s+43) := Fin.castAdd 43 header
theorem header_ne_live (header : Fin s) (hh : header.val≠7) : (storedHeader header).val≠7 := hh

private def assembled {k x y : ℕ}
    (setup : Σ q,Program (k+x) q 2) (scalar : Σ q,Program (k+y) q 2)
    (erase : Σ q,Program k q 2) : Σ q,Program (k+x+y) q 2 :=
  ⟨_,assemble setup.2 scalar.2 erase.2⟩

private def setupProgram (header : Fin s) : Σ q,Program (publicTapes s+43) q 2 :=
  ⟨_,CompactComplexScalarCountRootBank.program (c:=CompactComplexRolePhaseSite.roleCount) header⟩

private def eraseProgram (header : Fin s) : Σ q,Program (publicTapes s) q 2 :=
  ⟨_,CompactComplexScalarCountBudget.eraseProgram (countSlot header)⟩

private def scalarProgram (hs : 7<s) (header : Fin s) (hh : header.val≠7) (ops : List RowIndex) :
    Σ q, Program (CompactComplexControllerNativeFrame.tapes (s+43)+
      CompactComplexRolePhaseSite.roleCount+
      RawLinearCombinationComplexDenominatorPlaced.localCount CompactComplexScalarRowBlock.wireCount
        CompactComplexScalarPolynomialSequence.scratch) q 2 :=
  CompactComplexScalarRolePorts.program (s:=s+43) (liveProof hs) (storedHeader header) (header_ne_live header hh) ops

def program (hs : 7<s) (header : Fin s) (hh : header.val≠7) (ops : List RowIndex) :=
  assembled (k:=publicTapes s) (x:=43)
    (y:=RawLinearCombinationComplexDenominatorPlaced.localCount CompactComplexScalarRowBlock.wireCount
      CompactComplexScalarPolynomialSequence.scratch) (setupProgram header)
    (scalarProgram hs header hh ops) (eraseProgram header)

def counted (header : Fin s) (v : Tapes (publicTapes s) 2) (N : ℕ) :=
  CompactComplexScalarCountRootBank.output header v N

def scalarOutput {n : ℕ} (hs : 7<s) (header : Fin s) (v : Tapes (publicTapes s) 2)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Fin n → Coefficient) (d : ℕ) :=
  CompactComplexScalarRolePorts.output (liveProof hs) (storedHeader header) v data d

def output {n : ℕ} (hs : 7<s) (header : Fin s) (v : Tapes (publicTapes s) 2)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Fin n → Coefficient) (d : ℕ) :=
  SharedPlacementAlphabet.setTape (scalarOutput hs header (counted header v n) data d)
    (countSlot header) (fun _ => blank) 0

private theorem ready_count {c k n : ℕ} (common : Fin (c+2) → Fin k) (v : Tapes k 2)
    (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ)
    (h : RawLinearCombinationComplexDenominatorPlaced.Ready common v data bs d) :
    v.head (common (Fin.natAdd c (0 : Fin 2)))=1 ∧
    v.tape (common (Fin.natAdd c (0 : Fin 2)))=RadixZeroFill.encodedBinary bs := h.2.1

private theorem endpoint_count {n : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (publicTapes s) 2)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Fin n → Coefficient) (d : ℕ) :
    (scalarOutput hs header v data d).head (countSlot header)=1 ∧
    (scalarOutput hs header v data d).tape (countSlot header)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n) := by
  have h := ready_count _ _ _ _ _
    (CompactComplexScalarRolePorts.output_ready (liveProof hs) (storedHeader header)
      (header_ne_live header hh) v data d)
  simpa only [CompactComplexScalarRolePorts.count_port,scalarOutput,storedHeader,
    CompactComplexScalarCountRootBank.countSlot] using h

private theorem flat_width {c N R w : ℕ} (xs : Fin c → Fin N → Fin R → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w) :
    ∀ a i,(ActivePrefixStageNativePolynomial.flattenArray (xs a) i).1.length=w ∧
      (ActivePrefixStageNativePolynomial.flattenArray (xs a) i).2.length=w := by
  intro a i
  exact hw a (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def cost (ops : List RowIndex) (n w d : ℕ) :=
  (CompactComplexScalarCountBudget.constant+8)*n+
    CompactComplexScalarDenominatorSequence.cost ops n w d+2


def Realizes {k t : ℕ} (P : Σ q,Program t q 2) (v0 v1 : Tapes k 2) (A : ℕ) :=
  HoareTime P.2 (fun z => z=raw v0 t) (fun z => z=raw v1 t) A

private theorem composed {k x y A B C : ℕ}
    (setup : Σ q,Program (k+x) q 2) (scalar : Σ q,Program (k+y) q 2)
    (erase : Σ q,Program k q 2) (v0 v1 v2 v3 : Tapes k 2)
    (h0 : HoareTime setup.2 (fun z => z=CleanSubbank.bank (s:=x) v0)
      (fun z => z=CleanSubbank.bank (s:=x) v1) A)
    (h1 : HoareTime scalar.2 (fun z => z=CleanSubbank.bank (s:=y) v1)
      (fun z => z=CleanSubbank.bank (s:=y) v2) B)
    (h2 : HoareTime erase.2 (fun z => z=v2) (fun z => z=v3) C) :
    Realizes (assembled setup scalar erase) v0 v3 (A+B+C+2) :=
  compose setup.2 scalar.2 erase.2 v0 v1 v2 v3 h0 h1 h2

/-- No count header is supplied at input: it is physically derived before the
actual scalar row block, retained while used, then physically erased. -/
theorem runs {sh : CompactGadgetReservationShape.Shape}
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (ops : List RowIndex) (ell p w d : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
            (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hlive : storage.head ⟨7,hs⟩=1 ∧ storage.tape ⟨7,hs⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d)) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload
    let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
    Realizes (program hs header hh ops) v (output hs header v
        (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length))
      (cost ops (ActivePrefixStageTripleWords.count inp*2^ell) w d) := by
  dsimp only
  let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload
  let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
  let n := ActivePrefixStageTripleWords.count inp*2^ell
  have hN : inp.rows*2^sh.bits*2^ell=n := CompactComplexScalarCountHeaders.native_count inp ell
  have hK : 0<sh.chunk := by have := inp.hGK; omega
  have hA : 0<sh.axes := ActivePrefixStageParameters.positive_axes inp.stage
  have h0 := CompactComplexScalarCountRootBank.runs header control queue scalar inp.stage inp.rows ell p
    tail storage payload inp.hr (by have := inp.hG; omega) hA hK hblank.1 hblank.2
  rw [hN] at h0
  have hbanklive : v.head (countSlot (c:=CompactComplexRolePhaseSite.roleCount) ⟨7,hs⟩)=1 ∧
      v.tape (countSlot (c:=CompactComplexRolePhaseSite.roleCount) ⟨7,hs⟩)=
        RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d) := by
    have he := CompactComplexScalarCountRootBank.count_bank ⟨7,hs⟩ control queue scalar
      (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload
    exact ⟨he.1.trans hlive.1,he.2.trans hlive.2⟩
  have hr := CompactComplexScalarCountRootBank.scalar_ready inp hs header hh v xs hw d hsource hbanklive
  rw [hN] at hr
  have h1 := CompactComplexScalarRolePorts.runs (liveProof hs) (storedHeader header)
    (header_ne_live header hh) ops (counted header v n) data w d (flat_width xs hw) hr
  have he := endpoint_count hs header hh (counted header v n)
    (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length)
  have hn : 1≤n := by
    rw [←hN]
    exact (CompactComplexScalarCountBudget.count_bounds sh inp.rows ell inp.hr).1
  have h2 := CompactComplexScalarCountBudget.erase_runs_linear (countSlot header)
    (scalarOutput hs header (counted header v n)
      (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length)) n hn he.2 he.1
  have h := composed (k:=publicTapes s) (x:=43)
    (y:=RawLinearCombinationComplexDenominatorPlaced.localCount CompactComplexScalarRowBlock.wireCount
      CompactComplexScalarPolynomialSequence.scratch)
    (setupProgram header) (scalarProgram hs header hh ops) (eraseProgram header) v (counted header v n)
    (scalarOutput hs header (counted header v n)
      (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length))
    (output hs header v (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length)) h0 h1 h2
  exact h.consequence (fun _ h => h) (fun _ h => h) (by simp only [cost,n,Nat.add_mul]; omega)


/-- Fixed block constant; runtime denominator and coefficient count are not
part of the compiled control. -/
def timeConstant (ops : List RowIndex) :=
  CompactComplexScalarCountBudget.constant+10+
    2*ops.length*(CompactComplexScalarPolynomialReusable.timeConstant+2*ops.length+6)

private theorem linear_allowance (C T m n w : ℕ) (hn : 1≤n) :
    (C+8)*n+m*((T+2*m+6)*(n+1)*(w+1))+2≤
      (C+10+2*m*(T+2*m+6))*n*(w+1) := by
  have hN : n+1≤2*n := by omega
  have hS := Nat.mul_le_mul_left (m*(T+2*m+6))
    (Nat.mul_le_mul_right (w+1) hN)
  have hW : n≤n*(w+1) := by nlinarith
  have hB := Nat.mul_le_mul_left (C+8) hW
  have hP : 1≤n*(w+1) := hn.trans hW
  nlinarith

/-- All setup, source replacements, denominator increments and cleanup costs
are uniformly charged to the real augmented coefficient volume. -/
theorem cost_linear (ops : List RowIndex) (n w d : ℕ) (hn : 1≤n) (hd : d≤w) :
    cost ops n w d≤timeConstant ops*n*(w+1) := by
  have h := CompactComplexScalarDenominatorSequence.cost_linear ops n w d ops.length hd (le_refl _)
  have ha := linear_allowance CompactComplexScalarCountBudget.constant
    CompactComplexScalarPolynomialReusable.timeConstant ops.length n w hn
  exact (Nat.add_le_add_right (Nat.add_le_add_left h _) 2).trans ha


private theorem clear_at {k : ℕ} (v : Tapes k 2) (i : Fin k) :
    (SharedPlacementAlphabet.setTape v i (fun _ => blank) 0).head i=0 ∧
    (SharedPlacementAlphabet.setTape v i (fun _ => blank) 0).tape i=(fun _ => blank) := by
  simp [SharedPlacementAlphabet.setTape]

private theorem clear_outside {k : ℕ} (v : Tapes k 2) (i j : Fin k) (h : j≠i) :
    (SharedPlacementAlphabet.setTape v i (fun _ => blank) 0).head j=v.head j ∧
    (SharedPlacementAlphabet.setTape v i (fun _ => blank) 0).tape j=v.tape j := by
  simp only [SharedPlacementAlphabet.setTape,Function.update_of_ne h,and_self]

/-- The physically consumed count port is blank and normalized at return. -/
theorem output_count {n : ℕ} (hs : 7<s) (header : Fin s) (v : Tapes (publicTapes s) 2)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Fin n → Coefficient) (d : ℕ) :
    (output hs header v data d).head (countSlot header)=0 ∧
    (output hs header v data d).tape (countSlot header)=(fun _ => blank) :=
  clear_at _ _

/-- Count cleanup leaves every scalar-block endpoint outside its count port
literally unchanged. -/
theorem output_outside_count {n : ℕ} (hs : 7<s) (header : Fin s)
    (v : Tapes (publicTapes s) 2)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Fin n → Coefficient) (d : ℕ)
    (i : Fin (publicTapes s)) (hi : i≠countSlot header) :
    (output hs header v data d).head i=(scalarOutput hs header (counted header v n) data d).head i ∧
    (output hs header v data d).tape i=(scalarOutput hs header (counted header v n) data d).tape i :=
  clear_outside _ _ _ hi

private theorem countSlot_injective {s c : ℕ} :
    Function.Injective (CompactComplexScalarCountRootBank.countSlot (s:=s) (c:=c)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [CompactComplexScalarCountRootBank.countSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

/-- Live storage7 retains the actual scalar block's advanced denominator after
physical count destruction. -/
theorem output_live {n : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (v : Tapes (publicTapes s) 2)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Fin n → Coefficient) (d : ℕ) :
    (output hs header v data d).head (countSlot ⟨7,hs⟩)=1 ∧
    (output hs header v data d).tape (countSlot ⟨7,hs⟩)=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d) := by
  have hne : countSlot (c:=CompactComplexRolePhaseSite.roleCount) ⟨7,hs⟩≠countSlot header := by
    intro h
    have hv := congrArg Fin.val (countSlot_injective h)
    exact hh hv.symm
  have he := output_outside_count hs header v data d _ hne
  have hl := CompactComplexScalarRolePorts.output_live (liveProof hs) (storedHeader header)
    (header_ne_live header hh) (counted header v n) data d
  exact ⟨he.1.trans hl.1,he.2.trans hl.2⟩


private theorem realizes_mono {k t A B : ℕ} (P : Σ q,Program t q 2)
    (v0 v1 : Tapes k 2) (h : Realizes P v0 v1 A) (hb : A≤B) : Realizes P v0 v1 B :=
  h.consequence (fun _ hz => hz) (fun _ hz => hz) hb

/-- A denominator-capacity guard absorbs every setup and cleanup operation
into the same uniform original coefficient-volume budget. -/
theorem runs_linear {sh : CompactGadgetReservationShape.Shape}
    (inp : ActivePrefixStageFullData.Inputs sh) (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (ops : List RowIndex) (ell p w d : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : ActiveRepairRankHeadersCommands.State)
    (tail : Tapes 22 2) (storage : Tapes s 2)
    (payload : Tapes (1+CompactComplexRolePhaseSite.roleCount) 2)
    (xs : Fin CompactComplexScalarRowBlock.wireCount →
      Fin (ActivePrefixStageTripleWords.count inp) → Fin (2^ell) → Coefficient)
    (hw : ∀ a i j,(xs a i j).1.length=w ∧ (xs a i j).2.length=w)
    (hblank : storage.head header=0 ∧ storage.tape header=(fun _ => blank))
    (hsource : ∀ a,
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload).head
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=0 ∧
      (bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload).tape
        (CompactComplexNativeRoleBridge.roleSlot (CompactComplexScalarRolePorts.roleIndex a))=
          SymbolTripleClean.word (List.ofFn (ActivePrefixStageNativeRows.flat
            (ActivePrefixStageNativePolynomial.rows inp (xs a) (hw a)))))
    (hlive : storage.head ⟨7,hs⟩=1 ∧ storage.tape ⟨7,hs⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits d)) (hd : d≤w) :
    let v := bank control queue scalar (CompactComplexNativeCodec.raw inp.stage inp.rows ell p) tail storage payload
    let data := fun a => ActivePrefixStageNativePolynomial.flattenArray (xs a)
    Realizes (program hs header hh ops) v (output hs header v
        (CompactComplexScalarPolynomialSequence.execute ops data) (d+ops.length))
      (timeConstant ops*(ActivePrefixStageTripleWords.count inp*2^ell)*(w+1)) := by
  have h := runs inp hs header hh ops ell p w d control queue scalar tail storage payload xs hw hblank hsource hlive
  have hn : 1≤ActivePrefixStageTripleWords.count inp*2^ell := by
    rw [←CompactComplexScalarCountHeaders.native_count inp ell]
    exact (CompactComplexScalarCountBudget.count_bounds sh inp.rows ell inp.hr).1
  exact realizes_mono _ _ _ h (cost_linear ops _ w d hn hd)

end
end IntegerMultBounds.Machine.CompactComplexScalarCountLifecycle
