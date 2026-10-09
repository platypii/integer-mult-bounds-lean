import IntegerMultBounds.Machine.ContiguousBankPlacement
import IntegerMultBounds.Machine.CompactComplexStopRun
import IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced

/-! Generate the actual recursive stop flag from native dimension header45
and live controller exponent1. A contiguous fresh stop10 workspace follows
original controller44/native66 and arbitrary native-core workspace; every
persistent stack after it and every original caller tape/head is retained. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerStopSetup
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a w r : ℕ}

abbrev tapes (w r : ℕ) := (110+w)+(10+r)
def dimensionSource : Fin (110+w) := Fin.castAdd w (45 : Fin 110)
def exponentSource : Fin (110+w) := Fin.castAdd w (1 : Fin 110)
def bank (caller : Tapes (110+w) a) (stop : Tapes 10 a) (persist : Tapes r a) :=
  ContiguousBankPlacement.bank caller stop persist

def copyFocus (src : Fin (110+w)) (dst : Fin 10) : Fin 2 → Fin (tapes w r) :=
  ![Fin.castAdd (10+r) src,ContiguousBankPlacement.focus dst]
theorem copy_injective (src : Fin (110+w)) (dst : Fin 10) :
    Function.Injective (copyFocus (r := r) src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · have hv := congrArg Fin.val h
    simp [copyFocus,ContiguousBankPlacement.focus] at hv
    omega
  · have hv := congrArg Fin.val h
    simp [copyFocus,ContiguousBankPlacement.focus] at hv
    omega
  · rfl

def copyProgram (src : Fin (110+w)) (dst : Fin 10) :=
  BinaryDescriptorCopyPlaced.program (a := a) (copyFocus (r := r) src dst) (copy_injective src dst)

private theorem setTape_append_right {l n : ℕ} (v : Tapes l a) (small : Tapes n a)
    (i : Fin n) (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append small) (Fin.natAdd l i) f p=v.append (setTape small i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem update_stop (caller : Tapes (110+w) a) (stop : Tapes 10 a) (persist : Tapes r a)
    (dst : Fin 10) (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (bank caller stop persist) (ContiguousBankPlacement.focus dst) f p=
      bank caller (setTape stop dst f p) persist := by
  unfold bank ContiguousBankPlacement.bank ContiguousBankPlacement.focus
  rw [setTape_append_right,SharedPlacementAlphabet.setTape_append_left]

private theorem copy_runs (caller : Tapes (110+w) a) (stop : Tapes 10 a) (persist : Tapes r a)
    (src : Fin (110+w)) (dst : Fin 10) (value : ℕ)
    (ht : caller.tape src=RadixZeroFill.encodedBinary (bits value)) (hh : caller.head src=1)
    (hd : stop.tape dst=fun _ => blank) (hp : stop.head dst=0) :
    HoareTime (copyProgram src dst) (fun v => v=bank caller stop persist)
      (fun v => v=bank caller (setTape stop dst (RadixZeroFill.encodedBinary (bits value)) 1) persist)
      (2*value+7) := by
  have h := BinaryDescriptorCopyPlaced.copies (bank caller stop persist) (copyFocus src dst)
    (copy_injective src dst) (bits value) (by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
      all_goals simp [copyFocus,bank,ContiguousBankPlacement.bank,
        ContiguousBankPlacement.focus,Tapes.append,
        Copy.cfg,hh,hp,ht,hd])
  have hl := GrowingCounterData.canonical_width (bits value) (RecursiveChildQuotientsConstant.bits_canonical value)
  rw [RecursiveChildQuotientsConstant.bits_value] at hl
  have hlog := Nat.log2_le_self value
  apply h.consequence (fun _ h => h) _ (by omega)
  intro v hv
  rw [hv]
  exact update_stop caller stop persist dst _ _

def initialized (D e : ℕ) : Tapes 10 a :=
  setTape (setTape (SharedBank.empty 10 a) 6 (RadixZeroFill.encodedBinary (bits D)) 1)
    9 (RadixZeroFill.encodedBinary (bits e)) 1

private theorem initialized_eq (D e : ℕ) :
    initialized (a := a) D e=CompactComplexStopRun.input (bits D) (bits e) := by
  unfold initialized CompactComplexStopRun.input CompactComplexStopRun.exponent FixedBasePowerUntil.input
  simp only [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def initializeProgram : Σ q, Program (tapes w r) q a :=
  ⟨_,seq (copyProgram dimensionSource (6 : Fin 10)) (copyProgram exponentSource (9 : Fin 10))⟩
def programFor (B : ℕ) : Σ q, Program (tapes w r) q a :=
  ⟨_,seq initializeProgram.2 (ContiguousBankPlacement.program
    (CompactComplexStopRun.program (q := a) B))⟩

/-- Only retained original headers and a blank private stop workspace enter. -/
theorem runsFor (B : ℕ) (hB : 2≤B) (caller : Tapes (110+w) a) (persist : Tapes r a) (D e : ℕ) (hD : 0<D)
    (hd : caller.tape dimensionSource=RadixZeroFill.encodedBinary (bits D))
    (hhd : caller.head dimensionSource=1)
    (he : caller.tape exponentSource=RadixZeroFill.encodedBinary (bits e))
    (hhe : caller.head exponentSource=1) :
    HoareTime (programFor B (a := a) (w := w) (r := r)).2
      (fun v => v=bank caller (SharedBank.empty 10 a) persist)
      (fun v => v=bank caller
        (CompactComplexStopRun.output B D (bits D) (bits e)) persist)
      (2*D+2*e+16+
        (FixedBasePowerUntil.constant B*B+2*B+27)*(D+e+1)) := by
  have hd' := copy_runs caller (SharedBank.empty 10 a) persist dimensionSource 6 D hd hhd rfl rfl
  have he' := copy_runs caller
    (setTape (SharedBank.empty 10 a) 6 (RadixZeroFill.encodedBinary (bits D)) 1)
    persist exponentSource 9 e he hhe (by simp [setTape,SharedBank.empty]) (by simp [setTape,SharedBank.empty])
  have hi := hd'.seq he'
  change HoareTime initializeProgram.2 _ (fun v => v=bank caller (initialized D e) persist) _ at hi
  rw [initialized_eq] at hi
  have hs := ContiguousBankPlacement.runs (CompactComplexStopRun.runs_scalar B D hB hD (bits D) (bits e)
    (RecursiveChildQuotientsConstant.bits_value D) (RecursiveChildQuotientsConstant.bits_canonical D)
    (RecursiveChildQuotientsConstant.bits_canonical e)) caller persist
  simp only [RecursiveChildQuotientsConstant.bits_value] at hs
  exact (hi.seq hs).consequence (fun _ h => h) (fun _ h => h) (by omega)

def program : Σ q, Program (tapes w r) q a := programFor CompactComplexStopThreshold.base

theorem runs (caller : Tapes (110+w) a) (persist : Tapes r a) (D e : ℕ) (hD : 0<D)
    (hd : caller.tape dimensionSource=RadixZeroFill.encodedBinary (bits D))
    (hhd : caller.head dimensionSource=1)
    (he : caller.tape exponentSource=RadixZeroFill.encodedBinary (bits e))
    (hhe : caller.head exponentSource=1) :
    HoareTime (programFor CompactComplexStopThreshold.base (a := a) (w := w) (r := r)).2
      (fun v => v=bank caller (SharedBank.empty 10 a) persist)
      (fun v => v=bank caller
        (CompactComplexStopRun.output CompactComplexStopThreshold.base D (bits D) (bits e)) persist)
      (2*D+2*e+16+
        (FixedBasePowerUntil.constant CompactComplexStopThreshold.base*CompactComplexStopThreshold.base+2*CompactComplexStopThreshold.base+27)*(D+e+1)) :=
  runsFor CompactComplexStopThreshold.base CompactComplexStopThreshold.base_ge_two caller persist D e hD hd hhd he hhe

/-- The runtime symbol is exactly the manuscript's strict stopping decision. -/
theorem flag (caller : Tapes (110+w) a) (persist : Tapes r a) (D e : ℕ) :
    (bank caller (CompactComplexStopRun.output CompactComplexStopThreshold.base D (bits D) (bits e)) persist).reads
      (ContiguousBankPlacement.focus (8 : Fin 10))=bitSymbol (Networks.ComplexRecursiveCallSchema.stopped D e) := by
  simp only [bank,ContiguousBankPlacement.bank,ContiguousBankPlacement.focus,Tapes.reads,Tapes.append,
    Fin.addCases_right,Fin.addCases_left]
  change (CompactComplexStopRun.output (q := a) CompactComplexStopThreshold.base D (bits D) (bits e)).tape 8 0= _
  exact CompactComplexStopRun.flag_actual D e (bits D) (bits e) (RecursiveChildQuotientsConstant.bits_value e)

end
end IntegerMultBounds.Machine.CompactComplexControllerStopSetup
