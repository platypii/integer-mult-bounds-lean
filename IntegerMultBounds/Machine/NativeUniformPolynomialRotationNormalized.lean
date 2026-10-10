import IntegerMultBounds.Machine.NativeUniformPolynomialRotationSemantics
import IntegerMultBounds.Machine.UnitPhasePolynomialRestore
import IntegerMultBounds.Machine.BlankWordOverwriteAt
import IntegerMultBounds.Machine.UnitPhaseFullStreamNormalized

/-! Actual uniform-phase stream results are rewound, overwritten back onto
native source56 and erased on output58. The retained count/columns headers
and every other tape are unchanged at the reusable endpoint. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationNormalized
noncomputable section
open NativeUniformPolynomialRotation (bank phase flagged cleared)
open UnitPhasePolynomialLoop (state coreBlank)
open UnitPhaseFullStreamNormalized (serialized nonblank length)
open ButterflyStreamData (Coefficient)
open SharedPlacementAlphabet (setTape)
variable {N : ℕ}

def rewinds := seq (BlankWordReturnAt.program (a:=2) (56 : Fin 64))
  (BlankWordReturnAt.program (a:=2) (58 : Fin 64))
def overwrite := BlankWordOverwriteAt.program (a:=2) (56 : Fin 64) 58 (by decide)
def program := seq NativeUniformPolynomialRotation.program (seq rewinds overwrite)
def negativeProgram := seq NativeUniformPolynomialRotation.negativeProgram (seq rewinds overwrite)
def raw (v : Tapes 60 2) (q : Fin 4) (columns : ℕ) (xs : Fin N → Coefficient) :=
  bank (cleared (state (flagged v q) (UnitPhaseStreamData.contexts (fun _ => blank) 0 xs) q N)) N columns

def rewindSource (z : Tapes 64 2) (xs : List (Fin 6)) :=
  setTape z 56 (putWord (fun _ => blank) 0 xs) 0
def rewindBoth (z : Tapes 64 2) (xs ys : List (Fin 6)) :=
  setTape (rewindSource z xs) 58 (putWord (fun _ => blank) 0 ys) 0
def output (v : Tapes 60 2) (q : Fin 4) (columns : ℕ) (xs : Fin N → Coefficient) :=
  BlankWordOverwriteAt.output (rewindBoth (raw v q columns xs)
    (serialized xs) (serialized (UnitPhasePolynomialArray.result q xs))) 56 58
    (serialized (UnitPhasePolynomialArray.result q xs))

def cost (N w : ℕ) := N*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits N).length+40+
  5*(N*(2*(w+1)))+13

theorem cost_linear (N w : ℕ) (hn : 0<N) : cost N w≤120*(N*(2*(w+1))) := by
  have h := NativeUniformPolynomialRotationSemantics.cost_linear N w hn
  have hV : 0<N*(2*(w+1)) := by positivity
  unfold cost
  omega

private theorem bank_set (v : Tapes 60 2) (R columns : ℕ) (i : Fin 60)
    (f : ℤ → Fin 6) (p : ℤ) :
    setTape (bank v R columns) (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 i))) f p=
      bank (setTape v i f p) R columns := by
  unfold bank CountedLoopHeaderClean.bank
  rw [SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]

theorem restored (v : Tapes 60 2) (q : Fin 4) (columns : ℕ) (xs : Fin N → Coefficient)
    (hblank : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=0 ∧
      v.tape ⟨48+i.val,by omega⟩=(fun _ => blank))
    (hcore : coreBlank v) (ho : v.tape 58=(fun _ => blank) ∧ v.head 58=0) :
    output v q columns xs=bank
      (setTape v 56 (putWord (fun _ => blank) 0
        (serialized (UnitPhasePolynomialArray.result q xs))) 0) N columns := by
  unfold output BlankWordOverwriteAt.output rewindBoth rewindSource raw
  change setTape (setTape (setTape (setTape (bank _ N columns)
    (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (56 : Fin 60)))) _ 0)
    (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (58 : Fin 60)))) _ 0)
    (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (56 : Fin 60)))) _ 0)
    (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (58 : Fin 60)))) _ 0= _
  rw [bank_set,bank_set,bank_set,bank_set]
  apply congrArg (fun z => bank z N columns)
  have h0 : v.head (48 : Fin 60)=0 ∧ v.tape (48 : Fin 60)=(fun _ => blank) := hblank 0
  have h1 : v.head (49 : Fin 60)=0 ∧ v.tape (49 : Fin 60)=(fun _ => blank) := hblank 1
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases h56 : i=56
  all_goals by_cases h58 : i=58
  all_goals by_cases h48 : i=48
  all_goals by_cases h49 : i=49
  all_goals first
    | (subst_vars; simp [setTape,cleared,ho,h0,h1,Function.update_apply]; done)
    | (have h := NativeUniformPolynomialRotationSemantics.frame v q
          (UnitPhaseStreamData.contexts (fun _ => blank) 0 xs) hcore N i h48 h49 h56 h58
       simpa [setTape,h56,h58] using h.1)
    | (have h := NativeUniformPolynomialRotationSemantics.frame v q
          (UnitPhaseStreamData.contexts (fun _ => blank) 0 xs) hcore N i h48 h49 h56 h58
       simpa [setTape,h56,h58] using h.2)

private theorem normalize (v : Tapes 60 2) (q : Fin 4) (columns w : ℕ)
    (xs : Fin N → Coefficient) (hn : 0<N)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hcore : coreBlank v) (ho : v.tape 58=(fun _ => blank) ∧ v.head 58=0) :
    HoareTime (seq rewinds overwrite) (fun z => z=raw v q columns xs)
      (fun z => z=output v q columns xs) (5*(N*(2*(w+1)))+12) := by
  let ys := serialized (UnitPhasePolynomialArray.result q xs)
  have hf := NativeUniformPolynomialRotation.flagged_flags v q
  have hc := NativeUniformPolynomialRotation.flagged_core v q hcore
  have hs := UnitPhasePolynomialArray.source_endpoint (flagged v q) q (fun _ => blank) 0 xs hn hf hc
  have hout := NativeUniformPolynomialRotationSemantics.fixed_output_endpoint v q (fun _ => blank)
    (fun _ => blank) 0 0 xs hcore ho w hw
  have hwout := UnitPhasePolynomialArray.result_width q xs w hw
  have hlen : (serialized xs).length=ys.length := by rw [length xs w hw,length _ w hwout]
  have hshead : (raw v q columns xs).head 56=(serialized xs).length := by
    change (cleared (state (flagged v q) (UnitPhaseStreamData.contexts (fun _ => blank) 0 xs) q N)).head (56 : Fin 60)=_
    rw [length xs w hw]
    simpa [cleared,setTape,ButterflyStreamEndpoint.position_all 0 xs w hw] using hs.2

  have h1 := BlankWordReturnAt.runs (raw v q columns xs) (56 : Fin 64)
    (serialized xs) (nonblank xs) (by exact hs.1) hshead
  have h2 := BlankWordReturnAt.runs (rewindSource (raw v q columns xs) (serialized xs))
    (58 : Fin 64) ys (nonblank _) (by exact hout.1) (by
      change (cleared (state (flagged v q) (UnitPhaseStreamData.contexts (fun _ => blank) 0 xs) q N)).head (58 : Fin 60)=_
      rw [length _ w hwout]
      simpa using hout.2)

  have h3 := BlankWordOverwriteAt.runs
    (rewindBoth (raw v q columns xs) (serialized xs) ys)
    (56 : Fin 64) 58 (by decide) (serialized xs) ys hlen (nonblank _)
    (by exact ⟨rfl,rfl⟩) (by exact ⟨rfl,rfl⟩)
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) _
  rw [length xs w hw,length _ w hwout]
  omega

 theorem runs (v : Tapes 60 2) (columns w : ℕ) (xs : Fin N → Coefficient) (hn : 0<N)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hblank : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=0 ∧
      v.tape ⟨48+i.val,by omega⟩=(fun _ => blank))
    (hcore : coreBlank v)
    (hs : v.tape 56=putWord (fun _ => blank) 0 (serialized xs) ∧ v.head 56=0)
    (ho : v.tape 58=(fun _ => blank) ∧ v.head 58=0) :
    HoareTime program (fun z => z=bank v N columns)
      (fun z => z=output v (phase columns) columns xs) (cost N w) := by
  have h0 := NativeUniformPolynomialRotation.runs v
    (UnitPhaseStreamData.contexts (fun _ => blank) 0 xs) N columns w
    (UnitPhaseStreamData.widths _ _ _ w hw) hblank hcore (by
      rw [UnitPhaseStreamData.tape _ _ _ _ hn,UnitPhaseStreamData.start _ _ _ _ hn]
      simpa [ButterflyStreamData.full,ButterflyStreamData.position,CyclicRowCycle.rowPrefix,serialized] using hs)
    (UnitPhaseStreamData.adjacent _ _ _)
  have h1 := normalize v (phase columns) columns w xs hn hw hcore ho
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by unfold cost;omega)

 theorem negative_runs (v : Tapes 60 2) (columns w : ℕ) (xs : Fin N → Coefficient) (hn : 0<N)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hblank : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=0 ∧
      v.tape ⟨48+i.val,by omega⟩=(fun _ => blank))
    (hcore : coreBlank v)
    (hs : v.tape 56=putWord (fun _ => blank) 0 (serialized xs) ∧ v.head 56=0)
    (ho : v.tape 58=(fun _ => blank) ∧ v.head 58=0) :
    HoareTime negativeProgram (fun z => z=bank v N columns)
      (fun z => z=output v 2 columns xs) (cost N w) := by
  have h0 := NativeUniformPolynomialRotation.fixed_runs 2 v
    (UnitPhaseStreamData.contexts (fun _ => blank) 0 xs) N columns w
    (UnitPhaseStreamData.widths _ _ _ w hw) hblank hcore (by
      rw [UnitPhaseStreamData.tape _ _ _ _ hn,UnitPhaseStreamData.start _ _ _ _ hn]
      simpa [ButterflyStreamData.full,ButterflyStreamData.position,CyclicRowCycle.rowPrefix,serialized] using hs)
    (UnitPhaseStreamData.adjacent _ _ _)
  have h1 := normalize v 2 columns w xs hn hw hcore ho
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by unfold cost;omega)

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationNormalized
