import IntegerMultBounds.Machine.BinaryCorrectionOffsetRewind

/-! Build both actual subtraction operand tables from only original b/q/n
and controls. Every gather and every source/control/output rewind is paid.
The controlsAt source-prefix rewind preserves its unread b-stride suffix. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetPrepare
open SharedPlacementAlphabet (setTape)
open BinarySelectedOffsetData (source controls)
noncomputable section

def input (hs : Fin 3 → List Bool) (Z : List Bool) :=
  (BinarySelectedOffsetPrepare.input hs Z).append (FixedHeaderBankCopy.empty 14)
def prepared (hs : Fin 3 → List Bool) (Z : List Bool) (b n : ℕ) :=
  (BinarySelectedOffsetPrepare.output hs Z b n).append (FixedHeaderBankCopy.empty 14)
def selected (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  (BinarySelectedOffsetGather.after hs q b n Z hb hbq).append (FixedHeaderBankCopy.empty 14)
def selectedReady (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  (BinaryCorrectionOffsetGather.before hs Z b n (BinarySelectedOffsetGather.outputTape q b n Z hb hbq)).append (FixedHeaderBankCopy.empty 14)
def gathered (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  (BinaryCorrectionOffsetGather.after hs q b n Z (BinarySelectedOffsetGather.outputTape q b n Z hb hbq) hb hbq).append (FixedHeaderBankCopy.empty 14)
def output (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  (setTape (BinaryCorrectionOffsetGather.before hs Z b n (BinarySelectedOffsetGather.outputTape q b n Z hb hbq))
    9 (BinaryCorrectionOffsetGather.outputTape q b n Z hb hbq) 0).append (FixedHeaderBankCopy.empty 14)

def prepare := extend BinarySelectedOffsetPrepare.program 14
def rewindSelected := seq (seq (BinaryCorrectionOffsetRewind.program (6 : Fin 31))
  (BinaryCorrectionOffsetRewind.program (7 : Fin 31))) (BinaryCorrectionOffsetRewind.program (8 : Fin 31))
def rewindControls := seq (seq (BinaryCorrectionOffsetRewind.program (6 : Fin 31))
  (BinaryCorrectionOffsetRewind.program (7 : Fin 31))) (BinaryCorrectionOffsetRewind.program (9 : Fin 31))
def program : Program 31 992 0 := seq (seq (seq (seq prepare BinarySelectedOffsetGather.program) rewindSelected) BinaryCorrectionOffsetGather.program) rewindControls

theorem rewind_selected (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ)
    (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    HoareTime rewindSelected (fun z => z=selected hs Z q b n hb hbq)
      (fun z => z=selectedReady hs Z q b n hb hbq)
      ((n*2^(n*b))*b+n*2^(n*b)+(n*2^(n*b))*q+8) := by
  let v0 := selected hs Z q b n hb hbq
  let v1 := setTape v0 6 (v0.tape 6) 0
  let v2 := setTape v1 7 (v1.tape 7) 0
  have h0 := BinaryCorrectionOffsetRewind.runs (6 : Fin 31) v0 (source b n) ((n*2^(n*b))*b)
    (by rw [BinarySelectedOffsetData.source_length]) rfl rfl
  have h1 := BinaryCorrectionOffsetRewind.runs (7 : Fin 31) v1 (controls b n Z) (n*2^(n*b))
    (by rw [BinarySelectedOffsetData.controls_length b n Z hZ]) rfl rfl
  have h2 := BinaryCorrectionOffsetRewind.runs (8 : Fin 31) v2 (BinarySelectedOffsetData.word q b n hb hbq Z) ((n*2^(n*b))*q)
    (by rw [BinarySelectedOffsetData.word_length]) rfl rfl
  have he : setTape v2 8 (v2.tape 8) 0=selectedReady hs Z q b n hb hbq := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem controlWord_length (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    (BinaryCorrectionOffsetData.controlWord q b n Z hb hbq).length=(n*2^(n*b))*q :=
  Gather.gather_length _ _ _ _ _

theorem rewind_controls (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ)
    (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    HoareTime rewindControls (fun z => z=gathered hs Z q b n hb hbq)
      (fun z => z=output hs Z q b n hb hbq)
      (2*(n*2^(n*b))+(n*2^(n*b))*q+8) := by
  let v0 := gathered hs Z q b n hb hbq
  let v1 := setTape v0 6 (v0.tape 6) 0
  let v2 := setTape v1 7 (v1.tape 7) 0
  have h0 := BinaryCorrectionOffsetRewind.runs (6 : Fin 31) v0 (source b n) (n*2^(n*b))
    (by rw [BinarySelectedOffsetData.source_length]; exact Nat.le_mul_of_pos_right _ hb) rfl rfl
  have h1 := BinaryCorrectionOffsetRewind.runs (7 : Fin 31) v1 (controls b n Z) (n*2^(n*b))
    (by rw [BinarySelectedOffsetData.controls_length b n Z hZ]) rfl rfl
  have h2 := BinaryCorrectionOffsetRewind.runs (9 : Fin 31) v2 (BinaryCorrectionOffsetData.controlWord q b n Z hb hbq) ((n*2^(n*b))*q)
    (by rw [controlWord_length]) rfl rfl
  have he : setTape v2 9 (v2.tape 9) 0=output hs Z q b n hb hbq := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

def cost (q b n : ℕ) (Z : List Bool) := BinarySelectedOffsetPrepare.cost b n Z+
  640*((n*2^(n*b)+1)*(q+b+1))+(n*2^(n*b))*b+3*(n*2^(n*b))+2*((n*2^(n*b))*q)+20

theorem constructs (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z q b n hb hbq) (cost q b n Z) := by
  have h0 := hoare_extend_eq (BinarySelectedOffsetPrepare.runs hs Z b n hb hvb hvn (hc 0) (hc 2)) (FixedHeaderBankCopy.empty 14)
  have h1 := BinarySelectedOffsetGather.runs hs q b n Z hb hbq hvq hvb hc hZ
  rw [BinarySelectedOffsetGather.input_eq,BinarySelectedOffsetGather.input_eq] at h1
  have h2 := rewind_selected hs Z q b n hb hbq hZ
  have h3 := BinaryCorrectionOffsetGather.runs hs q b n Z (BinarySelectedOffsetGather.outputTape q b n Z hb hbq) hb hbq hvq hvb hc hZ
  rw [BinaryCorrectionOffsetGather.input_eq,BinaryCorrectionOffsetGather.input_eq] at h3
  have h4 := rewind_controls hs Z q b n hb hbq hZ
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.BinaryCorrectionOffsetPrepare
