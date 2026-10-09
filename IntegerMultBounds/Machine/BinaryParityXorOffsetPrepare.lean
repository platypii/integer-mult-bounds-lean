import IntegerMultBounds.Machine.BinaryCorrectionOffsetRewind
import IntegerMultBounds.Machine.BinaryParityXorOffsetGather

/-! Construct the positive parity-XOR table from original q/b/n and controls,
with every gather and all three payload rewinds charged. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetPrepare
open SharedPlacementAlphabet (setTape)
open BinaryParityXorOffsetData (source controls)
noncomputable section

def input (hs : Fin 3 → List Bool) (Z : List Bool) :=
  (BinarySelectedOffsetPrepare.input hs Z).append (FixedHeaderBankCopy.empty 14)
def prepared (hs : Fin 3 → List Bool) (Z : List Bool) (q n : ℕ) :=
  (BinarySelectedOffsetPrepare.output hs Z q n).append (FixedHeaderBankCopy.empty 14)
def selected (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  (BinaryParityXorOffsetGather.after hs q b n Z hb hbq).append (FixedHeaderBankCopy.empty 14)
def output (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  (setTape (BinarySelectedOffsetPrepare.output hs Z q n) 8
    (BinaryParityXorOffsetGather.outputTape q b n Z hb hbq) 0).append (FixedHeaderBankCopy.empty 14)

def prepare := extend BinarySelectedOffsetPrepare.program 14
def rewindSelected := seq (seq (BinaryCorrectionOffsetRewind.program (6 : Fin 31))
  (BinaryCorrectionOffsetRewind.program (7 : Fin 31))) (BinaryCorrectionOffsetRewind.program (8 : Fin 31))
def program := seq (seq prepare BinaryParityXorOffsetGather.program) rewindSelected

theorem rewind_selected (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ)
    (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    HoareTime rewindSelected (fun z => z=selected hs Z q b n hb hbq)
      (fun z => z=output hs Z q b n hb hbq)
      ((n*2^(n*q))*b+n*2^(n*q)+(n*2^(n*q))*q+8) := by
  let v0 := selected hs Z q b n hb hbq
  let v1 := setTape v0 6 (v0.tape 6) 0
  let v2 := setTape v1 7 (v1.tape 7) 0
  have h0 := BinaryCorrectionOffsetRewind.runs (6 : Fin 31) v0 (source q n) ((n*2^(n*q))*q)
    (by rw [BinaryParityXorOffsetData.source_length]) rfl rfl
  have h1 := BinaryCorrectionOffsetRewind.runs (7 : Fin 31) v1 (controls q n Z) (n*2^(n*q))
    (by rw [BinaryParityXorOffsetData.controls_length q n Z hZ]) rfl rfl
  have h2 := BinaryCorrectionOffsetRewind.runs (8 : Fin 31) v2 (BinaryParityXorOffsetData.positiveWord q b n Z hb hbq) ((n*2^(n*q))*b)
    (by rw [BinaryParityXorOffsetData.positiveWord_length]) rfl rfl
  have he : setTape v2 8 (v2.tape 8) 0=output hs Z q b n hb hbq := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

def cost (q b n : ℕ) (Z : List Bool) := BinarySelectedOffsetPrepare.cost q n Z+
  320*((n*2^(n*q)+1)*(q+b+1))+(n*2^(n*q))*b+n*2^(n*q)+((n*2^(n*q))*q)+10

theorem constructs (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z q b n hb hbq) (cost q b n Z) := by
  have h0 := hoare_extend_eq (BinarySelectedOffsetPrepare.runs hs Z q n (by omega) hvq hvn (hc 0) (hc 2)) (FixedHeaderBankCopy.empty 14)
  have h1 := BinaryParityXorOffsetGather.runs hs q b n Z hb hbq hvq hvb hc hZ
  rw [BinaryParityXorOffsetGather.input_eq,BinaryParityXorOffsetGather.input_eq] at h1
  have h2 := rewind_selected hs Z q b n hb hbq hZ
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.BinaryParityXorOffsetPrepare
