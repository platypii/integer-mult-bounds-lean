import IntegerMultBounds.Machine.BinaryCorrectionOffsetData
import IntegerMultBounds.Machine.CountedGatherOriginalRun

/-! Actual original-header gather over the physically generated address table.
Its q/b/count shape is installed and erased; all fourteen private metadata
tapes start and finish blank. Payload scans advance by the exact full lengths. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetGather
open SharedPlacementAlphabet (setTape)
open BinarySelectedOffsetData (source controls controls_length source_length)
open BinaryCorrectionOffsetData (controlWord)
noncomputable section

def hs' (hs : Fin 3 → List Bool) (b n : ℕ) : Fin 3 → List Bool :=
  ![hs 1,hs 0,BinaryAddressOffsetHeaders.countBits b n]
def ports : Fin 3 → Fin 17 := ![1,0,5]
def focus : Fin 9 → Fin 25 := ![6,7,9,19,20,21,22,23,24]
theorem focus_injective : Function.Injective focus := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | norm_num [focus] at h

def input (caller : Tapes 17 0) :=
  (CountedPackedShapeHeaders.input caller).append (FixedHeaderBankCopy.empty 6)
def ready (caller : Tapes 17 0) (hs : Fin 3 → List Bool) :=
  (CountedPackedShapeHeaders.output caller 2 hs).append (FixedHeaderBankCopy.empty 6)
def setup := extend (CountedPackedShapeHeaders.program (a := 0) 2 ports) 6
def core := CountedGatherOriginalRun.program (a := 0) (fun _ z => z) focus focus_injective
def cleanup := extend (CountedPackedShapeHeaders.cleanup (a := 0) (t := 17)) 6
def program := seq (seq setup core) cleanup

theorem input_eq (caller : Tapes 17 0) : input caller=caller.append (FixedHeaderBankCopy.empty 14) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def before (hs : Fin 3 → List Bool) (Z : List Bool) (b n : ℕ) (selected : ℤ → Fin 4) :=
  setTape (BinarySelectedOffsetPrepare.output hs Z b n) 8 selected 0
def outputTape (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  putWord (fun _ => blank) 0 ((controlWord q b n Z hb hbq).map (bitSymbol (a := 0)))
def after (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (selected : ℤ → Fin 4) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  setTape (setTape (setTape (before hs Z b n selected) 6 ((before hs Z b n selected).tape 6) (n*2^(n*b)))
    7 ((before hs Z b n selected).tape 7) (n*2^(n*b))) 9 (outputTape q b n Z hb hbq) ((n*2^(n*b))*q)

theorem header_values (hs : Fin 3 → List Bool) (q b n : ℕ)
    (hq : Counter.value (hs 1)=q) (hb : Counter.value (hs 0)=b) :
    ∀ i, Counter.value (hs' hs b n i)=CountedPackedShapeHeaders.originalValues q b (n*2^(n*b)) i := by
  intro i; fin_cases i
  · exact hq
  · exact hb
  · exact DimensionProductDescriptor.bits_value n (2^(n*b))

theorem header_canonical (hs : Fin 3 → List Bool) (b n : ℕ)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (hs' hs b n i) := by
  intro i; fin_cases i
  · exact hc 1
  · exact hc 0
  · exact DimensionProductDescriptor.bits_canonical n (2^(n*b))

theorem core_runs (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (selected : ℤ → Fin 4) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime core (fun z => z=ready (before hs Z b n selected) (hs' hs b n))
      (fun z => z=ready (after hs q b n Z selected hb hbq) (hs' hs b n))
      (169*((n*2^(n*b)+1)*(q+b+1))) := by
  let v := CountedPackedShapeHeaders.output (before hs Z b n selected) 2 (hs' hs b n)
  let hs6 := CountedPackedShapeHeaders.words 2 (hs' hs b n)
  have hv := CountedPackedShapeHeaders.words_values 2 q b (n*2^(n*b)) hb hbq
    (hs' hs b n) (header_values hs q b n hvq hvb)
  have hh := CountedGatherOriginalRun.runs v focus focus_injective (fun _ z => z)
    (PackedArith.controlsAt q b hb hbq) (source b n) (controls b n Z)
    (fun _ => blank) (fun _ => blank) (fun _ => blank) 0 0 0 hs6
    (by rw [controls_length b n Z hZ]; exact hv)
    (CountedPackedShapeHeaders.words_canonical 2 (hs' hs b n) (header_canonical hs b n hc))
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    rfl rfl rfl rfl rfl rfl
    (by simp only [controls_length b n Z hZ,source_length,PackedArith.controlsAt,Nat.mul_one]; exact Nat.le_mul_of_pos_right _ hb)
  have he : CountedGatherOriginalRun.result v focus
      (putWord (fun _ => blank) 0 ((Gather.gather (fun _ z => z) (PackedArith.controlsAt q b hb hbq)
        (source b n) (controls b n Z) (controls b n Z).length).map bitSymbol))
      (0+(controls b n Z).length*(PackedArith.controlsAt q b hb hbq).sx)
      (0+(controls b n Z).length) (0+(controls b n Z).length*(PackedArith.controlsAt q b hb hbq).st) =
      CountedPackedShapeHeaders.output (after hs q b n Z selected hb hbq) 2 (hs' hs b n) := by
    simp only [controls_length b n Z hZ]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change (0 : ℤ)+(n*2^(n*b) : ℕ)*q=((n*2^(n*b))*q : ℕ); push_cast; ring) | (change (0 : ℤ)+(n*2^(n*b) : ℕ)*1=((n*2^(n*b)) : ℕ); push_cast; ring) | (change (0 : ℤ)+(n*2^(n*b) : ℕ)=((n*2^(n*b)) : ℕ); ring)
  rw [he] at hh
  apply hh.consequence (fun _ h => h) (fun _ h => h) _
  have hcost := CountedGatherOriginalRun.cost_linear (PackedArith.controlsAt q b hb hbq)
    (n*2^(n*b)) hs6 hv
    (CountedPackedShapeHeaders.words_canonical 2 (hs' hs b n) (header_canonical hs b n hc))
  simp only [PackedArith.controlsAt] at hcost
  simp only [controls_length b n Z hZ] at *
  exact hcost.trans (by nlinarith)

theorem runs (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (selected : ℤ → Fin 4) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input (before hs Z b n selected))
      (fun z => z=input (after hs q b n Z selected hb hbq))
      (320*((n*2^(n*b)+1)*(q+b+1))) := by
  have hv := header_values hs q b n hvq hvb
  have hcanon := header_canonical hs b n hc
  have h0 := hoare_extend_eq (CountedPackedShapeHeaders.constructs 2 ports (before hs Z b n selected)
    q b (n*2^(n*b)) (hs' hs b n) hv hcanon
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)) (FixedHeaderBankCopy.empty 6)
  have h1 := core_runs hs q b n Z selected hb hbq hvq hvb hc hZ
  have h2 := hoare_extend_eq (CountedPackedShapeHeaders.cleans 2 (after hs q b n Z selected hb hbq)
    q b (n*2^(n*b)) (hs' hs b n) hv hcanon) (FixedHeaderBankCopy.empty 6)
  have hd (a b c : ℕ) : a+b+c+1 ≤ (c+1)*(a+b+1) := by nlinarith
  have hdim := hd q b (n*2^(n*b))
  have hpos : 1 ≤ (n*2^(n*b)+1)*(q+b+1) := Nat.mul_pos (by omega) (by omega)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryCorrectionOffsetGather
