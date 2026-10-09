import IntegerMultBounds.Machine.BinaryAddressOffsetPrepare
import IntegerMultBounds.Machine.CountedGatherOriginalRun

/-! Actual original-header gather over the physically generated address table.
Its q/b/count shape is installed and erased; all fourteen private metadata
tapes start and finish blank. Payload scans advance by the exact full lengths. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetGather
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetData
noncomputable section

def hs' (hs : Fin 3 → List Bool) (q n : ℕ) : Fin 3 → List Bool :=
  ![hs 0,hs 1,BinaryAddressOffsetHeaders.countBits q n]
def ports : Fin 3 → Fin 16 := ![0,1,5]
def focus : Fin 9 → Fin 24 := ![6,7,8,18,19,20,21,22,23]
theorem focus_injective : Function.Injective focus := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | norm_num [focus] at h

def input (caller : Tapes 16 0) :=
  (CountedPackedShapeHeaders.input caller).append (FixedHeaderBankCopy.empty 6)
def ready (caller : Tapes 16 0) (hs : Fin 3 → List Bool) :=
  (CountedPackedShapeHeaders.output caller 1 hs).append (FixedHeaderBankCopy.empty 6)
def setup := extend (CountedPackedShapeHeaders.program (a := 0) 1 ports) 6
def core := CountedGatherOriginalRun.program (a := 0) (fun x _ => x) focus focus_injective
def cleanup := extend (CountedPackedShapeHeaders.cleanup (a := 0) (t := 16)) 6
def program := seq (seq setup core) cleanup

theorem input_eq (caller : Tapes 16 0) : input caller=caller.append (FixedHeaderBankCopy.empty 14) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def before (hs : Fin 3 → List Bool) (q n : ℕ) := BinaryAddressOffsetPrepare.output hs q n
def outputTape (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  putWord (fun _ => blank) 0 ((word q b n hb hbq).map (bitSymbol (a := 0)))
def after (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  setTape (setTape (setTape (before hs q n) 6 ((before hs q n).tape 6) ((n*2^(n*q))*q))
    7 ((before hs q n).tape 7) (1+n*2^(n*q))) 8 (outputTape q b n hb hbq) ((n*2^(n*q))*b)

theorem header_values (hs : Fin 3 → List Bool) (q b n : ℕ)
    (hq : Counter.value (hs 0)=q) (hb : Counter.value (hs 1)=b) :
    ∀ i, Counter.value (hs' hs q n i)=CountedPackedShapeHeaders.originalValues q b (n*2^(n*q)) i := by
  intro i; fin_cases i
  · exact hq
  · exact hb
  · exact DimensionProductDescriptor.bits_value n (2^(n*q))

theorem header_canonical (hs : Fin 3 → List Bool) (q n : ℕ)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (hs' hs q n i) := by
  intro i; fin_cases i
  · exact hc 0
  · exact hc 1
  · exact DimensionProductDescriptor.bits_canonical n (2^(n*q))

theorem core_runs (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime core (fun z => z=ready (before hs q n) (hs' hs q n))
      (fun z => z=ready (after hs q b n hb hbq) (hs' hs q n))
      (169*((n*2^(n*q)+1)*(q+b+1))) := by
  let v := CountedPackedShapeHeaders.output (before hs q n) 1 (hs' hs q n)
  let hs6 := CountedPackedShapeHeaders.words 1 (hs' hs q n)
  have hv := CountedPackedShapeHeaders.words_values 1 q b (n*2^(n*q)) hb hbq
    (hs' hs q n) (header_values hs q b n hvq hvb)
  have hh := CountedGatherOriginalRun.runs v focus focus_injective (fun x _ => x)
    (PackedArith.parity q b hb hbq) (source q n) (dummy q n)
    (fun _ => blank) CountedCopyReuse.empty (fun _ => blank) 0 1 0 hs6
    (by simpa only [dummy_length,CountedPackedShapeHeaders.shape,hs6,Matrix.cons_val_one,Matrix.cons_val_zero] using hv)
    (CountedPackedShapeHeaders.words_canonical 1 (hs' hs q n) (header_canonical hs q n hc))
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    rfl (by exact BinaryAddressTableStep.bits_word _ _ _) rfl rfl rfl rfl
    (by simp only [dummy_length,source_length]; rfl)
  have he : CountedGatherOriginalRun.result v focus
      (putWord (fun _ => blank) 0 ((Gather.gather (fun x _ => x) (PackedArith.parity q b hb hbq)
        (source q n) (dummy q n) (dummy q n).length).map bitSymbol))
      (0+(dummy q n).length*(PackedArith.parity q b hb hbq).sx)
      (1+(dummy q n).length) (0+(dummy q n).length*(PackedArith.parity q b hb hbq).st) =
      CountedPackedShapeHeaders.output (after hs q b n hb hbq) 1 (hs' hs q n) := by
    simp only [dummy_length]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | (change (0 : ℤ)+(n*2^(n*q) : ℕ)*q=((n*2^(n*q))*q : ℕ); push_cast; ring) | (change (0 : ℤ)+(n*2^(n*q) : ℕ)*b=((n*2^(n*q))*b : ℕ); push_cast; ring)
  rw [he] at hh
  apply hh.consequence (fun _ h => h) (fun _ h => h) _
  have hcost := CountedGatherOriginalRun.cost_linear (PackedArith.parity q b hb hbq)
    (n*2^(n*q)) hs6 hv
    (CountedPackedShapeHeaders.words_canonical 1 (hs' hs q n) (header_canonical hs q n hc))
  simpa only [dummy_length,PackedArith.parity] using hcost

theorem runs (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun z => z=input (before hs q n))
      (fun z => z=input (after hs q b n hb hbq))
      (320*((n*2^(n*q)+1)*(q+b+1))) := by
  have hv := header_values hs q b n hvq hvb
  have hcanon := header_canonical hs q n hc
  have h0 := hoare_extend_eq (CountedPackedShapeHeaders.constructs 1 ports (before hs q n)
    q b (n*2^(n*q)) (hs' hs q n) hv hcanon
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)) (FixedHeaderBankCopy.empty 6)
  have h1 := core_runs hs q b n hb hbq hvq hvb hc
  have h2 := hoare_extend_eq (CountedPackedShapeHeaders.cleans 1 (after hs q b n hb hbq)
    q b (n*2^(n*q)) (hs' hs q n) hv hcanon) (FixedHeaderBankCopy.empty 6)
  have hd (a b c : ℕ) : a+b+c+1 ≤ (c+1)*(a+b+1) := by nlinarith
  have hdim := hd q b (n*2^(n*q))
  have hpos : 1 ≤ (n*2^(n*q)+1)*(q+b+1) := Nat.mul_pos (by omega) (by omega)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryAddressOffsetGather
