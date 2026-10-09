import IntegerMultBounds.Machine.CountedPackedLine
import IntegerMultBounds.Machine.CountedGatherOriginalRun

/-! Uniform packed line from the six original shape/count descriptors.
All four derived descriptors and both clocks are physically constructed and
erased. The payload heads and offset scratch are restored by real tape routines. -/
namespace IntegerMultBounds.Machine.CountedPackedOriginalLine
noncomputable section
variable {a : ℕ}
open ColumnTransducer (Rule)

def focus : Fin 9 → Fin 11 := ![0,1,2,5,6,7,8,9,10]
theorem focus_injective : Function.Injective focus := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [focus] at h

def caller (v : Tapes 5 a) (hs : Fin 6 → List Bool) :=
  v.append (FixedHeaderBankCopy.headerBank hs)
def bank (v : Tapes 5 a) (hs : Fin 6 → List Bool) :=
  CountedGatherOriginalRun.input (caller v hs)
def program (op : Bool → Bool → Bool) {s : ℕ} (R : Rule s) (a : ℕ) :=
  seq (CountedGatherOriginalRun.program (a := a) op focus focus_injective)
    (extend (CountedPackedLine.finish R a) 12)
def cost (S : Gather.Shape) (n m : ℕ) (hs : Fin 6 → List Bool) :=
  CountedGatherOriginalRun.cost S n hs+1+CountedPackedLine.finishCost S n m

theorem append_assoc (v : Tapes 5 a) (w z : Tapes 6 a) :
    (v.append w).append z = v.append (w.append z) := by
  unfold Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem result_bank (f0 f1 f2 f3 f4 target : ℤ → Fin (a+4))
    (p0 p1 p2 p3 p4 px pz pt : ℤ) (hs : Fin 6 → List Bool) :
    CountedGatherOriginalRun.result (caller (PackedLine.bank f0 f1 f2 f3 f4 p0 p1 p2 p3 p4) hs)
      focus target px pz pt =
      caller (PackedLine.bank f0 f1 target f3 f4 px pz pt p3 p4) hs := by
  unfold CountedGatherOriginalRun.result SharedPlacementAlphabet.setTape caller
    PackedLine.bank Tapes.append focus
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem original_tapes (v : Tapes 5 a) (hs : Fin 6 → List Bool) (i : Fin 6) :
    (caller v hs).tape (focus (Fin.natAdd 3 i)) = RadixZeroFill.encodedBinary (hs i) := by
  fin_cases i <;> rfl

theorem original_heads (v : Tapes 5 a) (hs : Fin 6 → List Bool) (i : Fin 6) :
    (caller v hs).head (focus (Fin.natAdd 3 i)) = 1 := by
  fin_cases i <;> rfl

variable (op : Bool → Bool → Bool) (S : Gather.Shape) {s : ℕ} (R : Rule s) (xs zs acc : List Bool)
  (f g h : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 : ℤ)

/-- Only the original six canonical headers are supplied. Private descriptors
and clocks start and finish blank at head zero, while all original headers are retained. -/
theorem line_hoare (hs : Fin 6 → List Bool)
    (hxs : zs.length*S.sx ≤ xs.length) (hacc : acc.length = zs.length*S.st)
    (hv : ∀ i, Counter.value (hs i) = CountedGatherMetadata.originalValues S zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) :
    HoareTime (program op R a)
      (fun v => v = bank (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4) hs)
      (fun v => v = bank (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4
          ((ColumnTransducer.digits R 0 (acc.zip (Gather.gather op S xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4) hs)
      (cost S zs.length acc.length hs) := by
  let payload := PackedLine.bank (putWord f p0 (xs.map (bitSymbol (a := a))))
    (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
    (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4
  have h1 := CountedGatherOriginalRun.runs (caller payload hs) focus focus_injective op S xs zs
    f g (fun _ => blank) p0 p1 p2 hs hv hc (original_tapes payload hs) (original_heads payload hs)
    rfl rfl rfl rfl rfl rfl hxs
  rw [result_bank] at h1
  have h2 := hoare_extend_eq (CountedPackedLine.finish_hoare op S R xs zs acc f g h p0 p1 p2 p3 p4
    hxs hacc hf hg hh hh')
    ((FixedHeaderBankCopy.headerBank (a := a) hs).append (FixedHeaderBankCopy.empty 6))
  rw [← append_assoc,← append_assoc] at h2
  exact h1.seq h2

theorem cost_linear (S : Gather.Shape) (n m : ℕ) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedGatherMetadata.originalValues S n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost S n m hs ≤ 190*((n+1)*(S.sx+S.st+1))+3*m := by
  have hg := CountedGatherOriginalRun.cost_linear S n hs hv hc
  unfold cost CountedPackedLine.finishCost
  nlinarith

/-- Uniform full line cost includes descriptor synthesis, both counted loops,
all joins and cleanup, including zero-digit and zero-stride cases. -/
theorem runs (hs : Fin 6 → List Bool)
    (hxs : zs.length*S.sx ≤ xs.length) (hacc : acc.length = zs.length*S.st)
    (hv : ∀ i, Counter.value (hs i) = CountedGatherMetadata.originalValues S zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) :
    HoareTime (program op R a)
      (fun v => v = bank (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4) hs)
      (fun v => v = bank (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4
          ((ColumnTransducer.digits R 0 (acc.zip (Gather.gather op S xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4) hs)
      (190*((zs.length+1)*(S.sx+S.st+1))+3*acc.length) :=
  (line_hoare op S R xs zs acc f g h p0 p1 p2 p3 p4 hs hxs hacc hv hc hf hg hh hh').consequence
    (fun _ h => h) (fun _ h => h) (cost_linear S zs.length acc.length hs hv hc)

end
end IntegerMultBounds.Machine.CountedPackedOriginalLine
