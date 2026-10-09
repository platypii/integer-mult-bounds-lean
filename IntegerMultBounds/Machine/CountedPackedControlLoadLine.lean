import IntegerMultBounds.Machine.CountedPackedOriginalLine
import IntegerMultBounds.Machine.CountedPackedControlLoadHeaders

/-! A packed line from only the runtime b/count descriptors. All six shape
headers, four derived descriptors and two clocks are physically synthesized
and erased; none occur as initialized private state in the contract. -/
namespace IntegerMultBounds.Machine.CountedPackedControlLoadLine
noncomputable section
variable {a : ℕ}
open ColumnTransducer (Rule)
open CountedPackedControlLoadHeaders (shape words)

def source : Fin 2 → Fin 7 := ![5,6]
def caller (payload : Tapes 5 a) (hs : Fin 2 → List Bool) :=
  payload.append (FixedHeaderBankCopy.headerBank hs)
def input (payload : Tapes 5 a) (hs : Fin 2 → List Bool) :=
  (CountedPackedControlLoadHeaders.input (caller payload hs)).append (FixedHeaderBankCopy.empty 6)
def ready (payload : Tapes 5 a) (hs : Fin 2 → List Bool) :=
  (CountedPackedControlLoadHeaders.output (caller payload hs) hs).append (FixedHeaderBankCopy.empty 6)
def extra (hs : Fin 2 → List Bool) : Tapes 4 a :=
  ((FixedHeaderBankCopy.headerBank hs).append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 1)
def placement : Fin (17+4) ≃ Fin 21 where
  toFun := ![0,1,2,3,4,9,10,11,12,13,14,15,16,17,18,19,20,5,6,7,8]
  invFun := ![0,1,2,3,4,17,18,19,20,5,6,7,8,9,10,11,12,13,14,15,16]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem placed_bank (payload : Tapes 5 a) (hs : Fin 2 → List Bool) :
    ((CountedPackedOriginalLine.bank payload (words hs)).append (extra hs)).reindex placement =
      ready payload hs := by
  unfold CountedPackedOriginalLine.bank CountedPackedOriginalLine.caller CountedGatherOriginalRun.input
    ready caller extra CountedPackedControlLoadHeaders.output Tapes.append Tapes.reindex placement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem source_tapes (payload : Tapes 5 a) (hs : Fin 2 → List Bool) (i : Fin 2) :
    (caller payload hs).tape (source i) = RadixZeroFill.encodedBinary (hs i) := by
  fin_cases i <;> rfl
theorem source_heads (payload : Tapes 5 a) (hs : Fin 2 → List Bool) (i : Fin 2) :
    (caller payload hs).head (source i) = 1 := by
  fin_cases i <;> rfl

def setup (a : ℕ) := extend
  (CountedPackedControlLoadHeaders.program (a := a) source) 6
def cleanup (a : ℕ) := extend (CountedPackedControlLoadHeaders.cleanup (a := a) (t := 7)) 6
def line (op : Bool → Bool → Bool) {s : ℕ} (R : Rule s) (a : ℕ) :=
  reindex (extend (CountedPackedOriginalLine.program op R a) 4) placement
/-- Only the static bit operation and modular rule enter finite control. -/
def program (op : Bool → Bool → Bool) {s : ℕ} (R : Rule s) (a : ℕ) :=
  seq (seq (setup a) (line op R a)) (cleanup a)

def cost (b n m : ℕ) (hb : 1 ≤ b) (hs : Fin 2 → List Bool) :=
  92*(b+n+1)+CountedPackedOriginalLine.cost (shape b hb) n m (words hs)+
    54*(b+n+1)+2

variable (op : Bool → Bool → Bool) {s : ℕ} (R : Rule s)
  (b : ℕ) (hb : 1 ≤ b) (xs zs acc : List Bool)
  (f g h : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 : ℤ)

/-- Exact modular packed-line execution from the original b/count headers.
Every private tape is blank again and all five payload heads return to origin. -/
theorem line_hoare (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedControlLoadHeaders.originalValues b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hxs : zs.length*(shape b hb).sx ≤ xs.length)
    (hacc : acc.length = zs.length*(shape b hb).st)
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) :
    HoareTime (program op R a)
      (fun v => v = input (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4) hs)
      (fun v => v = input (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4 ((ColumnTransducer.digits R 0
          (acc.zip (Gather.gather op (shape b hb) xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4) hs)
      (cost b zs.length acc.length hb hs) := by
  let payload := PackedLine.bank (putWord f p0 (xs.map (bitSymbol (a := a))))
    (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
    (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4
  let final := PackedLine.bank (putWord f p0 (xs.map (bitSymbol (a := a))))
    (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
    (putWord h p3 (acc.map bitSymbol))
    (putWord (fun _ => blank) p4 ((ColumnTransducer.digits R 0
      (acc.zip (Gather.gather op (shape b hb) xs zs zs.length))).map bitSymbol)) p0 p1 p2 p3 p4
  have h1 := hoare_extend_eq (CountedPackedControlLoadHeaders.constructs source (caller payload hs)
    b zs.length hs hv hc (source_tapes payload hs) (source_heads payload hs)) (FixedHeaderBankCopy.empty 6)
  have h2 := hoare_place (CountedPackedOriginalLine.line_hoare op (shape b hb) R
    xs zs acc f g h p0 p1 p2 p3 p4 (words hs) hxs hacc
    (CountedPackedControlLoadHeaders.words_values b zs.length hb hs hv)
    (CountedPackedControlLoadHeaders.words_canonical hs hc) hf hg hh hh') placement (extra hs)
  rw [placed_bank,placed_bank] at h2
  have h3 := hoare_extend_eq (CountedPackedControlLoadHeaders.cleans (caller final hs)
    b zs.length hs hv hc) (FixedHeaderBankCopy.empty 6)
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) _
  unfold cost
  omega

theorem cost_linear (b n m : ℕ) (hb : 1 ≤ b) (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedControlLoadHeaders.originalValues b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost b n m hb hs ≤ 340*((n+1)*(b+2))+3*m := by
  have hl := CountedPackedOriginalLine.cost_linear (shape b hb) n m (words hs)
    (CountedPackedControlLoadHeaders.words_values b n hb hs hv)
    (CountedPackedControlLoadHeaders.words_canonical hs hc)
  simp only [shape] at hl
  rw [show 1+b+1 = b+2 by omega] at hl
  have hbig : b+n+1 ≤ (n+1)*(b+2) := by nlinarith
  have hp : 1 ≤ (n+1)*(b+2) := by nlinarith
  unfold cost
  simp only [shape]
  omega

/-- Full paid runtime bound includes shape preparation and inverse cleanup. -/
theorem runs (hs : Fin 2 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedControlLoadHeaders.originalValues b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hxs : zs.length*(shape b hb).sx ≤ xs.length)
    (hacc : acc.length = zs.length*(shape b hb).st)
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) :
    HoareTime (program op R a)
      (fun v => v = input (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4) hs)
      (fun v => v = input (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4 ((ColumnTransducer.digits R 0
          (acc.zip (Gather.gather op (shape b hb) xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4) hs)
      (340*((zs.length+1)*(b+2))+3*acc.length) :=
  (line_hoare op R b hb xs zs acc f g h p0 p1 p2 p3 p4 hs hv hc hxs hacc hf hg hh hh').consequence
    (fun _ h => h) (fun _ h => h) (cost_linear b zs.length acc.length hb hs hv hc)

end
end IntegerMultBounds.Machine.CountedPackedControlLoadLine
