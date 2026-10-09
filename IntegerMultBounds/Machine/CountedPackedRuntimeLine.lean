import IntegerMultBounds.Machine.CountedPackedOriginalLine
import IntegerMultBounds.Machine.CountedPackedShapeHeaders

/-! A packed line from only the runtime q/b/n descriptors. All six shape
headers, four derived descriptors and two clocks are physically synthesized
and erased; none occur as initialized private state in the contract. -/
namespace IntegerMultBounds.Machine.CountedPackedRuntimeLine
noncomputable section
variable {a : ℕ}
open ColumnTransducer (Rule)
open CountedPackedShapeHeaders (shape words)

def source : Fin 3 → Fin 8 := ![5,6,7]
def caller (payload : Tapes 5 a) (hs : Fin 3 → List Bool) :=
  payload.append (FixedHeaderBankCopy.headerBank hs)
def input (payload : Tapes 5 a) (hs : Fin 3 → List Bool) :=
  (CountedPackedShapeHeaders.input (caller payload hs)).append (FixedHeaderBankCopy.empty 6)
def ready (payload : Tapes 5 a) (kind : Fin 3) (hs : Fin 3 → List Bool) :=
  (CountedPackedShapeHeaders.output (caller payload hs) kind hs).append (FixedHeaderBankCopy.empty 6)
def extra (hs : Fin 3 → List Bool) : Tapes 5 a :=
  ((FixedHeaderBankCopy.headerBank hs).append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 1)
def placement : Fin (17+5) ≃ Fin 22 where
  toFun := ![0,1,2,3,4,10,11,12,13,14,15,16,17,18,19,20,21,5,6,7,8,9]
  invFun := ![0,1,2,3,4,17,18,19,20,21,5,6,7,8,9,10,11,12,13,14,15,16]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem placed_bank (payload : Tapes 5 a) (kind : Fin 3) (hs : Fin 3 → List Bool) :
    ((CountedPackedOriginalLine.bank payload (words kind hs)).append (extra hs)).reindex placement =
      ready payload kind hs := by
  unfold CountedPackedOriginalLine.bank CountedPackedOriginalLine.caller CountedGatherOriginalRun.input
    ready caller extra CountedPackedShapeHeaders.output Tapes.append Tapes.reindex placement
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem source_tapes (payload : Tapes 5 a) (hs : Fin 3 → List Bool) (i : Fin 3) :
    (caller payload hs).tape (source i) = RadixZeroFill.encodedBinary (hs i) := by
  fin_cases i <;> rfl
theorem source_heads (payload : Tapes 5 a) (hs : Fin 3 → List Bool) (i : Fin 3) :
    (caller payload hs).head (source i) = 1 := by
  fin_cases i <;> rfl

def setup (kind : Fin 3) (a : ℕ) := extend
  (CountedPackedShapeHeaders.program (a := a) kind source) 6
def cleanup (a : ℕ) := extend (CountedPackedShapeHeaders.cleanup (a := a) (t := 8)) 6
def line (_kind : Fin 3) (op : Bool → Bool → Bool) {s : ℕ} (R : Rule s) (a : ℕ) :=
  reindex (extend (CountedPackedOriginalLine.program op R a) 5) placement
/-- Only the static line kind, bit operation and modular rule enter finite control. -/
def program (kind : Fin 3) (op : Bool → Bool → Bool) {s : ℕ} (R : Rule s) (a : ℕ) :=
  seq (seq (setup kind a) (line kind op R a)) (cleanup a)

def cost (kind : Fin 3) (q b n m : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (hs : Fin 3 → List Bool) :=
  92*(q+b+n+1)+CountedPackedOriginalLine.cost (shape kind q b hb hbq) n m (words kind hs)+
    54*(q+b+n+1)+2

theorem shape_stride_bound (kind : Fin 3) (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :
    (shape kind q b hb hbq).sx+(shape kind q b hb hbq).st+1 ≤ 2*(q+b+1) := by
  fin_cases kind
  · change b+q+1 ≤ 2*(q+b+1); omega
  · change q+b+1 ≤ 2*(q+b+1); omega
  · change 1+q+1 ≤ 2*(q+b+1); omega

variable (kind : Fin 3) (op : Bool → Bool → Bool) {s : ℕ} (R : Rule s)
  (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (xs zs acc : List Bool)
  (f g h : ℤ → Fin (a+4)) (p0 p1 p2 p3 p4 : ℤ)

/-- Exact modular packed-line execution from the original q/b/count headers.
Every private tape is blank again and all five payload heads return to origin. -/
theorem line_hoare (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hxs : zs.length*(shape kind q b hb hbq).sx ≤ xs.length)
    (hacc : acc.length = zs.length*(shape kind q b hb hbq).st)
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) :
    HoareTime (program kind op R a)
      (fun v => v = input (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4) hs)
      (fun v => v = input (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4 ((ColumnTransducer.digits R 0
          (acc.zip (Gather.gather op (shape kind q b hb hbq) xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4) hs)
      (cost kind q b zs.length acc.length hb hbq hs) := by
  let payload := PackedLine.bank (putWord f p0 (xs.map (bitSymbol (a := a))))
    (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
    (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4
  let final := PackedLine.bank (putWord f p0 (xs.map (bitSymbol (a := a))))
    (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
    (putWord h p3 (acc.map bitSymbol))
    (putWord (fun _ => blank) p4 ((ColumnTransducer.digits R 0
      (acc.zip (Gather.gather op (shape kind q b hb hbq) xs zs zs.length))).map bitSymbol)) p0 p1 p2 p3 p4
  have h1 := hoare_extend_eq (CountedPackedShapeHeaders.constructs kind source (caller payload hs)
    q b zs.length hs hv hc (source_tapes payload hs) (source_heads payload hs)) (FixedHeaderBankCopy.empty 6)
  have h2 := hoare_place (CountedPackedOriginalLine.line_hoare op (shape kind q b hb hbq) R
    xs zs acc f g h p0 p1 p2 p3 p4 (words kind hs) hxs hacc
    (CountedPackedShapeHeaders.words_values kind q b zs.length hb hbq hs hv)
    (CountedPackedShapeHeaders.words_canonical kind hs hc) hf hg hh hh') placement (extra hs)
  rw [placed_bank,placed_bank] at h2
  have h3 := hoare_extend_eq (CountedPackedShapeHeaders.cleans kind (caller final hs)
    q b zs.length hs hv hc) (FixedHeaderBankCopy.empty 6)
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) _
  unfold cost
  omega

theorem cost_linear (kind : Fin 3) (q b n m : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost kind q b n m hb hbq hs ≤ 530*((n+1)*(q+b+1))+3*m := by
  have hl := CountedPackedOriginalLine.cost_linear (shape kind q b hb hbq) n m (words kind hs)
    (CountedPackedShapeHeaders.words_values kind q b n hb hbq hs hv)
    (CountedPackedShapeHeaders.words_canonical kind hs hc)
  have hs := shape_stride_bound kind q b hb hbq
  have hm := Nat.mul_le_mul_left (n+1) hs
  have hbig : q+b+n+1 ≤ (n+1)*(q+b+1) := by nlinarith
  unfold cost
  nlinarith

/-- Full paid runtime bound includes shape preparation and inverse cleanup. -/
theorem runs (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hxs : zs.length*(shape kind q b hb hbq).sx ≤ xs.length)
    (hacc : acc.length = zs.length*(shape kind q b hb hbq).st)
    (hf : f (p0-1) = blank) (hg : g (p1-1) = blank) (hh : h (p3-1) = blank)
    (hh' : h (p3+acc.length) = blank) :
    HoareTime (program kind op R a)
      (fun v => v = input (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol)) (fun _ => blank) p0 p1 p2 p3 p4) hs)
      (fun v => v = input (PackedLine.bank (putWord f p0 (xs.map bitSymbol))
        (putWord g p1 (zs.map bitSymbol)) (fun _ => blank)
        (putWord h p3 (acc.map bitSymbol))
        (putWord (fun _ => blank) p4 ((ColumnTransducer.digits R 0
          (acc.zip (Gather.gather op (shape kind q b hb hbq) xs zs zs.length))).map bitSymbol))
        p0 p1 p2 p3 p4) hs)
      (530*((zs.length+1)*(q+b+1))+3*acc.length) :=
  (line_hoare kind op R q b hb hbq xs zs acc f g h p0 p1 p2 p3 p4 hs hv hc hxs hacc hf hg hh hh').consequence
    (fun _ h => h) (fun _ h => h) (cost_linear kind q b zs.length acc.length hb hbq hs hv hc)

end
end IntegerMultBounds.Machine.CountedPackedRuntimeLine
