import IntegerMultBounds.Machine.CountedRankSplitBank
import IntegerMultBounds.Machine.CountedRankSplitData

/-! Fixed rank splitting from only original q/b/n headers, with exact original
counter preservation through a possibly long blank tail and paid rewind. -/
namespace IntegerMultBounds.Machine.CountedRankSplitRun
noncomputable section
variable {a : ℕ}
open CountedRankSplitBank

def program := seq (seq (seq (seq (seq (seq (seq (seq (seq
  (qProgram (a := a)) bProgram) copyV) copyW) backCtrQ) backCtrB) backV) backW) clearQ) clearB

def budget (n q b : ℕ) :=
  74*(n*q+n*b)+23*((qBits n q).length+(bBits n b).length)+241

/-- The source and both destination heads return exactly to their supplied
positions. Counts, work clocks and product scratch are physically erased. -/
theorem runs_raw (f g h : ℤ → Fin (a+4)) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (q b n : ℕ) (hq : 0 < q) (hb : 0 < b)
    (hv : ∀ i, Counter.value (hs i) = values q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun u => u = bank f g h p v w hs none none)
      (fun u => u = bank f (putWord g v (CopyCells.cells f p (n*q)))
        (putWord h w (CopyCells.cells f (p+(n*q : ℕ)) (n*b))) p v w hs none none)
      (budget n q b) := by
  let qs := qBits n q
  let bs := bBits n b
  let V := putWord g v (CopyCells.cells f p (n*q))
  let W := putWord h w (CopyCells.cells f (p+(n*q : ℕ)) (n*b))
  have hqv : Counter.value qs = n*q := DimensionProductDescriptor.bits_value n q
  have hbv : Counter.value bs = n*b := DimensionProductDescriptor.bits_value n b
  have h0 := constructQ f g h p v w hs n q hq (hv 0) (hv 2) (hc 0) (hc 2)
  have h1 := constructB f g h p v w hs n b qs hb (hv 1) (hv 2) (hc 1) (hc 2)
  have h2 := copiesV f g h p v w hs qs bs (n*q) hqv
  have h3 := copiesW f V h (p+(n*q : ℕ)) (v+(n*q : ℕ)) w hs qs bs (n*b) hbv
  have h4 := movesCtrQ f V W ((p+(n*q : ℕ))+(n*b : ℕ)) (v+(n*q : ℕ)) (w+(n*b : ℕ)) hs qs bs (n*q) hqv
  have hp : ((p+(n*q : ℕ))+(n*b : ℕ))-(n*q : ℕ) = p+(n*b : ℕ) := by ring
  rw [hp] at h4
  have h5 := movesCtrB f V W (p+(n*b : ℕ)) (v+(n*q : ℕ)) (w+(n*b : ℕ)) hs qs bs (n*b) hbv
  simp only [add_sub_cancel_right] at h5
  have h6 := movesV f V W p (v+(n*q : ℕ)) (w+(n*b : ℕ)) hs qs bs (n*q) hqv
  simp only [add_sub_cancel_right] at h6
  have h7 := movesW f V W p v (w+(n*b : ℕ)) hs qs bs (n*b) hbv
  simp only [add_sub_cancel_right] at h7
  have h8 := cleansQ f V W p v w hs qs bs
  have h9 := cleansB f V W p v w hs bs
  apply (((((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).consequence
    (fun _ h => h) (fun _ h => h)
  unfold budget
  dsimp [qs,bs]
  omega

/-- The repair counter may be short. Blank tail cells yield zero bits while
the original stored counter and its entire tape are retained bit-for-bit. -/
theorem runs (f g h : ℤ → Fin (a+4)) (v w : ℤ) (cs : List Bool) (hs : Fin 3 → List Bool)
    (q b n : ℕ) (hq : 0 < q) (hb : 0 < b)
    (hv : ∀ i, Counter.value (hs i) = values q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ z : ℤ, 1+cs.length ≤ z → f z = blank) :
    HoareTime (program (a := a))
      (fun u => u = bank (putWord f 1 (cs.map bitSymbol)) g h 1 v w hs none none)
      (fun u => u = bank (putWord f 1 (cs.map bitSymbol))
        (putWord g v ((Gather.field cs 0 (n*q)).map bitSymbol))
        (putWord h w ((Gather.field cs (n*q) (n*b)).map bitSymbol)) 1 v w hs none none)
      (budget n q b) := by
  have h0 := runs_raw (putWord f 1 (cs.map bitSymbol)) g h 1 v w hs q b n hq hb hv hc
  have hV := CountedRankSplitData.cells_word f cs ht 0 (n*q)
  simp only [Nat.cast_zero,add_zero] at hV
  simpa only [hV,CountedRankSplitData.cells_word f cs ht (n*q) (n*b)] using h0

/-- Uniform runtime, including zero count and every generated descriptor. -/
theorem budget_linear (n q b : ℕ) : budget n q b ≤ 400*((n+1)*(q+b+1)) := by
  have hq := GrowingCounterData.canonical_width (qBits n q) (DimensionProductDescriptor.bits_canonical n q)
  have hb := GrowingCounterData.canonical_width (bBits n b) (DimensionProductDescriptor.bits_canonical n b)
  simp only [qBits,bBits,DimensionProductDescriptor.bits_value] at hq hb
  have hqlog := Nat.log2_le_self (n*q)
  have hblog := Nat.log2_le_self (n*b)
  unfold budget qBits bBits
  nlinarith

end
end IntegerMultBounds.Machine.CountedRankSplitRun
