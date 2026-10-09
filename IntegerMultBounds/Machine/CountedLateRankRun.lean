import IntegerMultBounds.Machine.CountedLateRankBank

/-! Complete original-header V/W/U rank split with paid reads over the blank
tail, charged rewind of all four heads, and literal descriptor/work erasure. -/
namespace IntegerMultBounds.Machine.CountedLateRankRun
noncomputable section
variable {a : ℕ}
open CountedLateRankBank
open CountedRankSplitBank (qBits bBits values)

def program := seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq
  (extend (CountedRankSplitBank.qProgram (a := a)) 1)
  (extend CountedRankSplitBank.bProgram 1))
  (extend CountedRankSplitBank.copyV 1))
  (extend CountedRankSplitBank.copyW 1)) copyU)
  (extend CountedRankSplitBank.backCtrQ 1))
  (extend CountedRankSplitBank.backCtrB 1))
  (extend CountedRankSplitBank.backCtrB 1))
  (extend CountedRankSplitBank.backV 1))
  (extend CountedRankSplitBank.backW 1)) backU)
  (extend CountedRankSplitBank.clearQ 1)) (extend CountedRankSplitBank.clearB 1)
def budget (n q b : ℕ) := 74*(n*q)+95*(n*b)+
  23*(qBits n q).length+44*(bBits n b).length+328

theorem runs_raw (f v w u : ℤ → Fin (a+4)) (p pv pw pu : ℤ) (hs : Fin 3 → List Bool)
    (q b n : ℕ) (hq : 0 < q) (hb : 0 < b)
    (hv : ∀ i, Counter.value (hs i) = values q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun z => z = bank f v w u p pv pw pu hs none none)
      (fun z => z = bank f
        (putWord v pv (CopyCells.cells f p (n*q)))
        (putWord w pw (CopyCells.cells f (p+(n*q : ℕ)) (n*b)))
        (putWord u pu (CopyCells.cells f ((p+(n*q : ℕ))+(n*b : ℕ)) (n*b)))
        p pv pw pu hs none none) (budget n q b) := by
  let qs := qBits n q
  let bs := bBits n b
  let V := putWord v pv (CopyCells.cells f p (n*q))
  let W := putWord w pw (CopyCells.cells f (p+(n*q : ℕ)) (n*b))
  let U := putWord u pu (CopyCells.cells f ((p+(n*q : ℕ))+(n*b : ℕ)) (n*b))
  have hqv : Counter.value qs = n*q := DimensionProductDescriptor.bits_value n q
  have hbv : Counter.value bs = n*b := DimensionProductDescriptor.bits_value n b
  have h0 := hoare_extend_eq (CountedRankSplitBank.constructQ f v w p pv pw hs n q hq
    (hv 0) (hv 2) (hc 0) (hc 2)) (one u pu)
  have h1 := hoare_extend_eq (CountedRankSplitBank.constructB f v w p pv pw hs n b qs hb
    (hv 1) (hv 2) (hc 1) (hc 2)) (one u pu)
  have h2 := hoare_extend_eq (CountedRankSplitBank.copiesV f v w p pv pw hs qs bs (n*q) hqv) (one u pu)
  have h3 := hoare_extend_eq (CountedRankSplitBank.copiesW f V w (p+(n*q : ℕ))
    (pv+(n*q : ℕ)) pw hs qs bs (n*b) hbv) (one u pu)
  have h4 := copiesU f V W u ((p+(n*q : ℕ))+(n*b : ℕ))
    (pv+(n*q : ℕ)) (pw+(n*b : ℕ)) pu hs qs bs (n*b) hbv
  have h5 := hoare_extend_eq (CountedRankSplitBank.movesCtrQ f V W
    (((p+(n*q : ℕ))+(n*b : ℕ))+(n*b : ℕ)) (pv+(n*q : ℕ)) (pw+(n*b : ℕ)) hs qs bs (n*q) hqv)
    (one U (pu+(n*b : ℕ)))
  have hp5 : (((p+(n*q : ℕ))+(n*b : ℕ))+(n*b : ℕ))-(n*q : ℕ) =
      (p+(n*b : ℕ))+(n*b : ℕ) := by ring
  rw [hp5] at h5
  have h6 := hoare_extend_eq (CountedRankSplitBank.movesCtrB f V W
    ((p+(n*b : ℕ))+(n*b : ℕ)) (pv+(n*q : ℕ)) (pw+(n*b : ℕ)) hs qs bs (n*b) hbv)
    (one U (pu+(n*b : ℕ)))
  simp only [add_sub_cancel_right] at h6
  have h7 := hoare_extend_eq (CountedRankSplitBank.movesCtrB f V W
    (p+(n*b : ℕ)) (pv+(n*q : ℕ)) (pw+(n*b : ℕ)) hs qs bs (n*b) hbv)
    (one U (pu+(n*b : ℕ)))
  simp only [add_sub_cancel_right] at h7
  have h8 := hoare_extend_eq (CountedRankSplitBank.movesV f V W p
    (pv+(n*q : ℕ)) (pw+(n*b : ℕ)) hs qs bs (n*q) hqv) (one U (pu+(n*b : ℕ)))
  simp only [add_sub_cancel_right] at h8
  have h9 := hoare_extend_eq (CountedRankSplitBank.movesW f V W p pv (pw+(n*b : ℕ))
    hs qs bs (n*b) hbv) (one U (pu+(n*b : ℕ)))
  simp only [add_sub_cancel_right] at h9
  have h10 := movesU f V W U p pv pw (pu+(n*b : ℕ)) hs qs bs (n*b) hbv
  simp only [add_sub_cancel_right] at h10
  have h11 := hoare_extend_eq (CountedRankSplitBank.cleansQ f V W p pv pw hs qs bs) (one U pu)
  have h12 := hoare_extend_eq (CountedRankSplitBank.cleansB f V W p pv pw hs bs) (one U pu)
  apply ((((((((((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).consequence
    (fun _ h => h) (fun _ h => h)
  unfold budget
  dsimp [qs,bs]
  omega

theorem budget_linear (n q b : ℕ) : budget n q b ≤ 600*((n+1)*(q+b+1)) := by
  have hq := GrowingCounterData.canonical_width (qBits n q) (DimensionProductDescriptor.bits_canonical n q)
  have hb := GrowingCounterData.canonical_width (bBits n b) (DimensionProductDescriptor.bits_canonical n b)
  simp only [qBits,bBits,DimensionProductDescriptor.bits_value] at hq hb
  have hqlog := Nat.log2_le_self (n*q)
  have hblog := Nat.log2_le_self (n*b)
  unfold budget qBits bBits
  nlinarith

end
end IntegerMultBounds.Machine.CountedLateRankRun
