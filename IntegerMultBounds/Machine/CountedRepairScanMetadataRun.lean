import IntegerMultBounds.Machine.CountedRepairScanMetadata

/-! Exact execution and uniform bounds for repair width/counter construction. -/
namespace IntegerMultBounds.Machine.CountedRepairScanMetadataRun
noncomputable section
open CountedRankSplitBank
open CountedRepairScanMetadata

def filled (f : ℤ → Fin 5) (p : ℤ) (n : ℕ) (b : Bool) := putWord f p (List.replicate n (bitSymbol b))

theorem filled_add (f : ℤ → Fin 5) (p : ℤ) (m n : ℕ) (b : Bool) :
    filled (filled f p m b) (p+m) n b = filled f p (m+n) b := by
  have h := putWord_append_forward f p (List.replicate m (bitSymbol (a := 1) b)) (List.replicate n (bitSymbol b))
  simpa only [filled,List.length_replicate,← List.replicate_add] using h

def budget (n q b : ℕ) := 100*(n*q+(n*b : ℕ))+40*((qBits n q).length+(bBits n b).length)+400

theorem runs (f g h : ℤ → Fin 5) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (q b n : ℕ) (hq : 0<q) (hb : 0<b)
    (hv : ∀ i, Counter.value (hs i)=values q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime CountedRepairScanMetadata.program (fun u => u=bank f g h p v w hs none none)
      (fun u => u=bank (filled f p (n*q+(n*b : ℕ)) false) (filled g v (n*q+(n*b : ℕ)) true) h p v w hs none none)
      (budget n q b) := by
  let qs := qBits n q
  let bs := bBits n b
  let G := filled g v (n*q) true
  let GG := filled g v (n*q+(n*b : ℕ)) true
  let F := filled f p (n*q) false
  let FF := filled f p (n*q+(n*b : ℕ)) false
  have hqv : Counter.value qs=n*q := DimensionProductDescriptor.bits_value n q
  have hbv : Counter.value bs=n*b := DimensionProductDescriptor.bits_value n b
  have h1 := constructQ f g h p v w hs n q hq (hv 0) (hv 2) (hc 0) (hc 2)
  have h2 := constructB f g h p v w hs n b qs hb (hv 1) (hv 2) (hc 1) (hc 2)
  have h3 := fillsVq f g h p v w hs qs bs (n*q) hqv
  have h4 := fillsVb f G h p (v+(n*q : ℕ)) w hs qs bs (n*b) hbv
  change HoareTime fillVb _ (fun u => u=bank f (filled G (v+(n*q : ℕ)) (n*b) true) h p (v+(n*q : ℕ)+(n*b : ℕ)) w hs (some qs) (some bs)) _ at h4
  rw [show filled G (v+(n*q : ℕ)) (n*b) true=GG from filled_add g v (n*q) (n*b) true] at h4
  have h5 := fillsCq f GG h p (v+(n*q : ℕ)+(n*b : ℕ)) w hs qs bs (n*q) hqv
  have h6 := fillsCb F GG h (p+(n*q : ℕ)) (v+(n*q : ℕ)+(n*b : ℕ)) w hs qs bs (n*b) hbv
  change HoareTime fillCb _ (fun u => u=bank (filled F (p+(n*q : ℕ)) (n*b) false) GG h (p+(n*q : ℕ)+(n*b : ℕ)) (v+(n*q : ℕ)+(n*b : ℕ)) w hs (some qs) (some bs)) _ at h6
  rw [show filled F (p+(n*q : ℕ)) (n*b) false=FF from filled_add f p (n*q) (n*b) false] at h6
  have h7 := movesV FF GG h (p+(n*q : ℕ)+(n*b : ℕ)) (v+(n*q : ℕ)+(n*b : ℕ)) w hs qs bs (n*q) hqv
  have eV : v+(n*q : ℕ)+(n*b : ℕ)-(n*q : ℕ)=v+(n*b : ℕ) := by push_cast; ring
  rw [eV] at h7
  have h8 := movesVb FF GG h (p+(n*q : ℕ)+(n*b : ℕ)) (v+(n*b : ℕ)) w hs qs bs (n*b) hbv
  simp only [add_sub_cancel_right] at h8
  have h9 := movesCtrQ FF GG h (p+(n*q : ℕ)+(n*b : ℕ)) v w hs qs bs (n*q) hqv
  have eP : p+(n*q : ℕ)+(n*b : ℕ)-(n*q : ℕ)=p+(n*b : ℕ) := by push_cast; ring
  rw [eP] at h9
  have h10 := movesCtrB FF GG h (p+(n*b : ℕ)) v w hs qs bs (n*b) hbv
  simp only [add_sub_cancel_right] at h10
  have h11 := cleansQ FF GG h p v w hs qs bs
  have h12 := cleansB FF GG h p v w hs bs
  exact (((((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12).consequence
    (fun _ h => h) (fun _ h => h) (by unfold budget; dsimp [qs,bs]; omega)

theorem budget_linear (n q b : ℕ) : budget n q b ≤ 1000*((n+1)*(q+b+1)) := by
  have hq := GrowingCounterData.canonical_width (qBits n q) (DimensionProductDescriptor.bits_canonical n q)
  have hb := GrowingCounterData.canonical_width (bBits n b) (DimensionProductDescriptor.bits_canonical n b)
  simp only [qBits,bBits,DimensionProductDescriptor.bits_value] at hq hb
  have hqlog := Nat.log2_le_self (n*q)
  have hblog := Nat.log2_le_self (n*b)
  unfold budget qBits bBits
  nlinarith

end
end IntegerMultBounds.Machine.CountedRepairScanMetadataRun
