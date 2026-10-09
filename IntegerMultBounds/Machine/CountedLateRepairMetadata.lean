import IntegerMultBounds.Machine.CountedRepairScanMetadataRun

/-! Runtime later sort width and zero rank counter. The original products
n*q and n*b are physically synthesized; the latter is replayed twice, with
all head returns and descriptor cleanup charged. -/
namespace IntegerMultBounds.Machine.CountedLateRepairMetadata
noncomputable section
open CountedRankSplitBank
open CountedRepairScanMetadata
open CountedRepairScanMetadataRun (filled filled_add)

def program := seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq
  (qProgram (a := 1)) bProgram) fillVq) fillVb) fillVb) fillCq) fillCb) fillCb)
  backV) backVb) backVb) backCtrQ) backCtrB) backCtrB) clearQ) clearB

def budget (n q b : ℕ) := 150*(n*q+n*b+n*b)+60*((qBits n q).length+(bBits n b).length)+600

theorem runs (f g h : ℤ → Fin 5) (p v w : ℤ) (hs : Fin 3 → List Bool)
    (q b n : ℕ) (hq : 0<q) (hb : 0<b)
    (hv : ∀ i, Counter.value (hs i)=values q b n i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun u => u=bank f g h p v w hs none none)
      (fun u => u=bank (filled f p (n*q+n*b+n*b) false)
        (filled g v (n*q+n*b+n*b) true) h p v w hs none none) (budget n q b) := by
  let qs := qBits n q
  let bs := bBits n b
  let G := filled g v (n*q) true
  let GG := filled g v (n*q+n*b) true
  let GGG := filled g v (n*q+n*b+n*b) true
  let F := filled f p (n*q) false
  let FF := filled f p (n*q+n*b) false
  let FFF := filled f p (n*q+n*b+n*b) false
  have hqv : Counter.value qs=n*q := DimensionProductDescriptor.bits_value n q
  have hbv : Counter.value bs=n*b := DimensionProductDescriptor.bits_value n b
  have h1 := constructQ f g h p v w hs n q hq (hv 0) (hv 2) (hc 0) (hc 2)
  have h2 := constructB f g h p v w hs n b qs hb (hv 1) (hv 2) (hc 1) (hc 2)
  have h3 := fillsVq f g h p v w hs qs bs (n*q) hqv
  have h4 := fillsVb f G h p (v+(n*q : ℕ)) w hs qs bs (n*b) hbv
  change HoareTime fillVb _ (fun u => u=bank f (filled G (v+(n*q : ℕ)) (n*b) true) h p
    (v+(n*q : ℕ)+(n*b : ℕ)) w hs (some qs) (some bs)) _ at h4
  rw [show filled G (v+(n*q : ℕ)) (n*b) true=GG from filled_add g v (n*q) (n*b) true] at h4
  have h4b := fillsVb f GG h p (v+((n*q+n*b : ℕ) : ℤ)) w hs qs bs (n*b) hbv
  change HoareTime fillVb _ (fun u => u=bank f (filled GG (v+((n*q+n*b : ℕ) : ℤ)) (n*b) true) h p
    (v+((n*q+n*b : ℕ) : ℤ)+(n*b : ℕ)) w hs (some qs) (some bs)) _ at h4b
  rw [show filled GG (v+((n*q+n*b : ℕ) : ℤ)) (n*b) true=GGG from filled_add g v (n*q+n*b) (n*b) true] at h4b
  have h5 := fillsCq f GGG h p (v+((n*q+n*b+n*b : ℕ) : ℤ)) w hs qs bs (n*q) hqv
  have h6 := fillsCb F GGG h (p+(n*q : ℕ)) (v+((n*q+n*b+n*b : ℕ) : ℤ)) w hs qs bs (n*b) hbv
  change HoareTime fillCb _ (fun u => u=bank (filled F (p+(n*q : ℕ)) (n*b) false) GGG h
    (p+(n*q : ℕ)+(n*b : ℕ)) (v+((n*q+n*b+n*b : ℕ) : ℤ)) w hs (some qs) (some bs)) _ at h6
  rw [show filled F (p+(n*q : ℕ)) (n*b) false=FF from filled_add f p (n*q) (n*b) false] at h6
  have h6b := fillsCb FF GGG h (p+((n*q+n*b : ℕ) : ℤ)) (v+((n*q+n*b+n*b : ℕ) : ℤ)) w hs qs bs (n*b) hbv
  change HoareTime fillCb _ (fun u => u=bank (filled FF (p+((n*q+n*b : ℕ) : ℤ)) (n*b) false) GGG h
    (p+((n*q+n*b : ℕ) : ℤ)+(n*b : ℕ)) (v+((n*q+n*b+n*b : ℕ) : ℤ)) w hs (some qs) (some bs)) _ at h6b
  rw [show filled FF (p+((n*q+n*b : ℕ) : ℤ)) (n*b) false=FFF from filled_add f p (n*q+n*b) (n*b) false] at h6b
  have h7 := movesV FFF GGG h (p+((n*q+n*b+n*b : ℕ) : ℤ)) (v+((n*q+n*b+n*b : ℕ) : ℤ)) w hs qs bs (n*q) hqv
  have eV : v+((n*q+n*b+n*b : ℕ) : ℤ)-(n*q : ℕ)=v+(n*b : ℕ)+(n*b : ℕ) := by push_cast; ring
  rw [eV] at h7
  have h8 := movesVb FFF GGG h (p+((n*q+n*b+n*b : ℕ) : ℤ)) (v+(n*b : ℕ)+(n*b : ℕ)) w hs qs bs (n*b) hbv
  simp only [add_sub_cancel_right] at h8
  have h8b := movesVb FFF GGG h (p+((n*q+n*b+n*b : ℕ) : ℤ)) (v+(n*b : ℕ)) w hs qs bs (n*b) hbv
  simp only [add_sub_cancel_right] at h8b
  have h9 := movesCtrQ FFF GGG h (p+((n*q+n*b+n*b : ℕ) : ℤ)) v w hs qs bs (n*q) hqv
  have eP : p+((n*q+n*b+n*b : ℕ) : ℤ)-(n*q : ℕ)=p+(n*b : ℕ)+(n*b : ℕ) := by push_cast; ring
  rw [eP] at h9
  have h10 := movesCtrB FFF GGG h (p+(n*b : ℕ)+(n*b : ℕ)) v w hs qs bs (n*b) hbv
  simp only [add_sub_cancel_right] at h10
  have h10b := movesCtrB FFF GGG h (p+(n*b : ℕ)) v w hs qs bs (n*b) hbv
  simp only [add_sub_cancel_right] at h10b
  have h11 := cleansQ FFF GGG h p v w hs qs bs
  have h12 := cleansB FFF GGG h p v w hs bs
  have ep1 : v+(n*q : ℕ)+(n*b : ℕ)=v+((n*q+n*b : ℕ) : ℤ) := by push_cast; ring
  have ep2 : p+(n*q : ℕ)+(n*b : ℕ)=p+((n*q+n*b : ℕ) : ℤ) := by push_cast; ring
  have ep3 : v+((n*q+n*b : ℕ) : ℤ)+(n*b : ℕ)=v+((n*q+n*b+n*b : ℕ) : ℤ) := by push_cast; ring
  have ep4 : p+((n*q+n*b : ℕ) : ℤ)+(n*b : ℕ)=p+((n*q+n*b+n*b : ℕ) : ℤ) := by push_cast; ring
  rw [ep1] at h4
  rw [ep2] at h6
  rw [ep3] at h4b
  rw [ep4] at h6b
  exact (((((((((((((((h1.seq h2).seq h3).seq h4).seq h4b).seq h5).seq h6).seq h6b).seq h7).seq h8).seq h8b).seq h9).seq h10).seq h10b).seq h11).seq h12).consequence
    (fun _ h => h) (fun _ h => h) (by unfold budget; dsimp [qs,bs]; omega)

theorem budget_linear (n q b : ℕ) : budget n q b ≤ 2000*((n+1)*(q+b+1)) := by
  have hq := GrowingCounterData.canonical_width (qBits n q) (DimensionProductDescriptor.bits_canonical n q)
  have hb := GrowingCounterData.canonical_width (bBits n b) (DimensionProductDescriptor.bits_canonical n b)
  simp only [qBits,bBits,DimensionProductDescriptor.bits_value] at hq hb
  have hqlog := Nat.log2_le_self (n*q)
  have hblog := Nat.log2_le_self (n*b)
  unfold budget qBits bBits
  nlinarith

end
end IntegerMultBounds.Machine.CountedLateRepairMetadata
