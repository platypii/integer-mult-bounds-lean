import IntegerMultBounds.Machine.BinaryCorrectionOffsetFinish

/-! Complete third-line correction offset table from original b/q/n and the
original control word, with explicit paid source scans, per-row borrow reset,
derived metadata construction, cleanup, and a uniform linear allowance bound. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffset
open BinaryAddressOffsetHeaders (widthBits rangeBits countBits)
open BinaryCorrectionOffsetFinish (widthWord)
noncomputable section

def input := BinaryCorrectionOffsetPrepare.input
def output := BinaryCorrectionOffsetFinish.output
def program : Program 31 1149 0 := seq BinaryCorrectionOffsetPrepare.program BinaryCorrectionOffsetFinish.program
def exactCost (q b n : ℕ) (Z : List Bool) := BinaryCorrectionOffsetPrepare.cost q b n Z+BinaryCorrectionOffsetFinish.cost q b n+1

theorem runs (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z q b n hb hbq) (exactCost q b n Z) := by
  have h0 := BinaryCorrectionOffsetPrepare.constructs hs Z q b n hb hbq hvq hvb hvn hc hZ
  have h1 := BinaryCorrectionOffsetFinish.finishes hs Z q b n hb hbq hvq hvn (hc 1) (hc 2) hZ
  have h := h0.seq h1
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold exactCost; omega)

def constant := BinarySelectedOffset.constant+1000
def allowance (q b n : ℕ) := (n+1)*(q+b+1)

private theorem length_le (xs : List Bool) (v : ℕ) (hv : Counter.value xs=v) (hc : GrowingCounterData.Canonical xs) :
    xs.length≤v+1 := by
  have hh := GrowingCounterData.canonical_width xs hc
  rw [hv] at hh
  exact hh.trans (Nat.add_le_add_right (Nat.log2_le_self v) 1)

theorem cost_bound (q b n : ℕ) (Z : List Bool) (hZ : Z.length=n) :
    exactCost q b n Z≤constant*(2^(n*b)*allowance q b n) := by
  let N := 2^(n*b)
  let m := n*N
  let D := N*((n+1)*(q+b+1))
  have hN : 0<N := by dsimp [N]; positivity
  have hA : 0<(n+1)*(q+b+1) := Nat.mul_pos (by omega) (by omega)
  have hD : 0<D := Nat.mul_pos hN hA
  have hND : N≤D := Nat.le_mul_of_pos_right _ hA
  have hmN : m+1≤(n+1)*N := by dsimp [m]; nlinarith
  have hg : (m+1)*(q+b+1)≤D := by
    have hh := Nat.mul_le_mul_right (q+b+1) hmN
    simpa only [D,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hh
  have hmD : m+1≤D := (Nat.le_mul_of_pos_right _ (by omega : 0<q+b+1)).trans hg
  have hqA : n*q+1≤(n+1)*(q+b+1) := by nlinarith
  have hbA : n*b+1≤(n+1)*(q+b+1) := by nlinarith
  have hqND := Nat.mul_le_mul_left N hqA
  have hbND := Nat.mul_le_mul_left N hbA
  have hqD : n*q+1≤D := (Nat.le_mul_of_pos_left _ hN).trans hqND
  have hbD : n*b+1≤D := (Nat.le_mul_of_pos_left _ hN).trans hbND
  have hselected := BinarySelectedOffset.cost_bound q b n Z hZ
  change BinarySelectedOffset.exactCost q b n Z≤BinarySelectedOffset.constant*D at hselected
  have hprep : BinaryCorrectionOffsetPrepare.cost q b n Z≤BinarySelectedOffset.exactCost q b n Z+350*D := by
    unfold BinaryCorrectionOffsetPrepare.cost BinarySelectedOffset.exactCost
    change BinarySelectedOffsetPrepare.cost b n Z+640*((m+1)*(q+b+1))+m*b+3*m+2*(m*q)+20≤
      BinarySelectedOffsetPrepare.cost b n Z+320*((m+1)*(q+b+1))+BinarySelectedOffsetCleanup.cost q b n+2+350*D
    nlinarith only [hD,hg]
  have hsub := BinaryCorrectionOffsetSubtract.cost_linear (n*q) N (widthWord q n) (rangeBits b n) hN
    (DimensionProductDescriptor.bits_value n q) (FixedBasePowerDescriptor.result_value 2 (n*b))
    (DimensionProductDescriptor.bits_canonical n q) (FixedBasePowerDescriptor.result_canonical 2 (n*b))
  have hsubD := hsub.trans (Nat.mul_le_mul_left 160 hqND)
  change BinaryCorrectionOffsetSubtract.cost (n*q) N (widthWord q n) (rangeBits b n)≤160*D at hsubD
  have hlw := length_le (widthBits b n) (n*b) (DimensionProductDescriptor.bits_value n b) (DimensionProductDescriptor.bits_canonical n b)
  have hlN := length_le (rangeBits b n) N (FixedBasePowerDescriptor.result_value 2 (n*b)) (FixedBasePowerDescriptor.result_canonical 2 (n*b))
  have hlm := length_le (countBits b n) m (DimensionProductDescriptor.bits_value n (2^(n*b))) (DimensionProductDescriptor.bits_canonical n (2^(n*b)))
  have hlq := length_le (widthWord q n) (n*q) (DimensionProductDescriptor.bits_value n q) (DimensionProductDescriptor.bits_canonical n q)
  have hh : BinaryDescriptorCleanupList.cost BinaryCorrectionOffsetFinish.headerSlots
      (BinaryCorrectionOffsetFinish.headerWords q b n)≤10*D+20 := by
    simp only [BinaryDescriptorCleanupList.cost,BinaryCorrectionOffsetFinish.headerSlots,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change 2*(widthBits b n).length+5+(2*(rangeBits b n).length+5+(2*(countBits b n).length+5+(2*(widthWord q n).length+5+0)))≤10*D+20
    omega
  have hfinish : BinaryCorrectionOffsetFinish.cost q b n≤300*D := by
    unfold BinaryCorrectionOffsetFinish.cost
    change 53*(n*q)+28+BinaryCorrectionOffsetSubtract.cost (n*q) N (widthWord q n) (rangeBits b n)+
      2*(m*b)+2*m+BinaryDescriptorCleanupList.cost BinaryCorrectionOffsetFinish.headerSlots
        (BinaryCorrectionOffsetFinish.headerWords q b n)+10≤300*D
    nlinarith only [hD,hqD,hg,hh,hsubD]
  change exactCost q b n Z≤constant*D
  unfold exactCost constant
  nlinarith only [hD,hselected,hprep,hfinish]

theorem constructs (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z q b n hb hbq)
      (constant*(2^(n*b)*allowance q b n)) :=
  (runs hs q b n Z hb hbq hvq hvb hvn hc hZ).consequence (fun _ h => h) (fun _ h => h) (cost_bound q b n Z hZ)

end
end IntegerMultBounds.Machine.BinaryCorrectionOffset
