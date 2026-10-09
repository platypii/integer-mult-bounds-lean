import IntegerMultBounds.Machine.BinaryParityXorOffsetFinish

/-! Complete fourth-line negative parity-XOR table from original q/b/n and the
original control word, with explicit paid source scans, per-row negation reset,
derived metadata construction, cleanup, and a uniform linear allowance bound. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffset
open BinaryAddressOffsetHeaders (widthBits rangeBits countBits)
open BinaryParityXorOffsetFinish (widthWord)
noncomputable section

def input := BinaryParityXorOffsetPrepare.input
def output := BinaryParityXorOffsetFinish.output
def program := seq BinaryParityXorOffsetPrepare.program BinaryParityXorOffsetFinish.program
def exactCost (q b n : ℕ) (Z : List Bool) := BinaryParityXorOffsetPrepare.cost q b n Z+BinaryParityXorOffsetFinish.cost q b n+1

theorem runs (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z q b n hb hbq) (exactCost q b n Z) := by
  have h0 := BinaryParityXorOffsetPrepare.constructs hs Z q b n hb hbq hvq hvb hvn hc hZ
  have h1 := BinaryParityXorOffsetFinish.finishes hs Z q b n hb hbq hvb hvn (hc 1) (hc 2) hZ
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
    exactCost q b n Z≤constant*(2^(n*q)*allowance q b n) := by
  let N := 2^(n*q)
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
  have hselected := BinarySelectedOffset.cost_bound b q n Z hZ
  simp only [BinarySelectedOffset.allowance,Nat.add_comm b q] at hselected
  change BinarySelectedOffset.exactCost b q n Z≤BinarySelectedOffset.constant*D at hselected
  have hprep : BinaryParityXorOffsetPrepare.cost q b n Z≤BinarySelectedOffset.exactCost b q n Z+350*D := by
    unfold BinaryParityXorOffsetPrepare.cost BinarySelectedOffset.exactCost
    rw [Nat.add_comm b q]
    change BinarySelectedOffsetPrepare.cost q n Z+320*((m+1)*(q+b+1))+m*b+m+m*q+10≤
      BinarySelectedOffsetPrepare.cost q n Z+320*((m+1)*(q+b+1))+BinarySelectedOffsetCleanup.cost b q n+2+350*D
    nlinarith only [hg,hD]
  have hsub := BinaryParityXorOffsetNegate.cost_linear (n*b) N (widthWord b n) (rangeBits q n) hN
    (DimensionProductDescriptor.bits_value n b) (FixedBasePowerDescriptor.result_value 2 (n*q))
    (DimensionProductDescriptor.bits_canonical n b) (FixedBasePowerDescriptor.result_canonical 2 (n*q))
  have hsubD := hsub.trans (Nat.mul_le_mul_left 120 hbND)
  change BinaryParityXorOffsetNegate.cost (n*b) N (widthWord b n) (rangeBits q n)≤120*D at hsubD
  have hlw := length_le (widthBits q n) (n*q) (DimensionProductDescriptor.bits_value n q) (DimensionProductDescriptor.bits_canonical n q)
  have hlN := length_le (rangeBits q n) N (FixedBasePowerDescriptor.result_value 2 (n*q)) (FixedBasePowerDescriptor.result_canonical 2 (n*q))
  have hlm := length_le (countBits q n) m (DimensionProductDescriptor.bits_value n (2^(n*q))) (DimensionProductDescriptor.bits_canonical n (2^(n*q)))
  have hlq := length_le (widthWord b n) (n*b) (DimensionProductDescriptor.bits_value n b) (DimensionProductDescriptor.bits_canonical n b)
  have hh : BinaryDescriptorCleanupList.cost BinaryParityXorOffsetFinish.headerSlots
      (BinaryParityXorOffsetFinish.headerWords q b n)≤10*D+20 := by
    simp only [BinaryDescriptorCleanupList.cost,BinaryParityXorOffsetFinish.headerSlots,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change 2*(widthBits q n).length+5+(2*(rangeBits q n).length+5+(2*(countBits q n).length+5+(2*(widthWord b n).length+5+0)))≤10*D+20
    omega
  have hfinish : BinaryParityXorOffsetFinish.cost q b n≤300*D := by
    unfold BinaryParityXorOffsetFinish.cost
    change 53*(n*b)+28+BinaryParityXorOffsetNegate.cost (n*b) N (widthWord b n) (rangeBits q n)+
      2*(m*q)+2*m+BinaryDescriptorCleanupList.cost BinaryParityXorOffsetFinish.headerSlots
        (BinaryParityXorOffsetFinish.headerWords q b n)+10≤300*D
    nlinarith only [hD,hbD,hg,hh,hsubD]
  change exactCost q b n Z≤constant*D
  unfold exactCost constant
  nlinarith only [hD,hselected,hprep,hfinish]

theorem constructs (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z q b n hb hbq)
      (constant*(2^(n*q)*allowance q b n)) :=
  (runs hs q b n Z hb hbq hvq hvb hvn hc hZ).consequence (fun _ h => h) (fun _ h => h) (cost_bound q b n Z hZ)

end
end IntegerMultBounds.Machine.BinaryParityXorOffset
