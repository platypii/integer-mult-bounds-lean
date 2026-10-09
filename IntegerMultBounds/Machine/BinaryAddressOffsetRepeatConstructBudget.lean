import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstruct

/-! Pay for derived descriptors and all physical repetition work in the full
rotation volume. The base enumeration allowance is an explicit record-width
hypothesis, rather than an uncharged precomputed control table. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstructBudget
open BinaryAddressOffsetRepeatHeaders

private theorem length_le (xs : List Bool) (v : ℕ) (hv : Counter.value xs=v)
    (hc : GrowingCounterData.Canonical xs) : xs.length≤v+1 := by
  have hh := GrowingCounterData.canonical_width xs hc
  rw [hv] at hh
  exact hh.trans (Nat.add_le_add_right (Nat.log2_le_self v) 1)

theorem header_bound (q b n P H : ℕ) (hP : 0<P) (hH : 0<H) :
    BinaryAddressOffsetRepeatHeaders.cost q b n P H≤
      (2*FixedBasePowerDescriptor.constant 2+400)*(((P*H)*2^(n*b))*2^(n*q)) := by
  let T := 2^(n*b)
  let N := 2^(n*q)
  let K := (P*H)*T
  let D := K*N
  have hPH : 0<P*H := Nat.mul_pos hP hH
  have hT : 0<T := by dsimp [T]; positivity
  have hN : 0<N := by dsimp [N]; positivity
  have hK : 0<K := Nat.mul_pos hPH hT
  have hD : 0<D := Nat.mul_pos hK hN
  have hTD : T≤D := (Nat.le_mul_of_pos_left _ hPH).trans (Nat.le_mul_of_pos_right _ hN)
  have hND : N≤D := Nat.le_mul_of_pos_left _ hK
  have hKD : K≤D := Nat.le_mul_of_pos_right _ hN
  have hPHD : P*H≤D := (Nat.le_mul_of_pos_right _ hT).trans hKD
  have hw : n*b+1≤T := Nat.lt_two_pow_self
  have hq : n*q+1≤N := Nat.lt_two_pow_self
  have hs := length_le (sourceBits q n) (n*q) (DimensionProductDescriptor.bits_value n q) (DimensionProductDescriptor.bits_canonical n q)
  have ht := length_le (targetBits b n) T (FixedBasePowerDescriptor.result_value 2 (n*b)) (FixedBasePowerDescriptor.result_canonical 2 (n*b))
  have hp := length_le (prefixBits P H) (P*H) (DimensionProductDescriptor.bits_value P H) (DimensionProductDescriptor.bits_canonical P H)
  have hC := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hND
  have hC' := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hTD
  have hcleanup : BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n P H)≤12*D+15 := by
    simp only [BinaryDescriptorCleanupList.cost,cleanupSlots,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change 2*(sourceBits q n).length+5+(2*(targetBits b n).length+5+(2*(prefixBits P H).length+5+0))≤12*D+15
    omega
  change BinaryAddressOffsetRepeatHeaders.cost q b n P H≤(2*FixedBasePowerDescriptor.constant 2+400)*D
  unfold BinaryAddressOffsetRepeatHeaders.cost
  change (53*(n*b)+28)+(53*(n*q)+28)+FixedBasePowerDescriptor.constant 2*N+
    FixedBasePowerDescriptor.constant 2*T+(53*(P*H)+28)+(53*K+28)+
    BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n P H)+6≤_
  nlinarith

def constant := 2*FixedBasePowerDescriptor.constant 2+BinaryAddressOffset.constant+680

def volume (q b n P H L B : ℕ) := (P*2^(n*b))*(H*2^(n*q)*L)*2^(n*b)*B

theorem cost_volume (hs : Fin 6 → List Bool) (q b n P H L B : ℕ)
    (hP : 0<P) (hH : 0<H) (hL : 0<L) (hvL : Counter.value (hs 5)=L)
    (hcL : GrowingCounterData.Canonical (hs 5)) (hB : BinaryAddressOffset.allowance q b n≤B) :
    BinaryAddressOffsetRepeatConstruct.cost hs q b n P H L≤constant*volume q b n P H L B := by
  let W := n*b
  let T := 2^W
  let N := 2^(n*q)
  let K := (P*H)*T
  let D := K*N
  let V := D*L*T*B
  have hT : 0<T := by dsimp [T]; positivity
  have hN : 0<N := by dsimp [N]; positivity
  have hK : 0<K := Nat.mul_pos (Nat.mul_pos hP hH) hT
  have hD : 0<D := Nat.mul_pos hK hN
  have hA : 0<BinaryAddressOffset.allowance q b n := Nat.mul_pos (by omega) (by omega)
  have hBpos : 0<B := hA.trans_le hB
  have hDV : D≤V := (Nat.le_mul_of_pos_right _ hL).trans
    ((Nat.le_mul_of_pos_right _ hT).trans (Nat.le_mul_of_pos_right _ hBpos))
  have hV : 0<V := hD.trans_le hDV
  have hNV : N*B≤V := by
    have hND : N≤D := Nat.le_mul_of_pos_left _ hK
    have hDT : D≤D*L*T := (Nat.le_mul_of_pos_right _ hL).trans (Nat.le_mul_of_pos_right _ hT)
    exact Nat.mul_le_mul_right B (hND.trans hDT)
  have hAV : N*BinaryAddressOffset.allowance q b n≤V :=
    (Nat.mul_le_mul_left N hB).trans hNV
  have hmeta := (header_bound q b n P H hP hH).trans
    (Nat.mul_le_mul_left (2*FixedBasePowerDescriptor.constant 2+400) hDV)
  have hc : ∀ i, GrowingCounterData.Canonical (BinaryAddressOffsetRepeatConstruct.descriptors hs q b n P H i) := by
    intro i; fin_cases i
    · exact DimensionProductDescriptor.bits_canonical n b
    · exact hcL
    · exact FixedBasePowerDescriptor.result_canonical 2 (n*q)
    · exact DimensionProductDescriptor.bits_canonical (P*H) (2^(n*b))
  have hr := BinaryAddressOffsetRepeatBudget.cost_bound W L N K
    (BinaryAddressOffsetRepeatConstruct.descriptors hs q b n P H) hL hN hK
    (DimensionProductDescriptor.bits_value n b) hvL (FixedBasePowerDescriptor.result_value 2 (n*q))
    (DimensionProductDescriptor.bits_value (P*H) (2^(n*b))) hc
  have hw : W+1≤T := Nat.lt_two_pow_self
  have hrV : K*(N*(L*(W+1)))≤V := by
    have hh := Nat.mul_le_mul_left (D*L) hw
    have hv : D*L*T≤V := Nat.le_mul_of_pos_right _ hBpos
    apply le_trans _ hv
    convert hh using 1; dsimp [D]; ring
  have hr' := hr.trans (Nat.mul_le_mul_left 250 hrV)
  have hKD : K≤D := Nat.le_mul_of_pos_right _ hN
  have hND : N≤D := Nat.le_mul_of_pos_left _ hK
  have hTD : T≤D := (Nat.le_mul_of_pos_left _ (Nat.mul_pos hP hH)).trans hKD
  have hwD : W≤D := (Nat.le_of_lt (show W<T from Nat.lt_two_pow_self)).trans hTD
  have hlw := length_le (widthBits b n) W (DimensionProductDescriptor.bits_value n b) (DimensionProductDescriptor.bits_canonical n b)
  have hlN := length_le (rangeBits q n) N (FixedBasePowerDescriptor.result_value 2 (n*q)) (FixedBasePowerDescriptor.result_canonical 2 (n*q))
  have hlK := length_le (repeatBits b n P H) K (DimensionProductDescriptor.bits_value (P*H) (2^(n*b))) (DimensionProductDescriptor.bits_canonical (P*H) (2^(n*b)))
  have hcleanup : BinaryDescriptorCleanupList.cost BinaryAddressOffsetRepeatConstruct.cleanupSlots
      (BinaryAddressOffsetRepeatConstruct.cleanupBits q b n P H)≤27*V := by
    simp only [BinaryDescriptorCleanupList.cost,BinaryAddressOffsetRepeatConstruct.cleanupSlots,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change 2*(widthBits b n).length+5+(2*(rangeBits q n).length+5+(2*(repeatBits b n P H).length+5+0))≤27*V
    omega
  have hbase := Nat.mul_le_mul_left BinaryAddressOffset.constant hAV
  have hv : volume q b n P H L B=V := by dsimp [volume,V,D,K,N,T,W]; ring
  rw [hv]
  unfold BinaryAddressOffsetRepeatConstruct.cost constant
  change BinaryAddressOffsetRepeatHeaders.cost q b n P H+BinaryAddressOffset.constant*(N*BinaryAddressOffset.allowance q b n)+
    BinaryAddressOffsetRepeat.cost W L N K (BinaryAddressOffsetRepeatConstruct.descriptors hs q b n P H)+
    BinaryDescriptorCleanupList.cost BinaryAddressOffsetRepeatConstruct.cleanupSlots (BinaryAddressOffsetRepeatConstruct.cleanupBits q b n P H)+3≤_
  nlinarith

end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstructBudget
