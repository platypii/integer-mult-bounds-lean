import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixParity
import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixNegative

/-! Both current-source-prefix constructors include physical metadata, source
production, repeated copying and full cleanup within the rotation volume. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyPrefixBudget
open BinaryAddressOffsetHeaders (widthBits rangeBits countBits)
open BinaryPackedEarlyPrefixNegative (descriptors cleanupSlots cleanupBits)

def allowance (q b n : ℕ) := (n+1)*(q+b+1)
def volume (q b n L K B : ℕ) := K*2^(n*q)*L*2^(n*b)*B
def constant (C : ℕ) := FixedBasePowerDescriptor.constant 2+C+600

def cost (C : ℕ) (hs : Fin 5 → List Bool) (q b n L K : ℕ) :=
  BinaryPackedEarlyPrefixHeaders.cost q b n+C*(2^(n*q)*allowance q b n)+
  BinaryAddressOffsetRepeat.cost (n*b) L (2^(n*q)) K (descriptors hs q b n)+
  BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n)+3

private theorem length_le (xs : List Bool) (v : ℕ) (hv : Counter.value xs=v)
    (hc : GrowingCounterData.Canonical xs) : xs.length≤v+1 := by
  have h := GrowingCounterData.canonical_width xs hc
  rw [hv] at h
  exact h.trans (Nat.add_le_add_right (Nat.log2_le_self v) 1)

theorem cost_volume (C : ℕ) (hs : Fin 5 → List Bool) (q b n L K B : ℕ)
    (hL : 0<L) (hK : 0<K) (hvL : Counter.value (hs 3)=L) (hvK : Counter.value (hs 4)=K)
    (hcL : GrowingCounterData.Canonical (hs 3)) (hcK : GrowingCounterData.Canonical (hs 4))
    (hB : allowance q b n≤B) :
    cost C hs q b n L K≤constant C*volume q b n L K B := by
  let N := 2^(n*q)
  let T := 2^(n*b)
  let A := allowance q b n
  let D := N*A
  let V := volume q b n L K B
  have hN : 0<N := by dsimp [N]; positivity
  have hT : 0<T := by dsimp [T]; positivity
  have hA : 0<A := Nat.mul_pos (by omega) (by omega)
  have hBpos : 0<B := hA.trans_le hB
  have hD : 0<D := Nat.mul_pos hN hA
  have hND : N≤D := Nat.le_mul_of_pos_right _ hA
  have hqa : n*q+1≤A := by dsimp [A,allowance]; nlinarith
  have hba : n*b+1≤A := by dsimp [A,allowance]; nlinarith
  have hna : n+1≤A := by dsimp [A,allowance]; nlinarith
  have hqD : n*q+1≤D := hqa.trans (Nat.le_mul_of_pos_left _ hN)
  have hbD : n*b+1≤D := hba.trans (Nat.le_mul_of_pos_left _ hN)
  have hnD : n*N+1≤D := by
    have h := Nat.mul_le_mul_left N hna
    dsimp [D]; nlinarith
  have hDV : D≤V := by
    have h0 := Nat.mul_le_mul_left N hB
    have h1 : N*B≤K*N*L*T*B := by
      have hh : N≤K*N*L*T := (Nat.le_mul_of_pos_left _ hK).trans
        ((Nat.le_mul_of_pos_right _ hL).trans (Nat.le_mul_of_pos_right _ hT))
      exact Nat.mul_le_mul_right B hh
    exact h0.trans h1
  have hV : 0<V := hD.trans_le hDV
  have hmeta : BinaryPackedEarlyPrefixHeaders.cost q b n≤(FixedBasePowerDescriptor.constant 2+250)*D := by
    have hh := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hND
    unfold BinaryPackedEarlyPrefixHeaders.cost BinaryAddressOffsetHeaders.cost
    change 53*(n*q)+FixedBasePowerDescriptor.constant 2*N+53*(n*N)+58+53*(n*b)+29≤_
    nlinarith only [hh,hqD,hbD,hnD,hD]
  have hlq := length_le (widthBits q n) (n*q) (DimensionProductDescriptor.bits_value n q) (DimensionProductDescriptor.bits_canonical n q)
  have hlb := length_le (widthBits b n) (n*b) (DimensionProductDescriptor.bits_value n b) (DimensionProductDescriptor.bits_canonical n b)
  have hlN := length_le (rangeBits q n) N (FixedBasePowerDescriptor.result_value 2 (n*q)) (FixedBasePowerDescriptor.result_canonical 2 (n*q))
  have hlc := length_le (countBits q n) (n*N) (DimensionProductDescriptor.bits_value n N) (DimensionProductDescriptor.bits_canonical n N)
  have hclean : BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n)≤40*D := by
    simp only [BinaryDescriptorCleanupList.cost,cleanupSlots,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change 2*(widthBits q n).length+5+(2*(rangeBits q n).length+5+(2*(countBits q n).length+5+(2*(widthBits b n).length+5+0)))≤40*D
    omega
  have hcan : ∀ i, GrowingCounterData.Canonical (descriptors hs q b n i) := by
    intro i; fin_cases i
    · exact DimensionProductDescriptor.bits_canonical n b
    · exact hcL
    · exact FixedBasePowerDescriptor.result_canonical 2 (n*q)
    · exact hcK
  have hr := BinaryAddressOffsetRepeatBudget.cost_bound (n*b) L N K (descriptors hs q b n) hL hN hK
    (DimensionProductDescriptor.bits_value n b) hvL (FixedBasePowerDescriptor.result_value 2 (n*q)) hvK hcan
  have hrV : K*(N*(L*(n*b+1)))≤V := by
    have hwidth : n*b+1≤T := Nat.lt_two_pow_self
    have h0 := Nat.mul_le_mul_left (K*N*L) hwidth
    have h1 : K*N*L*T≤V := Nat.le_mul_of_pos_right _ hBpos
    apply le_trans _ h1
    convert h0 using 1; ring
  have hrep := hr.trans (Nat.mul_le_mul_left 250 hrV)
  have hmetaV := hmeta.trans (Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2+250) hDV)
  have hcleanV := hclean.trans (Nat.mul_le_mul_left 40 hDV)
  have hbase := Nat.mul_le_mul_left C hDV
  change cost C hs q b n L K≤constant C*V
  unfold cost constant
  change BinaryPackedEarlyPrefixHeaders.cost q b n+C*D+
    BinaryAddressOffsetRepeat.cost (n*b) L N K (descriptors hs q b n)+
    BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n)+3≤_
  nlinarith only [hmetaV,hcleanV,hbase,hrep,hV]

theorem negative_cost (hs : Fin 5 → List Bool) (q b n L K B : ℕ)
    (hL : 0<L) (hK : 0<K) (hvL : Counter.value (hs 3)=L) (hvK : Counter.value (hs 4)=K)
    (hcL : GrowingCounterData.Canonical (hs 3)) (hcK : GrowingCounterData.Canonical (hs 4))
    (hB : allowance q b n≤B) :
    BinaryPackedEarlyPrefixNegative.cost hs q b n L K≤constant BinaryParityXorOffset.constant*volume q b n L K B :=
  cost_volume _ hs q b n L K B hL hK hvL hvK hcL hcK hB

theorem parity_cost (hs : Fin 5 → List Bool) (q b n L K B : ℕ)
    (hL : 0<L) (hK : 0<K) (hvL : Counter.value (hs 3)=L) (hvK : Counter.value (hs 4)=K)
    (hcL : GrowingCounterData.Canonical (hs 3)) (hcK : GrowingCounterData.Canonical (hs 4))
    (hB : allowance q b n≤B) :
    BinaryPackedEarlyPrefixParity.cost hs q b n L K≤constant BinaryAddressOffset.constant*volume q b n L K B :=
  cost_volume _ hs q b n L K B hL hK hvL hvK hcL hcK hB

end IntegerMultBounds.Machine.BinaryPackedEarlyPrefixBudget
