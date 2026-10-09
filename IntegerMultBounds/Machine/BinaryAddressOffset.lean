import IntegerMultBounds.Machine.BinaryAddressOffsetCleanup

/-! Complete physical parity-offset production from only original q/b/n.
The address table, repeated dummy control, all derived dimensions and every
private marker are constructed and erased. Only the actual packed offset
word remains, with an explicit record-width condition for linear volume cost. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffset
open BinaryAddressOffsetHeaders (widthBits rangeBits countBits)
noncomputable section

def input (hs : Fin 3 → List Bool) :=
  (BinaryAddressOffsetHeaders.bank hs).append (FixedHeaderBankCopy.empty 14)
def output (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  (BinaryAddressOffsetCleanup.output hs q b n hb hbq).append (FixedHeaderBankCopy.empty 14)

def prepare := extend BinaryAddressOffsetPrepare.program 14
def cleanup := extend BinaryAddressOffsetCleanup.program 14
def program := seq (seq prepare BinaryAddressOffsetGather.program) cleanup

def exactCost (q b n : ℕ) := BinaryAddressOffsetPrepare.cost q n+
  320*((n*2^(n*q)+1)*(q+b+1))+BinaryAddressOffsetCleanup.cost q b n+2

theorem runs (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun z => z=input hs) (fun z => z=output hs q b n hb hbq) (exactCost q b n) := by
  have h0 := hoare_extend_eq (BinaryAddressOffsetPrepare.constructs hs q n (by omega)
    hvq hvn (hc 0) (hc 2)) (FixedHeaderBankCopy.empty 14)
  have h1 := BinaryAddressOffsetGather.runs hs q b n hb hbq hvq hvb hc
  rw [BinaryAddressOffsetGather.input_eq,BinaryAddressOffsetGather.input_eq] at h1
  have h2 := hoare_extend_eq (BinaryAddressOffsetCleanup.cleans hs q b n hb hbq) (FixedHeaderBankCopy.empty 14)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold exactCost; omega)

def constant := FixedBasePowerDescriptor.constant 2+BinaryAddressTable.constant+600
/-- Per-address work needed by the source enumeration and packed gather. -/
def allowance (q b n : ℕ) := (n+1)*(q+b+1)

theorem cost_bound (q b n : ℕ) : exactCost q b n ≤ constant*(2^(n*q)*allowance q b n) := by
  let N := 2^(n*q)
  let m := n*N
  let w := n*q
  let D := N*((n+1)*(q+b+1))
  have hN : 1 ≤ N := Nat.one_le_pow _ _ (by decide)
  have hA : 1 ≤ (n+1)*(q+b+1) := Nat.mul_pos (by omega) (by omega)
  have hnD : N ≤ D := Nat.le_mul_of_pos_right _ hA
  have hwA : w+1 ≤ (n+1)*(q+b+1) := by dsimp [w]; nlinarith
  have hwN : (w+1)*N ≤ D := by
    simpa only [D,Nat.mul_comm] using Nat.mul_le_mul_right N hwA
  have hwD : w+1 ≤ D := (Nat.le_mul_of_pos_right _ hN).trans hwN
  have hmN : m+1 ≤ (n+1)*N := by dsimp [m]; nlinarith
  have hg : (m+1)*(q+b+1) ≤ D := by
    have h := Nat.mul_le_mul_right (q+b+1) hmN
    simpa only [D,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
  have hmD : m+1 ≤ D := (Nat.le_mul_of_pos_right _ (by omega : 0<q+b+1)).trans hg
  have hlw := GrowingCounterData.canonical_width (widthBits q n) (DimensionProductDescriptor.bits_canonical n q)
  rw [show Counter.value (widthBits q n)=w from DimensionProductDescriptor.bits_value n q] at hlw
  have hlN := GrowingCounterData.canonical_width (rangeBits q n) (FixedBasePowerDescriptor.result_canonical 2 (n*q))
  rw [show Counter.value (rangeBits q n)=N from FixedBasePowerDescriptor.result_value 2 (n*q)] at hlN
  have hlm := GrowingCounterData.canonical_width (countBits q n) (DimensionProductDescriptor.bits_canonical n (2^(n*q)))
  rw [show Counter.value (countBits q n)=m from DimensionProductDescriptor.bits_value n (2^(n*q))] at hlm
  have hlw' : (widthBits q n).length ≤ D := by have := Nat.log2_le_self w; omega
  have hlN' : (rangeBits q n).length ≤ 2*D := by have := Nat.log2_le_self N; omega
  have hlm' : (countBits q n).length ≤ D := by have := Nat.log2_le_self m; omega
  have hC := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hnD
  have hT := Nat.mul_le_mul_left BinaryAddressTable.constant hwN
  change exactCost q b n ≤ constant*D
  unfold exactCost BinaryAddressOffsetPrepare.cost BinaryAddressOffsetHeaders.cost BinaryAddressOffsetCleanup.cost constant
  have hfinal : FixedBasePowerDescriptor.constant 2*N+BinaryAddressTable.constant*((w+1)*N)+
      53*w+61*m+7*(countBits q n).length+320*((m+1)*(q+b+1))+
      m*q+m+m*b+2*((widthBits q n).length+(rangeBits q n).length+(countBits q n).length)+124 ≤
      (FixedBasePowerDescriptor.constant 2+BinaryAddressTable.constant+600)*D := by
    nlinarith
  convert hfinal using 1; dsimp [N,m,w,D]; ring

/-- A sole-input constructor. Tape8 contains all packed parity offsets in
increasing source-address order, at headzero; tapes0/1/2 retain originalq/b/n,
and the other26 tapes are wholly blank at headzero. -/
theorem constructs (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun z => z=input hs) (fun z => z=output hs q b n hb hbq)
      (constant*(2^(n*q)*allowance q b n)) :=
  (runs hs q b n hb hbq hvq hvb hvn hc).consequence (fun _ h => h) (fun _ h => h) (cost_bound q b n)

theorem cost_volume (q b n R : ℕ) (hR : allowance q b n ≤ R) :
    constant*(2^(n*q)*allowance q b n) ≤ constant*(2^(n*q)*R) :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hR)

end
end IntegerMultBounds.Machine.BinaryAddressOffset
