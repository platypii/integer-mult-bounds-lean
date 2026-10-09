import IntegerMultBounds.Machine.BinarySelectedOffsetCleanup

/-! Complete physical selected mask-shift offset production from original b/q/n and its control word.
The address table, repeated original control, all derived dimensions and every
private marker are constructed and erased. The original control and actual packed offset
word remain, with an explicit record-width condition for linear volume cost. -/
namespace IntegerMultBounds.Machine.BinarySelectedOffset
open BinaryAddressOffsetHeaders (widthBits rangeBits countBits)
noncomputable section

def input (hs : Fin 3 → List Bool) (Z : List Bool) :=
  (BinarySelectedOffsetPrepare.input hs Z).append (FixedHeaderBankCopy.empty 14)
def output (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q) :=
  (BinarySelectedOffsetCleanup.output hs q b n Z hb hbq).append (FixedHeaderBankCopy.empty 14)

def prepare := extend BinarySelectedOffsetPrepare.program 14
def cleanup := extend BinarySelectedOffsetCleanup.program 14
def program := seq (seq prepare BinarySelectedOffsetGather.program) cleanup

def exactCost (q b n : ℕ) (Z : List Bool) := BinarySelectedOffsetPrepare.cost b n Z+
  320*((n*2^(n*b)+1)*(q+b+1))+BinarySelectedOffsetCleanup.cost q b n+2

theorem runs (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs q b n Z hb hbq) (exactCost q b n Z) := by
  have h0 := hoare_extend_eq (BinarySelectedOffsetPrepare.runs hs Z b n (by omega)
    hvb hvn (hc 0) (hc 2)) (FixedHeaderBankCopy.empty 14)
  have h1 := BinarySelectedOffsetGather.runs hs q b n Z hb hbq hvq hvb hc hZ
  rw [BinarySelectedOffsetGather.input_eq,BinarySelectedOffsetGather.input_eq] at h1
  have h2 := hoare_extend_eq (BinarySelectedOffsetCleanup.cleans hs q b n Z hb hbq hZ) (FixedHeaderBankCopy.empty 14)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by unfold exactCost; omega)

def constant := FixedBasePowerDescriptor.constant 2+BinaryAddressTable.constant+650
/-- Per-address work needed by the source enumeration and packed gather. -/
def allowance (q b n : ℕ) := (n+1)*(q+b+1)

theorem cost_bound (q b n : ℕ) (Z : List Bool) (hZ : Z.length=n) : exactCost q b n Z ≤ constant*(2^(n*b)*allowance q b n) := by
  let N := 2^(n*b)
  let m := n*N
  let w := n*b
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
  have hlw := GrowingCounterData.canonical_width (widthBits b n) (DimensionProductDescriptor.bits_canonical n b)
  rw [show Counter.value (widthBits b n)=w from DimensionProductDescriptor.bits_value n b] at hlw
  have hlN := GrowingCounterData.canonical_width (rangeBits b n) (FixedBasePowerDescriptor.result_canonical 2 (n*b))
  rw [show Counter.value (rangeBits b n)=N from FixedBasePowerDescriptor.result_value 2 (n*b)] at hlN
  have hlm := GrowingCounterData.canonical_width (countBits b n) (DimensionProductDescriptor.bits_canonical n (2^(n*b)))
  rw [show Counter.value (countBits b n)=m from DimensionProductDescriptor.bits_value n (2^(n*b))] at hlm
  have hlw' : (widthBits b n).length ≤ D := by have := Nat.log2_le_self w; omega
  have hlN' : (rangeBits b n).length ≤ 2*D := by have := Nat.log2_le_self N; omega
  have hlm' : (countBits b n).length ≤ D := by have := Nat.log2_le_self m; omega
  have hC := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hnD
  have hT := Nat.mul_le_mul_left BinaryAddressTable.constant hwN
  change exactCost q b n Z ≤ constant*D
  have hc : N*(3*n+9) ≤ 12*D := by
    have hdim : 3*n+9 ≤ 12*((n+1)*(q+b+1)) := by nlinarith
    have hh := Nat.mul_le_mul_left N hdim
    simpa only [D,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
  unfold exactCost BinarySelectedOffsetPrepare.cost BinaryAddressOffsetHeaders.cost BinarySelectedOffsetCleanup.cost constant
  rw [hZ]
  have hfinal : FixedBasePowerDescriptor.constant 2*N+BinaryAddressTable.constant*((w+1)*N)+
      53*w+53*m+N*(3*n+9)+7*(rangeBits b n).length+320*((m+1)*(q+b+1))+
      m*q+m+m*b+2*((widthBits b n).length+(rangeBits b n).length+(countBits b n).length)+116 ≤
      (FixedBasePowerDescriptor.constant 2+BinaryAddressTable.constant+650)*D := by
    nlinarith
  convert hfinal using 1
  dsimp [N,m,w,D]
  ring

/-- A sole-input constructor. Tape8 contains all selected mask-shift offsets in
increasing source-address order, at headzero; tapes0/1/2 retain original b/q/n and tape16 retains the original control,
and the other26 tapes are wholly blank at headzero. -/
theorem constructs (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1 ≤ b) (hbq : b+1 ≤ q)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs q b n Z hb hbq)
      (constant*(2^(n*b)*allowance q b n)) :=
  (runs hs q b n Z hb hbq hvq hvb hvn hc hZ).consequence (fun _ h => h) (fun _ h => h) (cost_bound q b n Z hZ)

theorem cost_volume (q b n R : ℕ) (hR : allowance q b n ≤ R) :
    constant*(2^(n*b)*allowance q b n) ≤ constant*(2^(n*b)*R) :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hR)

end
end IntegerMultBounds.Machine.BinarySelectedOffset
