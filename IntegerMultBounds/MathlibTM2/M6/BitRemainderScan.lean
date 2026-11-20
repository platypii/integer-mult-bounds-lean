module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGeneratedGoodRecord

/-! Instantiate the generated cover scan with the physical PR589 idle child. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open IntegerMultBounds.MathlibTM2.Cover
open IntegerMultBounds.MathlibTM2.Cover.Fallback M8.RevMachine

/-- A record keeps the middle and trailing spectators. The prefix (including
the cover label) selects the record, so it contributes to its count exactly once. -/
theorem remainderRecord_volume (v : Descriptor) (w rows : ℕ) (e : ℕ × ℕ)
    (he : e ∈ BitHosting.remainderIntervals) (width : v.width = 64*(w+1))
    (split : v.rows = 142080*rows) :
    let directory := role v 142080
    let child := phaseIntervalChild e.1 e.2 (w+1) (v.between*v.afterD) 64
    LabelMask.records directory * volume prime child * 142080 = volume prime v := by
  intro directory child
  obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts e he
  rw [intervalChild_volume ordered (show e.2 ≤ 64 by omega)]
  simp only [LabelMask.records,directory,role,volume,width,split,
    Nat.mul_div_cancel_left _ (by decide : 0 < 142080),show 64*(w+1) = (w+1)*64 by omega,
    pow_mul,pow_add]
  ac_rfl

/-- The idle descriptor has the width, volume, and rational pivot certificate
required by the generated record program, with the actual binary header sizes. -/
theorem remainderRecord_scan [M8.Machine.Net] {T work Q : ℕ} {F U : Type}
    (e : ℕ × ℕ) (he : e ∈ BitHosting.remainderIntervals) (w W : ℕ) (hW : 0 < W)
    (parent parentInv : Fin 64 → ZMod (prime^(w+1))) (inv : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (arity : ℕ) (source : ℤ → Fin 4) (head : ℤ)
    (capacity : 217 ≤ Q) (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) :
    let M := prime^(w+1)
    let child := phaseIntervalChild e.1 e.2 (w+1) W 64
    let D : Matrix (Fin 64) (Fin 64) ℚ := Matrix.diagonal fun i =>
      if e.1 ≤ i.val ∧ i.val < e.2 then 1 else 0
    ∃ (positive : child.Positive) (width : child.width = D.rank*(w+1))
      (rankFits : D.rank ≤ 64) (length : volume prime child = M^64*(M^64*W)),
      GeneratedRecordSpec (F := F) (U := U) child positive w D width (intervalDiagonal_idem 64 e.1 e.2)
        (intervalFactor 64 e.1 e.2) (intervalFactor_denominators 64 e.1 e.2) rankFits parent parentInv inv
        io arity (Nat.size_le.mp (le_refl M.size)) (Nat.size_le.mp (le_refl W.size)) hW length capacity
        source head fits cap false := by
  intro M child D
  obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts e he
  have bounded : e.2 ≤ 64 := by omega
  have rank : D.rank = e.2-e.1 := intervalDiagonal_rank bounded
  have rankFits : D.rank ≤ 64 := by omega
  have width : child.width = D.rank*(w+1) := by rw [rank]; rfl
  have pos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have positive : child.Positive :=
    ⟨Nat.zero_lt_one,Nat.zero_lt_one,pow_pos pos _,pow_pos pos _,Nat.mul_pos (pow_pos pos _) hW⟩
  have length : volume prime child = M^64*(M^64*W) := by
    rw [intervalChild_volume ordered bounded, pow_add, Nat.mul_assoc]
  exact ⟨positive,width,rankFits,length,generatedRecordScan_exec child positive w D width
    (intervalDiagonal_idem 64 e.1 e.2) (intervalFactor 64 e.1 e.2)
    (intervalFactor_denominators 64 e.1 e.2) rankFits parent parentInv inv io arity _ _ hW
    length capacity source head fits cap⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
