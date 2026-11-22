module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepPhysicalRank
public import IntegerMultBounds.MathlibTM2.M6.BitSweepSelectorCycle

/-! Evaluate all PR589 destination ranks on fixed sweep registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl Cover.Fallback RingFormula Stack Host Node Routing RadixDigits RadixCounterData
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

private def fieldPorts : Fin 7 ↪ Fin 37 := ⟨![9,10,0,11,12,13,14],by decide⟩
private def binaryPorts : Fin 6 ↪ Fin 37 := ⟨![11,15,16,17,18,19],by decide⟩
private def refreshPorts : Fin 6 ↪ Fin 37 := ⟨![21,22,23,24,25,26],by decide⟩
private def readPorts : Fin 11 ↪ Fin 37 := ⟨![27,18,28,29,30,31,32,22,20,33,34],by decide⟩
def sweepLoopPorts : Fin 7 ↪ Fin 37 := Fin.castLEEmb (by decide)

theorem sweepPhysicalCycle_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (p : Fin 37 ↪ Fin T) (rankPool : Fin ((sweepBinaryRankCode.depth+1)*13) ↪ Fin T)
    (coordPool : Fin ((sweepCoordDepth+1)*13) ↪ Fin T)
    (disjoint : ∀ i j, coordPool i ≠ rankPool j)
    (hr : ∀ i j, p i ≠ rankPool j) (hc : ∀ i j, p i ≠ coordPool j)
    (n : Fin 9) (role : Role) :
    ∃ evaluate : Pr P T Q prime U, ∀ (w H : ℕ) (parent : Fin 64 → ZMod (prime^w))
      (units : ∀ i, IsUnit (parent i)) (suffix : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime),
    let M := (prime^w)^128
    let last : Fin M := ⟨M-1,by have := pow_pos (pow_pos prime_prime.pos w) 128; dsimp [M]; omega⟩
    let mat := sweepRankMatrices w parent n role
    0 < w → M < 2^H → (S.R (p 7)).length = M →
    S.R (p 0) = (zeros prime_prime.two_le (w*128)).map digitSymbol →
    (S.R (p 5)).length = w*128 → (S.R (p 10)).length = w → (S.R (p 18)).length = H →
    (S.R (p 21)).length = 128*H →
    S.R (p 22) = matrixWords prime H (mat last true) ++ suffix →
    (∃ t, S.R (p 28) = matrixWords prime H (mat last false) ++ t) →
    S.R (p 35) = binSyms H M → S.R (p 36) = binSyms H (prime^w) →
    S.R (p 20) = binSyms H 0 → S.R (p 33) = binSyms H (1 : ZMod (prime^w)).val →
    S.R (p 34) = binSyms H ((prime^w : ℕ) : ZMod M).val →
    (∀ i ∈ ([1,2,3,4,6,9,11,12,13,14,15,16,17,19,23,25,26,27,30,31,32] : List (Fin 37)), S.R (p i) = []) →
    (∀ j, S.R (rankPool j) = []) → (∀ j, S.R (coordPool j) = []) →
    let cost := sweepCounterRankTime w H n role+(sweepBinaryRankCode.depth+sweepCoordDepth+2)*(8*H+8)+4
    ∃ z R t, z.user = v.user ∧ t ≤ M*(cost+(2*H+9*(w*128)+15)+3)+2 ∧
      Exec body (eachSym (p 7) (p 8) (.seq evaluate (advanceSweepRank prime_prime.two_le (sweepLoopPorts.trans p))))
        (mk v S) t (mk z {S with R := R}) ∧
      R (p 7) = [] ∧ R (p 8) = (S.R (p 7)).reverse ++ S.R (p 8) ∧
      R (p 2) = (descriptorSelectorFrames H (List.ofFn (nodeSourceRank w parent units n role))).reverse ∧
      ∀ k, k ≠ p 7 → k ≠ p 8 → k ≠ p 2 → R k = S.R k := by
  let a := fieldPorts.trans p
  let b := binaryPorts.trans p
  let regs := refreshPorts.trans p
  let bank := readPorts.trans p
  let source := sourcePorts (m := 64) ((Fin.castLEEmb (by decide : 10 ≤ 11)).trans bank) id
  let rankRegs := fun a dst => ((sweepConstantMap a).trans bank).trans (Equiv.swap (bank 3) dst).toEmbedding
  let coord : Fin 128 → Fin T → Pr P T Q prime U := fun i => compile (readLeaf (leafBank source)) (registerBank coordPool) (sweepCoordinateCode n role i) 0
  let arithmetic := compile (rankLeafProgram coord rankRegs) (registerBank rankPool) sweepBinaryRankCode 0 (p 1)
  let rows : Pr P T Q prime U := sweepCounterRows a b (p 20) (regs 3) (sweepRowAxis (decide (role.bank.val / 2 = BitHosting.activePair n.val)))
  refine ⟨.seq (.seq rows (.seq (refreshSweepMatrix regs) (bclear (regs 2))))
    ((initFrames rankPool (p 35) (sweepBinaryRankCode.depth+1)).seq
      (((initFrames coordPool (p 36) (sweepCoordDepth+1)).seq (arithmetic.seq (clearFrames coordPool (sweepCoordDepth+1)))).seq
        (clearFrames rankPool (sweepBinaryRankCode.depth+1)))),?_⟩
  intro w H parent units suffix v S M last mat positive fits ticks counter digitWidth fieldWidth bits clock input chart
    rankWord coordWord zero one radix blank blankRank blankCoord cost
  apply sweepSelectorCycle_exec body prime_prime.two_le (by omega : 0 < w*128) (pow_mul prime w 128).symm
    (sweepLoopPorts.trans p) (p 22) (p 7) (p 8) (fun i => p.injective.ne (by decide +revert)) (by simp [List.nodup_cons])
    (fun i => ⟨p.injective.ne (by decide +revert),p.injective.ne (by decide +revert)⟩) H cost
    (nodeSourceRank w parent units n role) (fun d => matrixWords prime H (mat d true) ++ suffix)
    _ v S counter digitWidth ticks (blank 2 (by decide)) (fun i hi => blank (sweepLoopPorts i) (by decide +revert)) input
  · intro old dest ds len number u B live previous keep
    have stable (i : Fin 37) (hi : i ∉ ([22,7,8,0,2] : List (Fin 37))) : B.R (p i) = S.R (p i) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
      exact keep _ (p.injective.ne hi.1) (p.injective.ne hi.2.1) (p.injective.ne hi.2.2.1)
        (p.injective.ne hi.2.2.2.1) (p.injective.ne hi.2.2.2.2)
    have fresh (i : Fin 37) (hi : i ∉ ([22,7,8,0,2] : List (Fin 37)))
        (hj : i ∈ ([1,2,3,4,6,9,11,12,13,14,15,16,17,19,23,25,26,27,30,31,32] : List (Fin 37))) :=
      (stable i hi).trans (blank i hj)
    have chartOld : ∃ t, B.R (p 28) = matrixWords prime H (mat old false) ++ t := by
      obtain ⟨t,h⟩ := chart
      rw [show mat last false = mat old false from sweepRankMatrices_chart ..] at h
      exact ⟨t,(stable 28 (by decide)).trans h⟩
    apply sweepPhysicalRank_exec body (fieldPorts.trans p) (binaryPorts.trans p) rfl
      (fun i j => by rcases (show fieldPorts i ≠ binaryPorts j ∨ i = 3 ∧ j = 0 by decide +revert) with h|h
                     exacts [Or.inl (p.injective.ne h),Or.inr h])
      (refreshPorts.trans p) (p 20) (p.injective.ne (by decide)) (fun i => p.injective.ne (by decide +revert))
      (fun i => p.injective.ne (by decide +revert)) (fun i => p.injective.ne (by decide +revert)) n role w H
      (by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at fits; have := pow_pos (pow_pos prime_prime.pos w) 128; omega)
      parent old dest ds len number [] suffix u B
      ⟨by rw [List.append_nil]; exact live, (congrArg List.length (stable 10 (by decide))).trans fieldWidth,
        fun i hi => fresh (fieldPorts i) (by decide +revert) (by decide +revert),
        (congrArg List.length (stable 18 (by decide))).trans bits,
        fun i hi => fresh (binaryPorts i) (by decide +revert) (by decide +revert), (stable 20 (by decide)).trans zero⟩
      ((congrArg List.length (stable 21 (by decide))).trans clock) previous
      (fresh 23 (by decide) (by decide)) (fresh 25 (by decide) (by decide)) (fresh 26 (by decide) (by decide))
      rankPool coordPool (readPorts.trans p) rfl disjoint (fun i => hr _) (fun i => hc _) (p 35) (p 36) (p 1)
      (hr _) (hc _) (hr _) (p.injective.ne (by decide)) (p.injective.ne (by decide)) (hr _) (hc _)
      (fun i => p.injective.ne (by decide +revert)) fits units
      (fun j => (keep _ (hr _ j).symm (hr _ j).symm (hr _ j).symm (hr _ j).symm (hr _ j).symm).trans (blankRank j))
      (fun j => (keep _ (hc _ j).symm (hc _ j).symm (hc _ j).symm (hc _ j).symm (hc _ j).symm).trans (blankCoord j))
      ((stable 35 (by decide)).trans rankWord) ((stable 36 (by decide)).trans coordWord)
      (fresh 1 (by decide) (by decide)) chartOld ((congrArg List.length (stable 18 (by decide))).trans bits)
      ((stable 20 (by decide)).trans zero) ((stable 33 (by decide)).trans one) ((stable 34 (by decide)).trans radix)
      (fun i hi => fresh (readPorts i) (by decide +revert) (by decide +revert))

end IntegerMultBounds.MathlibTM2.M6.BitNode
