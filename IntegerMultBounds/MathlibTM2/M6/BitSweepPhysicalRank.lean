module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepCounterRank
public import IntegerMultBounds.MathlibTM2.M6.BitSweepRankFrames

/-! The PR589 destination evaluator with initialized input words and blank arithmetic frames. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl Cover.Fallback RingFormula Stack Host Node Cover.LabelTraversal RadixDigits
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def sweepCoordDepth : ℕ :=
  Finset.univ.sup fun i : Fin 128 => max (activeCoordinateCode i).depth (inactiveCoordinateCode i).depth

theorem sweepCoordDepth_bound (n : Fin 9) (r : Role) (i : Fin 128) :
    (sweepCoordinateCode n r i).depth ≤ sweepCoordDepth := by
  have bound := Finset.le_sup (s := Finset.univ)
    (f := fun j : Fin 128 => max (activeCoordinateCode j).depth (inactiveCoordinateCode j).depth) (Finset.mem_univ i)
  unfold sweepCoordinateCode
  split
  · exact (Nat.le_max_left ..).trans bound
  · exact (Nat.le_max_right ..).trans bound

theorem sweepPhysicalRank_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U) (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
    (shared : a 3 = b 0) (sep : ∀ i j, a i ≠ b j ∨ i = 3 ∧ j = 0)
    (regs : Fin 6 ↪ Fin T) (zeros : Fin T) (external : zeros ≠ regs 3) (aOut : ∀ i, a i ≠ regs 3) (bOut : ∀ i, b i ≠ regs 3)
    (zeroPort : ∀ i, zeros ≠ b i) (n : Fin 9) (role : Role)
    (w H : ℕ) (pos : 0 < H) (parent : Fin 64 → ZMod (prime^w)) (old dest : Fin ((prime^w)^128)) (ds : List (Fin prime))
    (len : ds.length = w*128) (number : value ds = dest.val) (tail suffix : List (Fin (prime+4)))
    (v : HS T Q prime U) (S : Stacks T prime)
    (ready : S.R (a 2) = ds.map digitSymbol ++ tail ∧ (S.R (a 1)).length = w ∧
      (∀ i : Fin 7, i = 0 ∨ 3 ≤ i → S.R (a i) = []) ∧ (S.R (b 4)).length = H ∧
      (∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 → S.R (b i) = []) ∧ S.R zeros = binSyms H 0)
    (clock : (S.R (regs 0)).length = 128*H)
    (input : S.R (regs 1) = matrixWords prime H (sweepRankMatrices w parent n role old true) ++ suffix)
    (empty : S.R (regs 2) = []) (saved : S.R (regs 4) = []) (tmp : S.R (regs 5) = [])
    (rankPool : Fin ((sweepBinaryRankCode.depth+1)*13) ↪ Fin T) (coordPool : Fin ((sweepCoordDepth+1)*13) ↪ Fin T)
    (bank : Fin 11 ↪ Fin T) (matrix : bank 7 = regs 1)
    (disjoint : ∀ i j, coordPool i ≠ rankPool j)
    (rankApart : ∀ i j, bank i ≠ rankPool j) (coordApart : ∀ i j, bank i ≠ coordPool j)
    (rankMod coordMod out : Fin T) (rankOff : ∀ j, rankMod ≠ rankPool j)
    (coordOff : ∀ j, coordMod ≠ coordPool j) (modOff : ∀ j, coordMod ≠ rankPool j)
    (rankKeep : rankMod ≠ bank 7) (coordKeep : coordMod ≠ bank 7)
    (outside : ∀ j, out ≠ rankPool j) (coordOut : ∀ j, out ≠ coordPool j) (bankOut : ∀ i, bank i ≠ out)
    (fits : (prime^w)^128 < 2^H) (units : ∀ i, IsUnit (parent i))
    (blankRank : ∀ j, S.R (rankPool j) = []) (blankCoord : ∀ j, S.R (coordPool j) = [])
    (rankWord : S.R rankMod = binSyms H ((prime^w)^128)) (coordWord : S.R coordMod = binSyms H (prime^w))
    (blankOut : S.R out = []) (chart : ∃ t, S.R (bank 2) = matrixWords prime H (sweepRankMatrices w parent n role old false) ++ t)
    (width : (S.R (bank 1)).length = H) (zero : S.R (bank 8) = binSyms H 0)
    (one : S.R (bank 9) = binSyms H (1 : ZMod (prime^w)).val)
    (radix : S.R (bank 10) = binSyms H ((prime^w : ℕ) : ZMod ((prime^w)^128)).val)
    (free : ∀ i : Fin 11, i ∈ [0,4,5,6] → S.R (bank i) = []) :
    let source := sourcePorts ((Fin.castLEEmb (by decide : 10 ≤ 11)).trans bank) id
    let rankRegs := fun a dst => ((sweepConstantMap a).trans bank).trans (Equiv.swap (bank 3) dst).toEmbedding
    let coord := fun i => compile (readLeaf (leafBank source)) (registerBank coordPool) (sweepCoordinateCode n role i) 0
    let arithmetic := compile (rankLeafProgram coord rankRegs) (registerBank rankPool) sweepBinaryRankCode 0 out
    let rows := sweepCounterRows a b zeros (regs 3) (sweepRowAxis (decide (role.bank.val / 2 = BitHosting.activePair n.val)))
    let R := Function.update S.R (regs 1) (matrixWords prime H (sweepRankMatrices w parent n role dest true) ++ suffix)
    ∃ z steps, z.user = v.user ∧ steps ≤ sweepCounterRankTime w H n role+(sweepBinaryRankCode.depth+sweepCoordDepth+2)*(8*H+8)+4 ∧
      Exec body (.seq (.seq rows (.seq (refreshSweepMatrix regs) (bclear (regs 2))))
        ((initFrames rankPool rankMod (sweepBinaryRankCode.depth+1)).seq
          (((initFrames coordPool coordMod (sweepCoordDepth+1)).seq (arithmetic.seq (clearFrames coordPool (sweepCoordDepth+1)))).seq
            (clearFrames rankPool (sweepBinaryRankCode.depth+1))))) (mk v S) steps
        (mk z {S with R := Function.update R out (binSyms H (nodeSourceRank w parent units n role dest).val)}) := by
  intro source rankRegs coord arithmetic rows R
  obtain ⟨u,k,hu,hk,install⟩ := prepareSweepDestination_exec body a b shared sep regs zeros external aOut bOut
    zeroPort n role w H pos parent old dest ds len number tail suffix v S ready clock input empty saved tmp
  let mat := sweepRankMatrices w parent n role dest
  have keep (i) (hi : i ≠ bank 7) : R i = S.R i := Function.update_of_ne (matrix ▸ hi) _ _
  have slot (i : Fin 11) (hi : i ≠ 7) := keep _ (bank.injective.ne hi)
  have packed (b : Bool) : ∃ t, R (bank (if b then 7 else 2)) = matrixWords prime H (mat b) ++ t := by
    cases b
    · obtain ⟨t,h⟩ := chart
      rw [sweepRankMatrices_chart w parent n role old dest] at h
      exact ⟨t,(slot 2 (by decide)).trans h⟩
    · exact ⟨suffix,by simp [R,mat,matrix]⟩
  have destBlank := (keep out (bankOut 7).symm).trans blankOut
  obtain ⟨z,l,hz,hl,run⟩ := sweepRankFromBlankFrames_exec body rankPool coordPool bank disjoint rankApart
    coordApart rankMod coordMod out rankOff coordOff modOff outside coordOut bankOut H fits mat
    (sweepCoordinateCode n role) le_rfl (sweepCoordDepth_bound n role) u {S with R := R}
    (fun j => (keep _ (rankApart 7 j).symm).trans (blankRank j))
    (fun j => (keep _ (coordApart 7 j).symm).trans (blankCoord j))
    ((keep _ rankKeep).trans rankWord) ((keep _ coordKeep).trans coordWord) destBlank packed
    ((congrArg List.length (slot 1 (by decide))).trans width) ((slot 8 (by decide)).trans zero) ((slot 9 (by decide)).trans one)
    ((slot 10 (by decide)).trans radix) (fun i hi => (slot i (by rintro rfl; simp at hi)).trans (free i hi))
  have number := sweepCoordinate_rank w parent units n role dest
  dsimp only at number
  change FlatCoordinateLayout.rank (fun i => eval (entryValue mat) (sweepCoordinateCode n role i)) = _ at number
  refine ⟨z,k+l,hz.trans hu,?_,Exec.seq install ?_⟩
  · unfold sweepCounterRankTime
    omega
  · simpa only [number,destBlank,List.append_nil] using run

theorem sweepPhysicalRankTime_quadratic (D E : ℕ) :
    ∃ C : ℕ, ∀ w H n r, (prime^w)^128 < 2^H →
      sweepCounterRankTime w H n r+(D+E+2)*(8*H+8)+4 ≤ C*(H+1)^2 := by
  obtain ⟨K,bound⟩ := sweepCounterRankTime_quadratic
  refine ⟨K+8*(D+E+2)+4,?_⟩
  intro w H n r fits
  have h := bound w H n r fits
  ring_nf at h ⊢
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
