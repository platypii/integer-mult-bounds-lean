module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepRowOrder

/-! Evaluate a PR589 source rank from the running destination counter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl Cover.Fallback RingFormula Stack Host Node Cover.LabelTraversal RadixDigits
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def sweepCounterRankTime (w H : ℕ) (n : Fin 9) (r : Role) :=
  2*(64*(8*(w*128)+w*(7*H+prime+31)+10*H+38)+1)+1+14*(128*H)+14 +
    time H (rankLeafCost H (fun i => time H (readTime H) (sweepCoordinateCode n r i))) sweepBinaryRankCode

theorem sweepCounterRankTime_quadratic :
    ∃ C : ℕ, ∀ w H n r, (prime^w)^128 < 2^H → sweepCounterRankTime w H n r ≤ C*(H+1)^2 := by
  obtain ⟨K,bound⟩ := sweepSourceRank_time
  refine ⟨K+128*prime+200000,?_⟩
  intro w H n r fits
  have small : 2^w < 2^H := ((Nat.pow_le_pow_left prime_prime.two_le w).trans
    (Nat.le_self_pow (by decide : 128 ≠ 0) _)).trans_lt fits
  have width : w ≤ H := by
    by_contra! h
    exact small.not_ge (Nat.pow_le_pow_right (by decide) h.le)
  unfold sweepCounterRankTime
  apply (Nat.add_le_add_left (bound H n r) _).trans
  calc
    _ ≤ 2*(64*(8*(H*128)+H*(7*H+prime+31)+10*H+38)+1)+1+14*(128*H)+14 + K*(H+1)^2 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem sweepCounterRank_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U) (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
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
    (ports : Leaf (Entry Bool 64) → Fin T → Fin 7 ↪ Fin T)
    (coordBank rankBank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (rankRegs : Leaf (Option (Fin 128)) → Fin T → Fin 4 ↪ Fin T)
    (out : Fin T) (fits : (prime^w)^128 < 2^H) (units : ∀ i, IsUnit (parent i)) :
    let mat := sweepRankMatrices w parent n role dest
    let R := Function.update S.R (regs 1) (matrixWords prime H (mat true) ++ suffix)
    let f := sweepCoordinateCode n role
    let x := fun k => eval (entryValue mat) (f k)
    let coord := fun k => compile (readLeaf ports) coordBank (f k) 0
    let coordReady := fun k => prepared coordBank (entryValue mat) H (leafReady ports mat H) (f k) 0
    prepared rankBank (rankInput x) H (rankLeafReady H x coordReady rankRegs) sweepBinaryRankCode 0 out R →
    let rows := sweepCounterRows a b zeros (regs 3) (sweepRowAxis (decide (role.bank.val / 2 = BitHosting.activePair n.val)))
    ∃ z steps, z.user = v.user ∧ steps ≤ sweepCounterRankTime w H n role ∧
      Exec body (.seq (.seq rows (.seq (refreshSweepMatrix regs) (bclear (regs 2))))
        (compile (rankLeafProgram coord rankRegs) rankBank sweepBinaryRankCode 0 out)) (mk v S) steps
        (mk z {S with R := Function.update R out (binSyms H (nodeSourceRank w parent units n role dest).val ++ R out)}) := by
  intro mat R f x coord coordReady arithmetic rows
  obtain ⟨u,k,hu,hk,install⟩ := prepareSweepDestination_exec body a b shared sep regs zeros external aOut bOut
    zeroPort n role w H pos parent old dest ds len number tail suffix v S ready clock input empty saved tmp
  obtain ⟨z,l,hz,hl,rank⟩ := sweepSourceRank_writes body ports coordBank rankBank rankRegs w H fits parent
    units n role dest out u {S with R := R} arithmetic
  exact ⟨z,k+l,hz.trans hu,Nat.add_le_add hk hl,Exec.seq install rank⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
