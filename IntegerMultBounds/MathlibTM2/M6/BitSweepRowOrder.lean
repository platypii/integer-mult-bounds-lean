module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepMatrixRefresh
public import IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose
public import IntegerMultBounds.MathlibTM2.M6.BitSweepCounterRows

/-! Counter positions for the two input rows of a PR589 sweep. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl FlatCoordinateLayout Cover.Fallback
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

def sweepRowAxis (active : Bool) (r : Fin 2) (j : Fin 64) : Fin 128 :=
  if active then match stageAxis.symm j with
    | .inl k => Fin.castAdd 112 (if r = 0 then Fin.castAdd 8 k else Fin.natAdd 8 k)
    | .inr k => Fin.natAdd 16 (finSumFinEquiv (if r = 0 then Sum.inl (finProdFinEquiv k)
      else Sum.inr (finProdFinEquiv k) : Fin 56 ⊕ Fin 56))
  else finSumFinEquiv (if r = 0 then Sum.inl j else Sum.inr j : Fin 64 ⊕ Fin 64)

private theorem sweepRank_coordinates {M : ℕ} [NeZero M] (a : Fin (M^16)) (b : Fin (M^112)) :
    coordinates (sweepRank M (a,b)) = (fun i => Fin.addCases (motive := fun _ => ZMod M) (coordinates a) (coordinates b) i) := by
  apply rankEquiv.injective
  change rank (coordinates (sweepRank M (a,b))) = rank _
  rw [rank_coordinates]
  apply Fin.ext
  rw [ArbitraryWidthSliceTranspose.rank_append,rank_coordinates,rank_coordinates]
  change b.val + M^112*a.val = _
  ac_rfl

theorem sweepDestinationRows (w H : ℕ) (parent : Fin 64 → ZMod (prime^w)) (n : Fin 9)
    (r : Role) (dest : Fin ((prime^w)^128)) :
    destinationRows prime H (sweepRankMatrices w parent n r dest true) =
      matrixWords prime H (fun i j => coordinates dest
        (sweepRowAxis (decide (r.bank.val / 2 = BitHosting.activePair n.val)) i j)) := by
  apply congrArg (matrixWords prime H)
  ext i j
  change sweepRankMatrices w parent n r dest true _ j = _
  by_cases active : r.bank.val / 2 = BitHosting.activePair n.val
  · obtain ⟨⟨a,b⟩,rfl⟩ := (sweepRank (prime^w)).surjective dest
    rw [sweepRank_coordinates]
    obtain ⟨k,rfl⟩ := stageAxis.surjective j
    fin_cases i <;> cases k <;>
      simp [sweepRankMatrices,sweepRowAxis,active,chartAddress,copyAddress,chartHalves,
        chartAddress.copyExterior,copyActive,rankEquiv] <;> try rfl
    rename_i k
    have eqn (i : Fin 8) : i.addNat 8 = Fin.natAdd 8 i := Fin.ext (Nat.add_comm ..)
    change AffineFieldCoordinates.embed (fun i => coordinates a (Fin.castAdd 8 i),fun i => coordinates a (i.addNat 8)) (k.addNat 8) = coordinates a (k.addNat 8)
    simpa only [eqn] using (AffineFieldCoordinates.embed_d
      (fun i => coordinates a (Fin.castAdd 8 i),fun i => coordinates a (Fin.natAdd 8 i)) k)
  · fin_cases i <;> simp [sweepRankMatrices,sweepRowAxis,active]

open Stack Host Node Cover.LabelTraversal RadixDigits

theorem sweepDestinationRows_writes {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U) (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
    (shared : a 3 = b 0) (sep : ∀ i j, a i ≠ b j ∨ i = 3 ∧ j = 0)
    (zeros out : Fin T) (external : zeros ≠ out) (aOut : ∀ i, a i ≠ out) (bOut : ∀ i, b i ≠ out)
    (zeroPort : ∀ i, zeros ≠ b i) (n : Fin 9) (role : Role)
    (w H : ℕ) (pos : 0 < H) (parent : Fin 64 → ZMod (prime^w)) (dest : Fin ((prime^w)^128)) (ds : List (Fin prime))
    (len : ds.length = w*128) (number : value ds = dest.val) (tail : List (Fin (prime+4))) :
    let ok := fun (R : Regs T prime) => R (a 2) = ds.map digitSymbol ++ tail ∧ (R (a 1)).length = w ∧
      (∀ i : Fin 7, i = 0 ∨ 3 ≤ i → R (a i) = []) ∧ (R (b 4)).length = H ∧
      (∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 → R (b i) = []) ∧ R zeros = binSyms H 0
    let cost := 8*(w*128)+w*(7*H+prime+31)+10*H+38
    Writes body ok out (sweepCounterRows a b zeros out
      (sweepRowAxis (decide (role.bank.val / 2 = BitHosting.activePair n.val))))
      (destinationRows prime H (sweepRankMatrices w parent n role dest true)) (2*(64*cost+1)+1) := by
  rw [sweepDestinationRows]
  exact sweepCounterRows_writes body a b shared sep zeros out external aOut bOut zeroPort _ w H pos dest ds len number tail

end IntegerMultBounds.MathlibTM2.M6.BitNode
