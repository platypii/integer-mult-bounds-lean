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

theorem prepareSweepDestination_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U) (a : Fin 7 ↪ Fin T) (b : Fin 6 ↪ Fin T)
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
    (empty : S.R (regs 2) = []) (saved : S.R (regs 4) = []) (tmp : S.R (regs 5) = []) :
    let rows := sweepCounterRows a b zeros (regs 3) (sweepRowAxis (decide (role.bank.val / 2 = BitHosting.activePair n.val)))
    let cost := 8*(w*128)+w*(7*H+prime+31)+10*H+38
    ∃ z steps, z.user = v.user ∧ steps ≤ 2*(64*cost+1)+1+14*(128*H)+14 ∧
      Exec body (.seq rows (.seq (refreshSweepMatrix regs) (bclear (regs 2)))) (mk v S) steps
        (mk z {S with R := Function.update S.R (regs 1) (matrixWords prime H (sweepRankMatrices w parent n role dest true) ++ suffix)}) := by
  intro rows cost
  let mat := fun d => sweepRankMatrices w parent n role d true
  obtain ⟨u,k,hu,hk,write⟩ := sweepDestinationRows_writes body a b shared sep zeros (regs 3)
    external aOut bOut zeroPort n role w H pos parent dest ds len number tail v S ready
  let B := {S with R := Function.update S.R (regs 3) (destinationRows prime H (mat dest) ++ S.R (regs 3))}
  obtain ⟨y,hy,install⟩ := refreshSweepMatrix_exec body regs w H parent n role old dest u B suffix (S.R (regs 3))
    (by simpa [B] using clock) (by simpa [B] using input) (Function.update_self ..)
    (by simpa [B] using saved) (by simpa [B] using tmp)
  let F := {S with R := Function.update (Function.update S.R (regs 2) (destinationRows prime H (mat old))) (regs 1) (matrixWords prime H (mat dest) ++ suffix)}
  have installed : Exec body (refreshSweepMatrix regs) (mk u B) (12*(128*H)+12) (mk y F) := by
    convert install using 1
    apply congrArg (mk y)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h₁ : i = regs 1 <;> by_cases h₂ : i = regs 2 <;> by_cases h₃ : i = regs 3 <;> simp_all [F,B,mat]
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (regs 2) y F
  have size : (F.R (regs 2)).length = 128*H := by simp [F,destinationRows_length]
  refine ⟨z,k+(12*(128*H)+12+(2*(F.R (regs 2)).length+2)),hz.trans (hy.trans hu),?_,Exec.seq write (Exec.seq installed ?_)⟩
  · rw [size]; change k ≤ 2*(64*cost+1)+1 at hk; omega
  · simpa only [F,Function.update_comm (regs.injective.ne (by decide : (1 : Fin 6) ≠ 2)),
      Function.update_idem,← empty,Function.update_eq_self] using clear

end IntegerMultBounds.MathlibTM2.M6.BitNode
