module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepBlockRouting
public import IntegerMultBounds.MathlibTM2.M6.BitSweepNodeAddress

/-! Source ranks for the record permutation of a PR589 parent and stage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Join the sixteen active digits and the 112 remaining digits into a
single record rank, in the order consumed by the block gather. -/
def sweepRank (M : ℕ) : Fin (M^16) × Fin (M^112) ≃ Fin (M^128) :=
  finProdFinEquiv.trans (finCongr (by rw [← pow_add]))

/-- Decode a destination record in a singleton block and read its parent
rank. Neither the block count nor the spectator width enters the formula. -/
noncomputable def nodeSourceRank (w : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (r : Role) (dest : Fin ((prime^w)^128)) :=
  let (a,t) := (sweepRank (prime^w)).symm dest
  let cell := finProdFinEquiv (a,finProdFinEquiv ((0 : Fin 1),finProdFinEquiv (t,(0 : Fin 1))))
  let s := ((sweepRoleEquiv w 1 1 n r).symm cell).2.1
  FlatCoordinateLayout.rank (nodeDigitsEquiv w parent units s)

/-- The same record permutation implements the full physical address change
for every inherited block and every offset inside a record. -/
theorem nodeToSweep_recordPermutation (w : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (r : Role) :
    let M := prime^w
    ∃ p : Equiv.Perm (Fin (M^128)), (∀ d, p.symm d = nodeSourceRank w parent units n r d) ∧
      ∀ {B W : ℕ} (b : Fin B) (i : Fin (M^128)) (j : Fin W),
      let (a,t) := (sweepRank M).symm (p i)
      nodeToSweep w B W parent units n r (stagedOwnerIndex b (finProdFinEquiv (i,j))) =
        finProdFinEquiv (a,finProdFinEquiv (b,finProdFinEquiv (t,j))) := by
  intro M
  let source := (nodeDigitsEquiv w parent units).trans FlatCoordinateLayout.rankEquiv
  obtain ⟨chart,read⟩ := sweepRecordPermutation w n r
  refine ⟨source.symm.trans (chart.trans (sweepRank M)),?_,?_⟩
  · intro d
    obtain ⟨s,rfl⟩ := (chart.trans (sweepRank M)).surjective d
    have singleton := read s (0 : Fin 1) (0 : Fin 1)
    let dest := (sweepRank M) (chart s)
    let cell := fun (x : Fin (M^16) × Fin (M^112)) =>
      finProdFinEquiv (x.1,finProdFinEquiv ((0 : Fin 1),finProdFinEquiv (x.2,(0 : Fin 1))))
    change source (chart.symm ((sweepRank M).symm dest)) =
      source (((sweepRoleEquiv w 1 1 n r).symm (cell ((sweepRank M).symm dest))).2.1)
    rw [show (sweepRank M).symm dest = chart s from (sweepRank M).symm_apply_apply _,chart.symm_apply_apply]
    rw [show cell (chart s) = sweepRoleEquiv w 1 1 n r (0,s,0) from singleton.symm,
      Equiv.symm_apply_apply]
  intro B W b i j
  obtain ⟨s,rfl⟩ := source.surjective i
  have node : stagedOwnerIndex b (finProdFinEquiv (source s,j)) =
      nodeWindowEquiv w B W parent units (b,s,j) := rfl
  simp only [node,nodeToSweep,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact read s b j

end IntegerMultBounds.MathlibTM2.M6.BitNode
