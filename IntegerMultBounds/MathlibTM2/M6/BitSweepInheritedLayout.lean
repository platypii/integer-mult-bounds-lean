module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepHeaderBlock

/-! Identify both words of the contiguous block pass with the staged owner layouts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Shared50ModularControl CompactRows
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem sweepStagedWord {M B W : ℕ} {α : Type} (x : Fin (M^16*(B*(M^112*W))) → α) :
    List.ofFn (compactTranspose x) = (List.finRange B).flatMap fun b =>
      (List.ofFn fun i : Fin (M^128) => List.ofFn fun j : Fin W => x (stagedOwnerIndex b (finProdFinEquiv (i,j)))).flatten := by
  have pack {m n : ℕ} (f : Fin (m*n) → α) :
      List.ofFn f = (List.ofFn fun i => List.ofFn fun j => f (finProdFinEquiv (i,j))).flatten := by
    simpa only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using List.ofFn_mul f
  rw [pack (compactTranspose x)]
  simp only [List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext b
  rw [List.ofFn_congr (ordinaryCompact_width M W),pack]
  simp only [compactTranspose_stagedOwnerIndex]

private theorem stagedOwner_rank {M B W : ℕ} (b : Fin B) (i : Fin (M^128)) (j : Fin W) :
    let (a,t) := (sweepRank M).symm i
    stagedOwnerIndex b (finProdFinEquiv (i,j)) = finProdFinEquiv (a,finProdFinEquiv (b,finProdFinEquiv (t,j))) := by
  obtain ⟨⟨a,t⟩,rfl⟩ := (sweepRank M).surjective i
  simp only [Equiv.symm_apply_apply]
  have cell : (finProdFinEquiv ((sweepRank M) (a,t),j)).cast (ordinaryCompact_width M W).symm =
      finProdFinEquiv (a,finProdFinEquiv (t,j)) := by
    apply Fin.ext
    simp [sweepRank,finProdFinEquiv]
    <;> ring
  simp only [stagedOwnerIndex,cell,Equiv.symm_apply_apply]

theorem sweepStagedOutput {B W : ℕ} {α : Type} (w : ℕ) (parent : Fin 64 → ZMod (prime^w))
    (units : ∀ i, IsUnit (parent i)) (n : Fin 9) (r : Role)
    (x : Fin ((prime^w)^16*(B*((prime^w)^112*W))) → α) :
    List.ofFn (compactTranspose (x ∘ (nodeToSweep w B W parent units n r).symm)) =
      (List.finRange B).flatMap fun b => (List.ofFn fun i : Fin ((prime^w)^128) => List.ofFn fun j : Fin W =>
        x (stagedOwnerIndex b (finProdFinEquiv (nodeSourceRank w parent units n r i,j)))).flatten := by
  rw [sweepStagedWord]
  obtain ⟨p,rank,cell⟩ := nodeToSweep_recordPermutation w parent units n r
  apply congrArg (fun f : Fin B → List α => (List.finRange B).flatMap f)
  funext b
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  change x ((nodeToSweep w B W parent units n r).symm _) = _
  apply congrArg x
  apply (nodeToSweep w B W parent units n r).injective
  rw [Equiv.apply_symm_apply,← rank,cell,Equiv.apply_symm_apply]
  exact stagedOwner_rank b i j

end IntegerMultBounds.MathlibTM2.M6.BitNode
