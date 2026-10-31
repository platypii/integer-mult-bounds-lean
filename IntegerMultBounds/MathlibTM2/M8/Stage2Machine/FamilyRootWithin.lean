module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Spec
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfWithin

/-! The actual PR97 root's halting certificate bounds every reachable prefix,
with one coefficient independent of atom width, atom count and recursion depth. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyRootWithin
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open FlatCoordinateSchedule (bits)
open RevMachine
open Family (Frame)
open RevHalf (pcs Ok)
open FamilyRoot
noncomputable section
variable [M8.Machine.Net] {k : ℕ}
  (capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k)

def coefficient (k cutoff : ℕ) : ℕ := RevHalf.frameSpaceConstant rev97m k
  (M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff)

theorem root_heads (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n)
    (b₀ : ℕ) (σ : Frame (pcs rev97m) capacity) (hok : Ok rev97m b₀ σ)
    (hn : 1 ≤ σ.n) (hret : σ.ret = .halt)
    (x : Fin (volume prime σ.v) → ZMod 2) (lo upper : ℤ)
    (hmargin : ∀ j, lo+(coefficient k cutoff*volume prime σ.v : ℕ) ≤
      (padded capacity (σ.at (rolesOf x) (Prepare.rest b₀ 529))).head j ∧
      (padded capacity (σ.at (rolesOf x) (Prepare.rest b₀ 529))).head j+
        (coefficient k cutoff*volume prime σ.v : ℕ) ≤ upper)
    {n : ℕ} {z} (hr : run (machine capacity) n
      (entry capacity .prepare (σ.at (rolesOf x) (Prepare.rest b₀ 529))) = some z) :
    ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper := by
  let S := Family.inv (Rev97Node.leafCore rev97m) Rev97Node.width97_pos
    (Rev97Node.half rev97m runs_rev97m Rev97Node.rk97 b₀ capacity)
  have he : S.Entry σ (σ.at (rolesOf x) (Prepare.rest b₀ 529)) := by
    refine ⟨hok,rolesOf x,⟨σ.hpos,x,rfl⟩,?_⟩
    rw [hok.b]
    rfl
  have h := RevHalf.contract_within rev97m capacity runs_rev97m Rev97Node.rk97 b₀ cutoff hcut
    (rev97m.two_le_width.trans runs_rev97m.width_le_roleCount) lo upper σ _ hn he hmargin
  exact GraphExists.ContractWithin.prefix S h hret hr

/-- The existing exact root semantics and runtime retain the same prefix-space certificate. -/
theorem root_hoare (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b₀ : ℕ, ∀ L : ℝ, 1 ≤ L → ((bits b₀).length : ℝ) ≤ L →
      ((max 1 b₀ : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau ≤ L →
      ∀ σ : Frame (pcs rev97m) capacity, Ok rev97m b₀ σ → 1 ≤ σ.n → σ.ret = .halt →
      ∀ (x : Fin (volume prime σ.v) → ZMod 2) (lo upper : ℤ),
        (∀ j, lo+(coefficient k cutoff*volume prime σ.v : ℕ) ≤
          (padded capacity (σ.at (rolesOf x) (Prepare.rest b₀ 529))).head j ∧
          (padded capacity (σ.at (rolesOf x) (Prepare.rest b₀ 529))).head j+
            (coefficient k cutoff*volume prime σ.v : ℕ) ≤ upper) →
        HoareWithin (machine capacity) (fun w => w = padded capacity (σ.at (rolesOf x) (Prepare.rest b₀ 529)))
          (fun w => ∃ y : Fin (volume prime σ.v) → ZMod 2, RevT prime b₀ σ.n σ.v (FamilyRoot.ext x) (FamilyRoot.ext y) ∧
            w = padded capacity (σ.exitAt (rolesOf y) 529))
          ⌊bound C L σ.n * volume prime σ.v⌋₊ (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨C,hC,ht⟩ := FamilyRoot.root_hoare capacity (Spec.familySpec capacity)
  refine ⟨C,hC,?_⟩
  intro b₀ L hL hbits hpower σ hok hn hret x lo upper hm
  apply HoareWithin.of_time_invariant (ht b₀ L hL hbits hpower σ hok hn hret x)
  rintro z ⟨v,rfl,n,hr⟩
  rw [start_entry] at hr
  exact root_heads capacity cutoff hcut b₀ σ hok hn hret x lo upper hm hr

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.FamilyRootWithin
