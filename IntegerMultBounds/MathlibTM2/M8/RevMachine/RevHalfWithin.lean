module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfFrameWithin
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.FamilyLeafCoreWithin
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfLeafWithin

/-! The actual reversed-family recursive graph has a uniform linear-volume
workspace certificate, with generated stage-1 execution beneath every leaf. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open NodeBank (tapes io)
noncomputable section
variable [M8.Machine.Net] (N : RevNetwork) {k : ℕ}
  (capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k)
  (hR : RevRuns N) (hRk : ∀ r ∈ Rk N, 1 ≤ r ∧ r < N.width) (b₀ cutoff : ℕ)

local notation "S" => Family.inv (Rev97Node.leafCore N) (lt_of_lt_of_le Nat.zero_lt_two N.two_le_width)
  (Rev97Node.half N hR hRk b₀ capacity)

/-- One fixed workspace coefficient pays every frame and every actual child.
The high-depth cutoff is a pure numerical premise, never an execution oracle. -/
theorem contract_within
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n)
    (hroles : 2 ≤ N.roleCount) (lo upper : ℤ) :
    let D := frameSpaceConstant N k (M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff)
    ∀ σ x, 1 ≤ σ.n → (S).Entry σ x → GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo upper σ x →
      GraphExists.ContractWithin (ht := Family.pcSlot_pos) S
        (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) σ x := by
  intro D
  have hspace := LeafCoreWithin.core_space cutoff hcut (io N) (RevNode.Good N)
    (fun _ _ h => RevNode.Good.to_leafCore N h)
  exact frame_contract_within N capacity hR hRk b₀ (Rev97Node.leafCore N) hspace D
    (frame_reserve N k _) lo upper hroles

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
