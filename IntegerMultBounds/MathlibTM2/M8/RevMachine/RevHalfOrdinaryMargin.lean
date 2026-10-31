module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfVolumeMargin
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfFrameBankBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphFrameRawMargin

/-! One frame-entry reserve transfers to every ordinary leaf or retirement
bank and every private padding. The boundary offset costs at most one cell. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open NodeBank (tapes)
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  (capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k)
  (hR : RevRuns N) (hRk : ∀ r ∈ Rk N, 1 ≤ r ∧ r < N.width) (b₀ : ℕ)
  {core : Graph.Block (CommonBank.count (tapes N)) prime} {coreCost : ℕ → ℕ → ℕ}
  (hcore : Family.LeafCore core (RevNode.Good N) coreCost)

local notation "S" => Family.inv hcore (lt_of_lt_of_le Nat.zero_lt_two N.two_le_width)
  (Rev97Node.half N hR hRk b₀ capacity)

theorem ordinary_bank_margin (D B : ℕ) (lo hi : ℤ)
    (σ : (S).Shape) (x : Tapes (CommonBank.count (tapes N)) prime) (hx : (S).Entry σ x)
    (hm : GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo hi σ x)
    (roles : Tapes (tapes N) prime) (hg : RevNode.Good N σ.v roles)
    (c : Fin CommonBank.K → Option ℕ)
    (hB : B+1 ≤ D*RecursiveInterchangeLayout.volume prime σ.v) :
    ∀ n j, lo+(B : ℕ) ≤ (SharedBankStageInput.raw (σ.at roles c) n).head j ∧
      (SharedBankStageInput.raw (σ.at roles c) n).head j+(B : ℕ) ≤ hi := by
  have hraw := GraphExists.volume_margin_raw S D lo hi σ x hm
  obtain ⟨hok,rr,hr,rfl⟩ := hx
  intro n
  exact frame_bank_margin N σ rr roles hr hg (Prepare.rest σ.b N.width) c n B D lo hi hB (hraw n)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
