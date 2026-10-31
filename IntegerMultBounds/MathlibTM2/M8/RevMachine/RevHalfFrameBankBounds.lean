module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfBankBounds

/-! Leaf-loop and retirement banks change data and counter words, while all
retained stack heads stay fixed. Their head offset from frame entry is at most one. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open Family (Frame)
open NodeBank (tapes)
open Routines (hdr)
open SharedBankStageInput (raw)
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

theorem frame_heads_close (σ : Frame (pcs N) capacity)
    (rr rr' : Tapes (tapes N) prime) (hg : RevNode.Good N σ.v rr) (hg' : RevNode.Good N σ.v rr')
    (c c' : Fin CommonBank.K → Option ℕ) :
    ∀ n j, (raw (σ.at rr c) n).head j-1 ≤ (raw (σ.at rr' c') n).head j ∧
      (raw (σ.at rr' c') n).head j ≤ (raw (σ.at rr c) n).head j+1 := by
  have hclose := CommonBank.bank_heads_close 1 (by decide) rr rr' (hdr σ.v) (hdr σ.v)
    σ.f σ.f σ.p σ.p σ.node σ.node σ.scalar σ.scalar c c' σ.st σ.st
    (by intro j; rw [RevNode.Good.heads N hg j,RevNode.Good.heads N hg' j]; omega)
    (by constructor <;> omega) (by intro j; constructor <;> omega)
    (by intro j; constructor <;> omega) (by intro j; constructor <;> omega)
  intro n j
  by_cases hj : j.val < CommonBank.count (tapes N)
  · simpa only [raw,hj,↓reduceDIte,Family.Frame.at,Nat.cast_one] using hclose ⟨j.val,hj⟩
  · simp only [raw,hj,↓reduceDIte]
    constructor <;> omega

/-- A frame's reserved margin transfers to every leaf or retirement bank. -/
theorem frame_bank_margin (σ : Frame (pcs N) capacity)
    (rr rr' : Tapes (tapes N) prime) (hg : RevNode.Good N σ.v rr) (hg' : RevNode.Good N σ.v rr')
    (c c' : Fin CommonBank.K → Option ℕ) (n B D : ℕ) (lo hi : ℤ)
    (hB : B+1 ≤ D*RecursiveInterchangeLayout.volume prime σ.v)
    (hmargin : ∀ j, lo+(D*RecursiveInterchangeLayout.volume prime σ.v : ℕ) ≤ (raw (σ.at rr c) n).head j ∧
      (raw (σ.at rr c) n).head j+(D*RecursiveInterchangeLayout.volume prime σ.v : ℕ) ≤ hi) :
    ∀ j, lo+B ≤ (raw (σ.at rr' c') n).head j ∧ (raw (σ.at rr' c') n).head j+B ≤ hi := by
  intro j
  have hm := hmargin j
  have hc := frame_heads_close N σ rr rr' hg hg' c c' n j
  omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
