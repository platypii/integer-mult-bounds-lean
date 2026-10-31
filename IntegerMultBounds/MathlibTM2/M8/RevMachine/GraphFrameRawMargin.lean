module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphFrameVolumeWithin
public import IntegerMultBounds.Machine.RawHeadMargin

/-! The finite graph bank includes blank private tapes. Its entry reserve
therefore transfers to every block's raw padding without additional cost. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
open IntegerMultBounds.Machine Graph
open SharedBankStageInput (raw)
noncomputable section
variable {Seg Call : Type} {t a k : ℕ} {pieces : List (Piece Seg Call)}
  {capacity : Fintype.card (PC pieces.length) ≤ 2^k} {stack : Fin t} {ht : 0 < t}
  {impl : Implementation t a k Seg Call} {m W : ℕ} {rank : Call → ℕ}
  (S : Inv pieces capacity stack impl m W rank)

theorem volume_margin_raw (D : ℕ) (lo hi : ℤ) (σ : S.Shape) (x : Tapes t a)
    (hm : VolumeMargin (ht := ht) S D lo hi σ x) :
    ∀ n j, lo+(D*S.vol σ : ℕ) ≤ (raw x n).head j ∧
      (raw x n).head j+(D*S.vol σ : ℕ) ≤ hi := by
  apply SharedBankStageInput.raw_margin_of_padding x ?_ hm
  have hp := Finset.single_le_sum
    (fun pc (_ : pc ∈ Finset.univ) => Nat.zero_le (block pieces capacity stack ht impl pc).tapes)
    (Finset.mem_univ (.prepare : PC pieces.length))
  have hc := SharedBankFamily.common_le (block pieces capacity stack ht impl .prepare)
  change t < t+∑ pc, (block pieces capacity stack ht impl pc).tapes
  omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
