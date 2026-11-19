module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGeneratedSignedPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout

/-! Charge a terminal signed pass and its enclosing good records on one descriptor volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine RecursiveInterchangeLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- The recursive adapters contribute their linear overheads. Only the terminal
rank width occurs in the width-dependent residual term. -/
theorem signedPass_chain_cost [M8.Machine.Net] {ι : Type*} (U : Type)
    (r d T : ℕ) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) (gap overhead : ι → ℕ)
    (time : List ι → Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor prime (v.width-gap i) (gap i) v) + overhead i * volume prime v)
    (records : List ι) (v : Descriptor) (fits : (records.map gap).sum ≤ v.width)
    (B width swaps shears C : ℕ) :
    let child := rankDescriptor prime (v.width-(records.map gap).sum) (records.map gap).sum v
    let w := child.width/r-1
    let W := prime^(2*(child.width%r))*child.between*child.afterD
    r ≤ child.width → width ≤ prime^child.width →
    SignedPassCharge U r d T child w W (Nat.size (prime^(w+1))) (Nat.size W)
      B width swaps shears C (time [] child) →
    let V := (volume prime v : ℝ)
    (time records v : ℝ) ≤ (C+(records.map overhead).sum : ℕ)*V +
      (6 + ((swaps : ℝ)*((3808275 + M8.RevMachine.LeafCore.C) *
        ((child.width : ℝ)^M8.Machine.BudgetBound.tau / (r : ℝ)^M8.Machine.BudgetBound.tau)) + shears)) *
        (((prime-1 : ℕ) : ℝ)/prime*V) := by
  intro child w W rankFits widthBound charge V
  have dim := Fintype.card_congr e
  simp only [Fintype.card_sum,Fintype.card_fin] at dim
  have rankPos : 0 < r := by omega
  have atom : w+1 = child.width/r := Nat.sub_add_cancel (Nat.div_pos rankFits rankPos)
  have split : child.width = r*(w+1)+child.width%r := by rw [atom,Nat.div_add_mod]
  have terminal := charge.quotient (child.width%r) split (Nat.mod_lt _ rankPos)
    (signedPassVolume_eq_descriptor child e w (child.width%r) split) rfl rfl widthBound
  have sameVolume : volume prime child = volume prime v :=
    rankDescriptor_volume v (Nat.sub_add_cancel fits).symm
  rw [sameVolume] at terminal
  have chain := rankDescriptor_chain_time gap overhead time step records v fits
  calc
    (time records v : ℝ) ≤ ((time [] child + (records.map overhead).sum * volume prime v : ℕ) : ℝ) :=
      Nat.cast_le.mpr chain
    _ = (time [] child : ℝ) + ((records.map overhead).sum : ℝ)*V := by push_cast; rfl
    _ ≤ _ := by push_cast; dsimp only [V] at *; linarith only [terminal]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
