module

public import IntegerMultBounds.MathlibTM2.Cover.LabelRoute
import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevBudget

/-! One circuit for a rational label route at every positive width. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelFactorization
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Stage2Machine.Straight (words)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open ActualAffineScaling (modulus)
open IntegerMultBounds.Swap.Modular
open IntegerMultBounds.Swap.LowerTriangular (Factorization)
variable {T m : ℕ} [M8.Machine.Net]

private theorem overhead (ps : List (LabelSchedule.Pair m)) :
    ∃ C : ℕ, ∀ (v : Descriptor) (w B : ℕ), 0 < m → 0 < w → 0 < B →
      v.beforeH = B*prime^(m*(w*m)) → v.Positive →
      LabelRoute.pivotCost v w ps + 2 ≤
        C * volume prime v + (m-1)*LeafCore.coreCost (volume prime v) (w*m) := by
  let K := 2 * RecursiveChildQuotientsConstant.cost m + LabelSchedule.countCost ps + 110017
  refine ⟨K + 110011 + (m-1)*3808274, ?_⟩
  intro v w B hm hw hb hv hp
  let V := volume prime v
  have hV : 0 < V := RecursiveAffinePrepare.volume_positive prime_prime.two_le v hp
  have hpow := Nat.lt_pow_self (n := m*(w*m)) prime_prime.one_lt
  have hcol : w*m ≤ V := calc
    w*m ≤ m*(w*m) := Nat.le_mul_of_pos_left _ hm
    _ ≤ prime^(m*(w*m)) := hpow.le
    _ ≤ v.beforeH := hv ▸ Nat.le_mul_of_pos_left _ hb
    _ ≤ V := (LabelPrepare.factors v hV).1
  have hwV := (Nat.le_mul_of_pos_right w hm).trans hcol
  have hmV := (Nat.le_mul_of_pos_left m hw).trans hcol
  have h₁ := LabelWidth.widen_cost v w m
  have h₂ := LabelWidth.narrow_cost v w m hm
  have hK := Nat.le_mul_of_pos_right K hV
  dsimp [K] at hK ⊢
  unfold LabelRoute.pivotCost
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hK ⊢
  dsimp [V] at *
  omega

/-- The circuit and its linear overhead depend only on the rational factorization.
Each of the at most `m-1` supplier calls exchanges columns of width `w*m`. -/
theorem realizes (hk : 2 ≤ m*m) (io : Fin T) (σ : Matrix (Fin m) (Fin m) ℚ)
    (hu : IsUnit σ) (F : Factorization Finset.univ Finset.univ σ.transpose)
    (hd : ∀ d ∈ factorizationDenominators F, d < prime)
    (hs₁ : ∀ op ∈ LabelAddress.pass F.E₁, FlatCoordinateSchedule.Supported op)
    (hs₂ : ∀ op ∈ LabelAddress.pass F.E₂, FlatCoordinateSchedule.Supported op) :
    ∃ (M : Graph.Block (T+24) prime) (C : ℕ), Blocks.Leading M ∧
      ∀ (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
        v.beforeH = B*prime^(m*(w*m)) → v.Positive →
        ∀ (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2),
        roles.head io = 0 → roles.tape io = sourceWord x →
        let d := words (LabelSchedule.base v w)
        ∃ y : Fin (volume prime v) → ZMod 2,
          LabelPermutation.Transport v B w (fun g => g * reduce (modulus w) σ) (ext x) (ext y) ∧
          let cost := C * volume prime v + (m-1)*LeafCore.coreCost (volume prime v) (w*m)
          GraphContract.Runs M (LabelCall.bank roles v d)
            (LabelCall.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0) v d)
            cost ∧ ∀ width : ℕ, w*m ≤ width →
              (cost : ℝ) ≤ ((C : ℝ) + ((m-1 : ℕ) : ℝ) * |LeafCore.C| *
                (width : ℝ)^M8.Machine.BudgetBound.tau) * volume prime v := by
  have hlen : F.L.length = m := by
    rw [IntegerMultBounds.Swap.PivotRank.length_eq_rank F, Matrix.rank_transpose,
      Matrix.rank_of_isUnit σ hu, Fintype.card_fin]
  obtain ⟨π, hπ⟩ := Route.exists_perm F.L F.nodup₁ F.nodup₂ hlen
  obtain ⟨ps, _, hr⟩ := LabelRoute.realizes hk io π F.E₁ F.E₂ hs₁ hs₂ F.lower₁ F.lower₂
  obtain ⟨C, hc⟩ := overhead ps
  refine ⟨Blocks.seqB (Blocks.seqB (LabelProgram.program io (LabelProgram.pass hk F.E₂ hs₂))
    (LabelRoute.pivot io ps)) (LabelProgram.program io (LabelProgram.pass hk F.E₁ hs₁)),
    LabelProgram.coefficient (LabelProgram.pass hk F.E₂ hs₂) + C +
    LabelProgram.coefficient (LabelProgram.pass hk F.E₁ hs₁), Blocks.seq_leading _ _, ?_⟩
  intro v w B hw hb hv hp roles x hh hx
  obtain ⟨_, _, _, _, _, i₁, i₁', i₂, i₂', heq⟩ := reduce_factorization_of_prime F prime_prime hd w
  obtain ⟨y, hy, h⟩ := hr v w B hw hb hv hp (isUnit_iff_exists.mpr ⟨_, i₁, i₁'⟩)
    (isUnit_iff_exists.mpr ⟨_, i₂, i₂'⟩) (reduce (modulus w) σ) F.L (F.nodup₁.of_map _) hπ heq roles x hh hx
  have hm : 0 < m := by by_contra! h; interval_cases m; contradiction
  have := hc v w B hm hw hb hv hp
  refine ⟨y, hy, Blocks.runs_mono h ?_, ?_⟩
  · simp only [Nat.add_mul]
    omega
  · intro width fits
    have col : max 1 (w*m) ≤ width := max_le ((Nat.mul_pos hw hm).trans_le fits) fits
    have sized := RevBudget.coreCost_le (volume prime v) (w*m)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (show ((max 1 (w*m) : ℕ) : ℝ) ≤ width by exact_mod_cast col)
        M8.Machine.BudgetBound.exponent_range.1.le)
    push_cast
    calc
      _ ≤ _ + ((m-1 : ℕ) : ℝ)*(|LeafCore.C| * volume prime v *
          (width : ℝ)^M8.Machine.BudgetBound.tau) := add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left sized (Nat.cast_nonneg _))
      _ = _ := by ring

end
end IntegerMultBounds.MathlibTM2.Cover.LabelFactorization
