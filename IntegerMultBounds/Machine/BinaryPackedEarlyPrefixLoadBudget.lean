import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixParityLoad
import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixNegativeLoad
import IntegerMultBounds.Machine.BinaryRepeatedOffsetLoadBudget

/-! Source-prefix generation, real interchange action and offset erasure retain
the uniform interchange exponent, with setup absorbed by actual suffix width. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyPrefixLoadBudget
open RadixRangePadding (volume)

 theorem parity_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (hs : Fin 5 → List Bool) (shape : Fin 4 → List Bool) (q b n K A G B : ℕ)
      (hb : 1≤b) (hbq : b+1≤q),
      0<K → 0<A → 0<G → 0<B →
      Counter.value (hs 3)=BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G →
      Counter.value (hs 4)=K → GrowingCounterData.Canonical (hs 3) → GrowingCounterData.Canonical (hs 4) →
      BinaryPackedEarlyPrefixBudget.allowance q b n≤B →
      (∀ i, Counter.value (shape i)=BinaryRadixRangePrepare.values (K*2^(n*q)*A) G B (n*b) i) →
      (∀ i, GrowingCounterData.Canonical (shape i)) →
      ((BinaryPackedEarlyPrefixParityLoad.cost hs shape q b n K A G B hb hbq : ℕ) : ℝ) ≤
        C*(volume (K*2^(n*q)*A) (2^(n*b)) G B : ℝ)*
          ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedOffsetOriginalBudget.uniform_bound
  let Cgen : ℝ := (BinaryPackedEarlyPrefixBudget.constant BinaryAddressOffset.constant+7 : ℕ)
  have hCgen : 0≤Cgen := by dsimp [Cgen]; positivity
  refine ⟨C+Cgen,by linarith,?_⟩
  intro hs shape q b n K A G B hb hbq hK hA hG hB hvL hvK hcL hcK hallow hv hc
  have hP : 0<K*2^(n*q)*A := by positivity
  have hL : 0<BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G := by unfold BinaryPackedEarlyPrefixAction.repeatLength; positivity
  have hi := hbound (K*2^(n*q)*A) G B (n*b) shape hP hG hB hv hc
  have hg := BinaryPackedEarlyPrefixBudget.parity_cost hs q b n (BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G) K B hL hK hvL hvK hcL hcK hallow
  have he := BinaryRepeatedOffsetLoadBudget.erase_bound (BinaryPackedEarlyPrefixParityLoad.packed q b n K A G hb hbq)
    (K*2^(n*q)*A) (n*b) G B
    (BinaryPackedEarlyPrefixAction.parity_length q b n K A G hb hbq) hP hG hB
  have hp : ((BinaryPackedEarlyPrefixParity.cost hs q b n (BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G) K+
      (2*(BinaryPackedEarlyPrefixParityLoad.packed q b n K A G hb hbq).length+3)+2 : ℕ) : ℝ) ≤
      Cgen*(volume (K*2^(n*q)*A) (2^(n*b)) G B : ℝ) := by
    dsimp only [Cgen]
    have hn : BinaryPackedEarlyPrefixParity.cost hs q b n (BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G) K+
        (2*(BinaryPackedEarlyPrefixParityLoad.packed q b n K A G hb hbq).length+3)+2 ≤
        (BinaryPackedEarlyPrefixBudget.constant BinaryAddressOffset.constant+7)*volume (K*2^(n*q)*A) (2^(n*b)) G B := by
      have hvgen : BinaryPackedEarlyPrefixBudget.volume q b n
          (BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G) K B=volume (K*2^(n*q)*A) (2^(n*b)) G B := by
        unfold BinaryPackedEarlyPrefixBudget.volume BinaryPackedEarlyPrefixAction.repeatLength volume
        ring
      rw [hvgen] at hg
      nlinarith only [hg,he]
    exact_mod_cast hn
  have hw : 1≤((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*b)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hCgen
    (by positivity : 0≤(volume (K*2^(n*q)*A) (2^(n*b)) G B : ℝ)))
  unfold BinaryPackedEarlyPrefixParityLoad.cost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hp ⊢
  nlinarith only [hi,hp,hm]

 theorem negative_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (hs : Fin 5 → List Bool) (Z : List Bool) (shape : Fin 4 → List Bool) (q b n K A G B : ℕ)
      (hb : 1≤b) (hbq : b+1≤q),
      0<K → 0<A → 0<G → 0<B →
      Counter.value (hs 3)=BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G →
      Counter.value (hs 4)=K → GrowingCounterData.Canonical (hs 3) → GrowingCounterData.Canonical (hs 4) →
      BinaryPackedEarlyPrefixBudget.allowance q b n≤B →
      (∀ i, Counter.value (shape i)=BinaryRadixRangePrepare.values (K*2^(n*q)*A) G B (n*b) i) →
      (∀ i, GrowingCounterData.Canonical (shape i)) →
      ((BinaryPackedEarlyPrefixNegativeLoad.cost hs Z shape q b n K A G B hb hbq : ℕ) : ℝ) ≤
        C*(volume (K*2^(n*q)*A) (2^(n*b)) G B : ℝ)*
          ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedOffsetOriginalBudget.uniform_bound
  let Cgen : ℝ := (BinaryPackedEarlyPrefixBudget.constant BinaryParityXorOffset.constant+7 : ℕ)
  have hCgen : 0≤Cgen := by dsimp [Cgen]; positivity
  refine ⟨C+Cgen,by linarith,?_⟩
  intro hs Z shape q b n K A G B hb hbq hK hA hG hB hvL hvK hcL hcK hallow hv hc
  have hP : 0<K*2^(n*q)*A := by positivity
  have hL : 0<BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G := by unfold BinaryPackedEarlyPrefixAction.repeatLength; positivity
  have hi := hbound (K*2^(n*q)*A) G B (n*b) shape hP hG hB hv hc
  have hg := BinaryPackedEarlyPrefixBudget.negative_cost hs q b n (BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G) K B hL hK hvL hvK hcL hcK hallow
  have he := BinaryRepeatedOffsetLoadBudget.erase_bound (BinaryPackedEarlyPrefixNegativeLoad.packed q b n K A G Z hb hbq)
    (K*2^(n*q)*A) (n*b) G B
    (BinaryPackedEarlyPrefixAction.negative_length q b n K A G Z hb hbq) hP hG hB
  have hp : ((BinaryPackedEarlyPrefixNegative.cost hs q b n (BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G) K+
      (2*(BinaryPackedEarlyPrefixNegativeLoad.packed q b n K A G Z hb hbq).length+3)+2 : ℕ) : ℝ) ≤
      Cgen*(volume (K*2^(n*q)*A) (2^(n*b)) G B : ℝ) := by
    dsimp only [Cgen]
    have hn : BinaryPackedEarlyPrefixNegative.cost hs q b n (BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G) K+
        (2*(BinaryPackedEarlyPrefixNegativeLoad.packed q b n K A G Z hb hbq).length+3)+2 ≤
        (BinaryPackedEarlyPrefixBudget.constant BinaryParityXorOffset.constant+7)*volume (K*2^(n*q)*A) (2^(n*b)) G B := by
      have hvgen : BinaryPackedEarlyPrefixBudget.volume q b n
          (BinaryPackedEarlyPrefixAction.repeatLength A (n*b) G) K B=volume (K*2^(n*q)*A) (2^(n*b)) G B := by
        unfold BinaryPackedEarlyPrefixBudget.volume BinaryPackedEarlyPrefixAction.repeatLength volume
        ring
      rw [hvgen] at hg
      nlinarith only [hg,he]
    exact_mod_cast hn
  have hw : 1≤((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*b)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hCgen
    (by positivity : 0≤(volume (K*2^(n*q)*A) (2^(n*b)) G B : ℝ)))
  unfold BinaryPackedEarlyPrefixNegativeLoad.cost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hp ⊢
  nlinarith only [hi,hp,hm]

end IntegerMultBounds.Machine.BinaryPackedEarlyPrefixLoadBudget
