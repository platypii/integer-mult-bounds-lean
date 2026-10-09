import IntegerMultBounds.Machine.BinaryParityOffsetLoad
import IntegerMultBounds.Machine.BinarySelectedOffsetLoad
import IntegerMultBounds.Machine.BinaryCorrectionOffsetLoad
import IntegerMultBounds.Machine.BinaryParityXorOffsetLoad
import IntegerMultBounds.Machine.BinaryPackedOffsetOriginalBudget

/-! Original-input offset production, action and physical offset erasure
retain the certified interchange exponent. The producer's explicit allowance
is charged to actual suffix width, not treated as a free setup assumption. -/
namespace IntegerMultBounds.Machine.BinaryRepeatedOffsetLoadBudget
open RadixRangePadding (volume)

 theorem erase_bound (V : List Bool) (P w G B : ℕ)
    (hV : V.length=BinaryPackedOffsetData.rows P w G*w)
    (hP : 0<P) (hG : 0<G) (hB : 0<B) :
    2*V.length+3+2≤7*volume P (2^w) G B := by
  have hw : w≤2^w := (Nat.le_succ w).trans Nat.lt_two_pow_self
  have hlen : V.length≤volume P (2^w) G B := by
    rw [hV]
    have h0 := Nat.mul_le_mul_left (BinaryPackedOffsetData.rows P w G) hw
    have h1 := Nat.le_mul_of_pos_right (BinaryPackedOffsetData.rows P w G*2^w) hB
    exact h0.trans h1
  have hv : 1≤volume P (2^w) G B := Nat.succ_le_of_lt (by unfold volume; positivity)
  omega

 theorem parity_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (hs : Fin 6 → List Bool) (shape : Fin 4 → List Bool) (q b n P H L B : ℕ)
      (hb : 1≤b) (hbq : b+1≤q),
      0<P → 0<H → 0<L → 0<B →
      Counter.value (hs 5)=L → GrowingCounterData.Canonical (hs 5) →
      BinaryAddressOffset.allowance q b n≤B →
      (∀ i, Counter.value (shape i)=BinaryRadixRangePrepare.values P (H*2^(n*q)*L) B (n*b) i) →
      (∀ i, GrowingCounterData.Canonical (shape i)) →
      ((BinaryParityOffsetLoad.cost hs shape q b n P H L B hb hbq : ℕ) : ℝ) ≤
        C*(volume P (2^(n*b)) (H*2^(n*q)*L) B : ℝ)*
          ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedOffsetOriginalBudget.uniform_bound
  let K : ℝ := (BinaryAddressOffsetRepeatConstructBudget.constant+7 : ℕ)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨C+K,by linarith,?_⟩
  intro hs shape q b n P H L B hb hbq hP hH hL hB hvL hcL hallow hv hc
  have hG : 0<H*2^(n*q)*L := by positivity
  have hi := hbound P (H*2^(n*q)*L) B (n*b) shape hP hG hB hv hc
  have hg := BinaryAddressOffsetRepeatConstructBudget.cost_volume hs q b n P H L B hP hH hL hvL hcL hallow
  have he := erase_bound (BinaryParityOffsetLoad.packed q b n P H L hb hbq)
    P (n*b) (H*2^(n*q)*L) B
    (BinaryAddressOffsetRepeatCoordinates.word_length q b n P H L hb hbq) hP hG hB
  have hp : ((BinaryAddressOffsetRepeatConstruct.cost hs q b n P H L+
      (2*(BinaryParityOffsetLoad.packed q b n P H L hb hbq).length+3)+2 : ℕ) : ℝ) ≤
      K*(volume P (2^(n*b)) (H*2^(n*q)*L) B : ℝ) := by
    dsimp only [K]
    have hn : BinaryAddressOffsetRepeatConstruct.cost hs q b n P H L+
        (2*(BinaryParityOffsetLoad.packed q b n P H L hb hbq).length+3)+2 ≤
        (BinaryAddressOffsetRepeatConstructBudget.constant+7)*volume P (2^(n*b)) (H*2^(n*q)*L) B := by
      change BinaryAddressOffsetRepeatConstruct.cost hs q b n P H L≤
        BinaryAddressOffsetRepeatConstructBudget.constant*volume P (2^(n*b)) (H*2^(n*q)*L) B at hg
      nlinarith only [hg,he]
    exact_mod_cast hn
  have hw : 1≤((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*b)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hK
    (by positivity : 0≤(volume P (2^(n*b)) (H*2^(n*q)*L) B : ℝ)))
  unfold BinaryParityOffsetLoad.cost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hp ⊢
  nlinarith only [hi,hp,hm]

 theorem selected_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (hs : Fin 6 → List Bool) (Z : List Bool) (shape : Fin 4 → List Bool) (q b n P H L B : ℕ)
      (hb : 1≤b) (hbq : b+1≤q),
      0<P → 0<H → 0<L → 0<B →
      Counter.value (hs 5)=L → GrowingCounterData.Canonical (hs 5) →
      BinarySelectedOffset.allowance q b n≤B →
      (∀ i, Counter.value (shape i)=BinaryRadixRangePrepare.values P (H*2^(n*b)*L) B (n*q) i) →
      (∀ i, GrowingCounterData.Canonical (shape i)) →
      ((BinarySelectedOffsetLoad.cost hs Z shape q b n P H L B hb hbq : ℕ) : ℝ) ≤
        C*(volume P (2^(n*q)) (H*2^(n*b)*L) B : ℝ)*
          ((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedOffsetOriginalBudget.uniform_bound
  let K : ℝ := (BinarySelectedOffsetRepeatBudget.constant+7 : ℕ)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨C+K,by linarith,?_⟩
  intro hs Z shape q b n P H L B hb hbq hP hH hL hB hvL hcL hallow hv hc
  have hG : 0<H*2^(n*b)*L := by positivity
  have hi := hbound P (H*2^(n*b)*L) B (n*q) shape hP hG hB hv hc
  have hg := BinarySelectedOffsetRepeatBudget.cost_volume hs q b n P H L B hP hH hL hvL hcL hallow
  have he := erase_bound (BinarySelectedOffsetLoad.packed q b n P H L Z hb hbq)
    P (n*q) (H*2^(n*b)*L) B
    (BinarySelectedOffsetRepeatCoordinates.word_length q b n P H L Z hb hbq) hP hG hB
  have hp : ((BinarySelectedOffsetRepeatConstruct.cost hs q b n P H L+
      (2*(BinarySelectedOffsetLoad.packed q b n P H L Z hb hbq).length+3)+2 : ℕ) : ℝ) ≤
      K*(volume P (2^(n*q)) (H*2^(n*b)*L) B : ℝ) := by
    dsimp only [K]
    have hn : BinarySelectedOffsetRepeatConstruct.cost hs q b n P H L+
        (2*(BinarySelectedOffsetLoad.packed q b n P H L Z hb hbq).length+3)+2 ≤
        (BinarySelectedOffsetRepeatBudget.constant+7)*volume P (2^(n*q)) (H*2^(n*b)*L) B := by
      change BinarySelectedOffsetRepeatConstruct.cost hs q b n P H L≤
        BinarySelectedOffsetRepeatBudget.constant*volume P (2^(n*q)) (H*2^(n*b)*L) B at hg
      nlinarith only [hg,he]
    exact_mod_cast hn
  have hw : 1≤((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*q)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hK
    (by positivity : 0≤(volume P (2^(n*q)) (H*2^(n*b)*L) B : ℝ)))
  unfold BinarySelectedOffsetLoad.cost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hp ⊢
  nlinarith only [hi,hp,hm]

 theorem correction_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (hs : Fin 6 → List Bool) (Z : List Bool) (shape : Fin 4 → List Bool) (q b n P H L B : ℕ)
      (hb : 1≤b) (hbq : b+1≤q),
      Z.length=n → 0<P → 0<H → 0<L → 0<B →
      Counter.value (hs 5)=L → GrowingCounterData.Canonical (hs 5) →
      BinaryCorrectionOffset.allowance q b n≤B →
      (∀ i, Counter.value (shape i)=BinaryRadixRangePrepare.values P (H*2^(n*b)*L) B (n*q) i) →
      (∀ i, GrowingCounterData.Canonical (shape i)) →
      ((BinaryCorrectionOffsetLoad.cost hs Z shape q b n P H L B hb hbq : ℕ) : ℝ) ≤
        C*(volume P (2^(n*q)) (H*2^(n*b)*L) B : ℝ)*
          ((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedOffsetOriginalBudget.uniform_bound
  let K : ℝ := (BinaryCorrectionOffsetRepeatBudget.constant+7 : ℕ)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨C+K,by linarith,?_⟩
  intro hs Z shape q b n P H L B hb hbq hZ hP hH hL hB hvL hcL hallow hv hc
  have hG : 0<H*2^(n*b)*L := by positivity
  have hi := hbound P (H*2^(n*b)*L) B (n*q) shape hP hG hB hv hc
  have hg := BinaryCorrectionOffsetRepeatBudget.cost_volume hs q b n P H L B hP hH hL hvL hcL hallow
  have he := erase_bound (BinaryCorrectionOffsetLoad.packed q b n P H L Z hb hbq)
    P (n*q) (H*2^(n*b)*L) B
    (BinaryCorrectionOffsetRepeatCoordinates.word_length q b n P H L Z hb hbq hZ) hP hG hB
  have hp : ((BinaryCorrectionOffsetRepeatConstruct.cost hs q b n P H L+
      (2*(BinaryCorrectionOffsetLoad.packed q b n P H L Z hb hbq).length+3)+2 : ℕ) : ℝ) ≤
      K*(volume P (2^(n*q)) (H*2^(n*b)*L) B : ℝ) := by
    dsimp only [K]
    have hn : BinaryCorrectionOffsetRepeatConstruct.cost hs q b n P H L+
        (2*(BinaryCorrectionOffsetLoad.packed q b n P H L Z hb hbq).length+3)+2 ≤
        (BinaryCorrectionOffsetRepeatBudget.constant+7)*volume P (2^(n*q)) (H*2^(n*b)*L) B := by
      change BinaryCorrectionOffsetRepeatConstruct.cost hs q b n P H L≤
        BinaryCorrectionOffsetRepeatBudget.constant*volume P (2^(n*q)) (H*2^(n*b)*L) B at hg
      nlinarith only [hg,he]
    exact_mod_cast hn
  have hw : 1≤((max 1 (n*q) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*q)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hK
    (by positivity : 0≤(volume P (2^(n*q)) (H*2^(n*b)*L) B : ℝ)))
  unfold BinaryCorrectionOffsetLoad.cost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hp ⊢
  nlinarith only [hi,hp,hm]

 theorem parity_xor_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (hs : Fin 6 → List Bool) (Z : List Bool) (shape : Fin 4 → List Bool) (q b n P H L B : ℕ)
      (hb : 1≤b) (hbq : b+1≤q),
      0<P → 0<H → 0<L → 0<B →
      Counter.value (hs 5)=L → GrowingCounterData.Canonical (hs 5) →
      BinaryParityXorOffset.allowance q b n≤B →
      (∀ i, Counter.value (shape i)=BinaryRadixRangePrepare.values P (H*2^(n*q)*L) B (n*b) i) →
      (∀ i, GrowingCounterData.Canonical (shape i)) →
      ((BinaryParityXorOffsetLoad.cost hs Z shape q b n P H L B hb hbq : ℕ) : ℝ) ≤
        C*(volume P (2^(n*b)) (H*2^(n*q)*L) B : ℝ)*
          ((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryPackedOffsetOriginalBudget.uniform_bound
  let K : ℝ := (BinaryParityXorOffsetRepeatBudget.constant+7 : ℕ)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨C+K,by linarith,?_⟩
  intro hs Z shape q b n P H L B hb hbq hP hH hL hB hvL hcL hallow hv hc
  have hG : 0<H*2^(n*q)*L := by positivity
  have hi := hbound P (H*2^(n*q)*L) B (n*b) shape hP hG hB hv hc
  have hg := BinaryParityXorOffsetRepeatBudget.cost_volume hs q b n P H L B hP hH hL hvL hcL hallow
  have he := erase_bound (BinaryParityXorOffsetLoad.packed q b n P H L Z hb hbq)
    P (n*b) (H*2^(n*q)*L) B
    (BinaryParityXorOffsetRepeatCoordinates.word_length q b n P H L Z hb hbq) hP hG hB
  have hp : ((BinaryParityXorOffsetRepeatConstruct.cost hs q b n P H L+
      (2*(BinaryParityXorOffsetLoad.packed q b n P H L Z hb hbq).length+3)+2 : ℕ) : ℝ) ≤
      K*(volume P (2^(n*b)) (H*2^(n*q)*L) B : ℝ) := by
    dsimp only [K]
    have hn : BinaryParityXorOffsetRepeatConstruct.cost hs q b n P H L+
        (2*(BinaryParityXorOffsetLoad.packed q b n P H L Z hb hbq).length+3)+2 ≤
        (BinaryParityXorOffsetRepeatBudget.constant+7)*volume P (2^(n*b)) (H*2^(n*q)*L) B := by
      change BinaryParityXorOffsetRepeatConstruct.cost hs q b n P H L≤
        BinaryParityXorOffsetRepeatBudget.constant*volume P (2^(n*b)) (H*2^(n*q)*L) B at hg
      nlinarith only [hg,he]
    exact_mod_cast hn
  have hw : 1≤((max 1 (n*b) : ℕ) : ℝ)^Parameters.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 (n*b)) Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hK
    (by positivity : 0≤(volume P (2^(n*b)) (H*2^(n*q)*L) B : ℝ)))
  unfold BinaryParityXorOffsetLoad.cost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hp ⊢
  nlinarith only [hi,hp,hm]

end IntegerMultBounds.Machine.BinaryRepeatedOffsetLoadBudget
