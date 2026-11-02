module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedChunkInterchange
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRectangularChunkLayout

/-! Physical balanced rectangular schedules. Every later stage's readiness
follows from the exact frame of the preceding execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

structure BalancedChunkInterchangeStage (T : ℕ) where
  dims : Fin 5 → Fin T
  outerCount : ℕ
  blockWidth : ℕ
  leftBits : ℕ
  rightBits : ℕ

def BalancedChunkInterchangeStage.shape {T : ℕ}
    (r : BalancedChunkInterchangeStage T) : RectangularChunkSwap :=
  ⟨r.outerCount,2^r.leftBits,2^r.rightBits,r.blockWidth⟩

def balancedChunkStageBits {T : ℕ} :
    List (BalancedChunkInterchangeStage T) → List Bool → List Bool
  | [],xs => xs
  | r::rs,xs => balancedChunkStageBits rs
      (swapList r.outerCount (2^r.leftBits) 1 (2^r.rightBits) r.blockWidth false xs)

theorem balancedChunkStageBits_eq {T : ℕ}
    (rs : List (BalancedChunkInterchangeStage T)) (xs : List Bool) :
    balancedChunkStageBits rs xs =
      runRectangularChunkSwaps false (rs.map BalancedChunkInterchangeStage.shape) xs := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih => exact ih _

/-- Matching the structural schedule suffices to identify the entire output;
no individual address certificates are required. -/
theorem balancedChunkStageBits_words {T K W : ℕ}
    (rs : List (BalancedChunkInterchangeStage T)) (ns : List ℕ)
    (hshape : rs.map BalancedChunkInterchangeStage.shape = rectangularChunkSwaps K W ns)
    (f : Fin ns.prod → Fin K → Fin W → Bool) :
    balancedChunkStageBits rs (replicaKeyWords f) = keyReplicaWords f := by
  rw [balancedChunkStageBits_eq,hshape]
  exact runRectangularChunkSwaps_words K W ns false f

theorem balancedChunkStageBits_inverse_words {T K W : ℕ}
    (rs : List (BalancedChunkInterchangeStage T)) (ns : List ℕ)
    (hshape : rs.map BalancedChunkInterchangeStage.shape =
      (rectangularChunkSwaps K W ns).reverse.map RectangularChunkSwap.inverse)
    (f : Fin ns.prod → Fin K → Fin W → Bool) :
    balancedChunkStageBits rs (keyReplicaWords f) = replicaKeyWords f := by
  rw [balancedChunkStageBits_eq,hshape]
  exact runRectangularChunkSwaps_inverse_words K W ns false f

noncomputable def balancedChunkInterchangeLoop {t₀ T Q K : ℕ} {U P : Type}
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (a half par bits cnt work : Fin T) : List (BalancedChunkInterchangeStage T) → Pr P T Q (prime+K) U
  | [] => .act .done
  | r::rs => .seq (generatedChunkInterchange hd pay hi hQ ι hι hT r.dims a half par bits cnt work)
      (balancedChunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs)

/-- All later stage readiness is derived from the preceding actual execution.
The only supplied stage data are dimension values and a common payload volume. -/
theorem balancedChunkInterchangeLoop_exec {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hpay : ∀ k, hd k ≠ pay) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (a half par bits cnt work : Fin T) (V : ℕ) (rs : List (BalancedChunkInterchangeStage T))
    (hgen : ∀ r ∈ rs, ∀ k, [r.dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ r ∈ rs, ∀ k j, ι (reg (hd k)) ≠ r.dims j)
    (hmaster : ∀ r ∈ rs, ∀ k, r.dims k ≠ ι (reg pay))
    (hscratch : ∀ i ∈ [a,half,par,bits,cnt,work], i ≠ ι (reg pay))
    (hpositive : ∀ r ∈ rs, 0 < r.outerCount ∧ 0 < r.blockWidth)
    (hbalance : ∀ r ∈ rs, r.leftBits ≤ r.rightBits+1 ∧ r.rightBits ≤ r.leftBits+1)
    (hvolume : ∀ r ∈ rs, V = BinaryAdjacentWidthInterchange.volume r.outerCount (2^r.leftBits) 1 (2^r.rightBits) r.blockWidth)
    (xs : List Bool) (hlen : xs.length = V)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hdims : ∀ r ∈ rs, ∀ k, (S.R (r.dims k)).length = swapValues r.outerCount 1 r.blockWidth r.leftBits r.rightBits k)
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R (ι (reg pay)) = xs.map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (rs.map (fun r => generatedBalancedChunkInterchangeCost T t₀ r.outerCount r.blockWidth r.leftBits r.rightBits
        (∑ j, (S.R (ι j)).length))).sum+1 ∧
      Exec body (balancedChunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs)
        (mk v S) n (mk v' {S with L := fun _ => [], R := (Function.update S.R (ι (reg pay))
          ((balancedChunkStageBits rs xs).map bitSymbol))}) := by
  induction rs generalizing xs v S with
  | nil =>
    refine ⟨v,1,rfl,by simp,?_⟩
    refine (Exec.act (body := body) .done (mk v S)).cast rfl ?_
    apply congrArg (mk v)
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i; exact hL i
    · funext i
      by_cases hi : i = ι (reg pay)
      · subst i; simpa only [balancedChunkStageBits,Function.update_self] using hsrc
      · exact (Function.update_of_ne hi _ _).symm
  | cons r rs ih =>
    have hr : r ∈ r::rs := by simp
    have htail : ∀ s ∈ rs, s ∈ r::rs := by intro s hs; simp [hs]
    have hlen' := hlen.trans (hvolume r hr)
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatedBalancedChunkInterchange_exec body hd pay hi hpay hQ ι hι hT
      r.dims a half par bits cnt work (hgen r hr) (hdisjoint r hr) r.outerCount r.blockWidth r.leftBits r.rightBits
      (hbalance r hr).1 (hbalance r hr).2 (hpositive r hr).1 (hpositive r hr).2 xs hlen' v S hL hpriv (hdims r hr) hhdr hgenBlank hsrc hother
    let ys := swapList r.outerCount (2^r.leftBits) 1 (2^r.rightBits) r.blockWidth false xs
    let M : Stacks T (prime+K) := {S with L := fun _ => [], R := Function.update S.R (ι (reg pay)) (ys.map bitSymbol)}
    have hframe (i : Fin T) (hi : i ≠ ι (reg pay)) : M.R i = S.R i := Function.update_of_ne hi _ _
    have hlenys : ys.length = V := (swapList_bitSymbols_length xs hlen').trans hlen
    have hstock : (∑ j, (M.R (ι j)).length) = ∑ j, (S.R (ι j)).length := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases he : ι j = ι (reg pay)
      · rw [he]
        simp only [M,Function.update_self,hsrc,List.length_map,hlenys,hlen]
      · rw [hframe _ he]
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih
      (by intro s hs; exact hgen s (htail s hs))
      (by intro s hs; exact hdisjoint s (htail s hs))
      (by intro s hs; exact hmaster s (htail s hs))
      (by intro s hs; exact hpositive s (htail s hs))
      (by intro s hs; exact hbalance s (htail s hs))
      (by intro s hs; exact hvolume s (htail s hs)) ys hlenys v₁ M
      (by intro i; rfl)
      (by
        intro j hj
        rw [hframe]
        · exact hpriv j hj
        · intro he
          have hh := congrArg Fin.val (hι he)
          change j.val = pay.val at hh
          have hp := pay.isLt
          omega)
      (by intro s hs k; rw [hframe _ (hmaster s (htail s hs) k)]; exact hdims s (htail s hs) k)
      (by
        intro k
        rw [hframe]
        · exact hhdr k
        · intro he; exact hpay k (BinaryInterchangeRun.slot_injective (hι he)))
      (by intro i hi; rw [hframe _ (hscratch i hi)]; exact hgenBlank i hi)
      (by simp only [M,Function.update_self])
      (by
        intro i hip hheads s hs
        rw [hframe] at hs
        · exact hother i hip hheads s hs
        · intro he; exact hip (BinaryInterchangeRun.slot_injective (hι he)))
    rw [hstock] at hn₂
    refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · refine (Exec.seq he₁ he₂).cast rfl ?_
      apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = ι (reg pay)
      · subst i; simp only [Function.update_self,balancedChunkStageBits,ys]
      · simp only [Function.update_of_ne hi,M]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
