module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkInterchangeLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedChunkInterchangeStock
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! Chronological chunk stages share one reserve: each stage restores scratch
and preserves the length of the only changed payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def chunkStageStockAllowance {T : ℕ} (t d : ℕ) (r : ChunkInterchangeStage T) : ℕ :=
  2*(21*(r.outerCount+1+r.blockWidth+d+d)+56)+
    t*(2*SwapMachineStock.reserve r.outerCount 1 r.blockWidth d d+2)+3*t+20

noncomputable def chunkStockAllowance {T : ℕ} (t d : ℕ) : List (ChunkInterchangeStage T) → ℕ
  | [] => 0
  | r::rs => max (chunkStageStockAllowance t d r) (chunkStockAllowance t d rs)

theorem chunkInterchangeLoop_exec_within {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hpay : ∀ k, hd k ≠ pay) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (a half par bits cnt work : Fin T) (d V : ℕ) (rs : List (ChunkInterchangeStage T))
    (hgen : ∀ r ∈ rs, ∀ k, [r.dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ r ∈ rs, ∀ k j, ι (reg (hd k)) ≠ r.dims j)
    (hmaster : ∀ r ∈ rs, ∀ k, r.dims k ≠ ι (reg pay))
    (hscratch : ∀ i ∈ [a,half,par,bits,cnt,work], i ≠ ι (reg pay))
    (hpositive : ∀ r ∈ rs, 0 < r.outerCount ∧ 0 < r.blockWidth)
    (hvolume : ∀ r ∈ rs, V = BinaryAdjacentWidthInterchange.volume r.outerCount (2^d) 1 (2^d) r.blockWidth)
    (xs : List Bool) (hlen : xs.length = V)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hdims : ∀ r ∈ rs, ∀ k, (S.R (r.dims k)).length = swapValues r.outerCount 1 r.blockWidth d d k)
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R (ι (reg pay)) = xs.map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (rs.map (fun r => generatedChunkInterchangeCost T t₀ r.outerCount r.blockWidth d
        (∑ j, (S.R (ι j)).length))).sum+1 ∧
      ExecWithin body (fun z c => mnSize c+z ≤ mnSize (mk v S)+depth+
        chunkStockAllowance T d rs) depth (chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work rs)
        (mk v S) n (mk v' {S with L := fun _ => [], R := (Function.update S.R (ι (reg pay))
          ((chunkStageBits d rs xs).map bitSymbol))}) := by
  induction rs generalizing xs v S with
  | nil =>
    refine ⟨v,1,rfl,by simp,?_⟩
    have he := ExecWithin.act (body := body) (Inv := fun z c =>
      mnSize c+z ≤ mnSize (mk v S)+depth+chunkStockAllowance (T := T) T d [])
      (d := depth) .done (mk v S) (by simp [chunkStockAllowance]) (by simp [Action.run,chunkStockAllowance])
    have hout : mk v S = mk v {S with L := fun _ => [], R := (Function.update S.R (ι (reg pay))
        ((chunkStageBits (T := T) d [] xs).map bitSymbol))} := by
      apply congrArg (mk v)
      refine Stacks.ext rfl rfl ?_ ?_
      · funext i; exact hL i
      · funext i
        by_cases hi : i = ι (reg pay)
        · subst i; simpa only [chunkStageBits,Function.update_self] using hsrc
        · exact (Function.update_of_ne hi _ _).symm
    exact (congrArg (fun f => ExecWithin body (fun z c =>
      mnSize c+z ≤ mnSize (mk v S)+depth+chunkStockAllowance (T := T) T d [])
      depth (.act .done) (mk v S) 1 f) hout).mp he
  | cons r rs ih =>
    have hr : r ∈ r::rs := by simp
    have htail : ∀ s ∈ rs, s ∈ r::rs := by intro s hs; simp [hs]
    have hlen' := hlen.trans (hvolume r hr)
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatedChunkInterchange_exec_within body hd pay hi hpay hQ ι hι hT
      r.dims a half par bits cnt work (hgen r hr) (hdisjoint r hr) r.outerCount r.blockWidth d
      (hpositive r hr).1 (hpositive r hr).2 xs hlen' v S hL hpriv (hdims r hr) hhdr hgenBlank hsrc hother depth
    let ys := swapList r.outerCount (2^d) 1 (2^d) r.blockWidth false xs
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
    have hfullStock : mnSize (mk v₁ M) = mnSize (mk v S) := by
      rw [mnSize_mk_registerBankStock,mnSize_mk_registerBankStock]
      change S.inp.length+S.out.length+registerBankStock M =
        S.inp.length+S.out.length+registerBankStock S
      apply congrArg (fun n => S.inp.length+S.out.length+n)
      rw [registerBankStock_eq_right_sum M (by intro i; rfl),
        registerBankStock_eq_right_sum S hL]
      apply Finset.sum_congr rfl
      intro i _
      by_cases he : i = ι (reg pay)
      · subst i
        simp only [M,Function.update_self,hsrc,List.length_map,hlenys,hlen]
      · exact congrArg List.length (hframe i he)
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih
      (by intro s hs; exact hgen s (htail s hs))
      (by intro s hs; exact hdisjoint s (htail s hs))
      (by intro s hs; exact hmaster s (htail s hs))
      (by intro s hs; exact hpositive s (htail s hs))
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
    · have hw₁ := he₁.mono (J := fun z c => mnSize c+z ≤
          mnSize (mk v S)+depth+chunkStockAllowance T d (r::rs)) (by
        intro z c hc
        have hm := Nat.le_max_left (chunkStageStockAllowance T d r) (chunkStockAllowance T d rs)
        change mnSize c+z ≤ mnSize (mk v S)+depth+
          max (chunkStageStockAllowance T d r) (chunkStockAllowance T d rs)
        have hc' : mnSize c+z ≤ mnSize (mk v S)+depth+chunkStageStockAllowance T d r := by
          simpa only [chunkStageStockAllowance,Nat.add_assoc] using hc
        exact hc'.trans (Nat.add_le_add_left hm _))
      have hw₂ := he₂.mono (J := fun z c => mnSize c+z ≤
          mnSize (mk v S)+depth+chunkStockAllowance T d (r::rs)) (by
        intro z c hc
        change mnSize c+z ≤ mnSize (mk v₁ M)+depth+chunkStockAllowance T d rs at hc
        rw [hfullStock] at hc
        have hm := Nat.le_max_right (chunkStageStockAllowance T d r) (chunkStockAllowance T d rs)
        change mnSize c+z ≤ mnSize (mk v S)+depth+
          max (chunkStageStockAllowance T d r) (chunkStockAllowance T d rs)
        exact hc.trans (Nat.add_le_add_left hm _))
      have he := ExecWithin.seq hw₁ hw₂
      have hout : mk v₂ {M with L := fun _ => [], R := (Function.update M.R (ι (reg pay))
          ((chunkStageBits d rs ys).map bitSymbol))} =
          mk v₂ {S with L := fun _ => [], R := (Function.update S.R (ι (reg pay))
          ((chunkStageBits d (r::rs) xs).map bitSymbol))} := by
        apply congrArg (mk v₂)
        refine Stacks.ext rfl rfl rfl ?_
        funext i
        by_cases hi : i = ι (reg pay)
        · subst i; simp only [Function.update_self,chunkStageBits,ys]
        · simp only [Function.update_of_ne hi,M]
      exact (congrArg (fun f => ExecWithin body (fun z c =>
        mnSize c+z ≤ mnSize (mk v S)+depth+chunkStockAllowance T d (r::rs))
        depth (chunkInterchangeLoop hd pay hi hQ ι hι hT a half par bits cnt work (r::rs))
        (mk v S) (n₁+n₂) f) hout).mp he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
