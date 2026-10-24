module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveRotations
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveSwaps

/-!
# Shared prepared state for the complete selective host schedule

Each of the five offset types has a retained descriptor bank. Two retained
interchange banks hold their canonical headers. Every pass restores this metadata,
so only the record stream changes between passes. Preparing and finally clearing
these banks remain explicit setup obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

structure SelectiveHost (T : ℕ) where
  cf : Fin 5 → Fin T
  cb : Off → PatternReg 2 → Fin T
  src : Fin T
  dst : Fin 2 → Fin T
  aux : Fin 2 → Fin T
  out : Fin T
  ctr : Fin T
  tmp : Fin T
  cnt : Fin T
  ctmp : Fin T
  swaps : Fin 2 → Fin (swapT 6) → Fin T

namespace SelectiveHost

variable {T : ℕ} (H : SelectiveHost T)

structure Valid : Prop where
  callback : ∀ off, HeaderBank H.cf (H.cb off) (selectiveTgt off)
  move : ∀ off, MoveRegs (fun k => (∃ f, H.cf f = k) ∨ (∃ r, H.cb off r = k))
    H.src H.dst H.aux H.out H.ctr H.tmp H.cnt H.ctmp
  swap_inj : ∀ c, Function.Injective (H.swaps c)
  swap_src : ∀ c j, H.swaps c j ≠ H.src
  swap_tmp : ∀ c j, H.swaps c j ≠ H.tmp

theorem Valid.tmp_src (V : H.Valid) : H.tmp ≠ H.src := by
  have hn := (List.nodup_cons.mp (V.move .A).regs).1
  intro he
  exact hn (by simp [he])

theorem Valid.cb_src (V : H.Valid) (off : Off) (r : PatternReg 2) : H.cb off r ≠ H.src := by
  intro he
  have h := (V.move off).idx H.src (Or.inr ⟨r, he⟩)
  simp at h

theorem Valid.cf_src (V : H.Valid) (f : Fin 5) : H.cf f ≠ H.src := by
  intro he
  have h := (V.move .A).idx H.src (Or.inl ⟨f, he⟩)
  simp at h

end SelectiveHost

variable {T K : ℕ} (p : Par) (X : ℕ) (H : SelectiveHost T)
  (hG : 0 < p.G) (hK : 0 < p.K) (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

structure SelectivePrepared (B M : ℕ) (hs : Fin 2 → Fin 5 → List Bool)
    (S : Stacks T (prime + K)) : Prop where
  left : ∀ j, S.L j = []
  ctr : (S.R H.ctr).length = B
  cnt : (S.R H.cnt).length = M
  tmp : S.R H.tmp = []
  ctmp : S.R H.ctmp = []
  out : S.R H.out = []
  dst : ∀ d, S.R (H.dst d) = []
  aux : ∀ d, S.R (H.aux d) = []
  inv : ∀ off, HeaderInv (selectiveLen p X) H.cf (H.cb off)
    (selectivePatterns p X hG hK active s off) S.R 0
  pay : ∀ c, S.R (H.swaps c (reg selectiveSwapPay)) = []
  priv : ∀ c (j : Fin (swapT 6)), 6 ≤ j.val → S.R (H.swaps c j) = []
  hdr : ∀ c k, S.R (H.swaps c (reg (selectiveSwapHd k))) = separator :: (hs c k).map bitSymbol

/-- A prepared swap bank contains only its five bounded headers; all other words are blank. -/
theorem SelectivePrepared.swapBank_length_le {B M : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {S : Stacks T (prime + K)} (h : SelectivePrepared p X H hG hK active s B M headers S)
    (width : ℕ) (hheaders : ∀ c k, (headers c k).length ≤ width) (c : Fin 2) :
    (∑ j, (S.R (H.swaps c j)).length) ≤ swapT 6 * (width + 1) := by
  calc
    _ ≤ ∑ _j : Fin (swapT 6), (width + 1) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j.val < 5
      · let k : Fin 5 := ⟨j.val, hj⟩
        have he : j = reg (selectiveSwapHd k) := Fin.ext rfl
        rw [he, h.hdr]
        simp only [List.length_cons, List.length_map]
        exact Nat.add_le_add_right (hheaders c k) 1
      · by_cases h6 : j.val < 6
        · have he : j = reg selectiveSwapPay := by apply Fin.ext; change j.val = 5; omega
          rw [he, h.pay]
          exact Nat.zero_le _
        · rw [h.priv c j (by omega)]
          exact Nat.zero_le _
    _ = _ := by simp

/-- Changing only the stream preserves every prepared host obligation. -/
theorem SelectivePrepared.update {B M : ℕ} {hs : Fin 2 → Fin 5 → List Bool}
    {S : Stacks T (prime + K)} (V : H.Valid)
    (h : SelectivePrepared p X H hG hK active s B M hs S) (w : List (Fin (prime + K + 4))) :
    SelectivePrepared p X H hG hK active s B M hs { S with R := Function.update S.R H.src w } := by
  have hn := (List.nodup_cons.mp (V.move .A).regs).1
  have hne : ∀ k ∈ [H.out, H.ctr, H.tmp, H.cnt, H.ctmp], k ≠ H.src := by
    intro k hk he
    subst k
    exact hn hk
  have hd (d : Fin 2) : H.dst d ≠ H.src := by
    intro he
    have hh := (V.move .A).dst_regs d
    simp [he] at hh
  have ha (d : Fin 2) : H.aux d ≠ H.src := by
    intro he
    have hh := (V.move .A).aux_regs d
    simp [he] at hh
  refine ⟨h.left, ?_, ?_, ?_, ?_, ?_, fun d => ?_, fun d => ?_, fun off => ?_,
    fun c => ?_, fun c j hj => ?_, fun c k => ?_⟩
  · simpa [hne H.ctr (by simp)] using h.ctr
  · simpa [hne H.cnt (by simp)] using h.cnt
  · simpa [hne H.tmp (by simp)] using h.tmp
  · simpa [hne H.ctmp (by simp)] using h.ctmp
  · simpa [hne H.out (by simp)] using h.out
  · simpa [hd d] using h.dst d
  · simpa [ha d] using h.aux d
  · refine ⟨fun f => ?_, ?_, fun r hr hs => ?_⟩
    · simpa [SelectiveHost.Valid.cf_src H V f] using (h.inv off).1 f
    · simpa [SelectiveHost.Valid.cb_src H V off (.fld 0)] using (h.inv off).2.1
    · simpa [SelectiveHost.Valid.cb_src H V off r] using (h.inv off).2.2 r hr hs
  · simpa [V.swap_src c _] using h.pay c
  · simpa [V.swap_src c j] using h.priv c j hj
  · simpa [V.swap_src c _] using h.hdr c k

end IntegerMultBounds.MathlibTM2.Routing
