module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightBatchStep

/-! Execute all ambient-origin packets with a structural counted loop.
The two accumulators contain rows in reverse cell order; the packer reverses
whole rows, preserving the coordinate order and bits within each row. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def originPacket (A lo : ℕ) : List (Fin (A + 4)) := List.replicate lo tick ++ [blank]

def weightBatchLoop : Pr P₀ 117 Q A U := scanP 116 107 weightBatchStep

def weightBatchLoopCost (P s t u q L w B : ℕ) (lo : ℕ → ℕ) : ℕ :=
  (∑ i ∈ Finset.range B, weightBatchStepCost P s t u q L (lo i) w) + 5 * B + 4

theorem weightBatchLoop_exec (P s t u q L w B : ℕ) (lo : ℕ → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hw : (S.R 94).length = w) (hrow : (S.R 64).length = L * w)
    (hbatch : (S.R 116).length = B)
    (hpacket : S.R 109 = (List.range B).flatMap (fun i => originPacket A (lo i)) ++ tail)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 104, 105, 106, 107, 108, 111, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : ∀ i < B, lo i < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ weightBatchLoopCost P s t u q L w B lo ∧
      Exec body weightBatchLoop (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 109 tail)
          95 (((List.range B).reverse.flatMap (fun i => outputWeightRow A w q P s t u L (lo i))) ++ S.R 95))
          113 (((List.range B).reverse.flatMap (fun i => inputWeightRow A w q P s t u L (lo i))) ++ S.R 113)) }) := by
  let X := fun i => outputWeightRow A w q P s t u L (lo i)
  let Y := fun i => inputWeightRow A w q P s t u L (lo i)
  let F := fun i => originPacket A (lo i)
  let Ψ : ℕ → Regs 117 A := fun i => Function.update (Function.update (Function.update S.R
    109 (((List.range B).drop i).flatMap F ++ tail))
    95 ((List.range i).reverse.flatMap X ++ S.R 95))
    113 ((List.range i).reverse.flatMap Y ++ S.R 113)
  have hlow (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
    obtain ⟨r, rfl⟩ := coefficientReg_covers k hk
    exact hblank r
  have hstep : IterSpec body weightBatchStep 116 107 Ψ
      (fun i => weightBatchStepCost P s t u q L (lo i) w) B := by
    intro i hi vi Si hSi
    have hd : (List.range B).drop i = i :: (List.range B).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]
      simp
    let rest := ((List.range B).drop (i + 1)).flatMap F ++ tail
    have hkeep (k : Fin 117) (hk : k ∉ [(116 : Fin 117), 107, 109, 95, 113]) : Si.R k = S.R k := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      rw [hSi k hk.1 hk.2.1]
      simp [Ψ, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2]
    obtain ⟨vi', m, hu', hm, he⟩ := weightBatchStep_exec (body := body) P s t u q L (lo i) w vi Si rest
      (by rw [hkeep 114 (by decide)]; exact hP') (by rw [hkeep 97 (by decide)]; exact hs')
      (by rw [hkeep 98 (by decide)]; exact ht') (by rw [hkeep 99 (by decide)]; exact hu')
      (by rw [hkeep 112 (by decide)]; exact hq) (by rw [hkeep 102 (by decide)]; exact hL')
      (by rw [hkeep 103 (by decide)]; exact hcount) (by rw [hkeep 94 (by decide)]; exact hw)
      (by rw [hkeep 64 (by decide)]; exact hrow)
      (by rw [hSi 109 (by decide) (by decide)]; simp [Ψ, hd, F, originPacket, rest, List.append_assoc])
      (by
        intro r
        have hr := coefficientReg_range r
        have hn : coefficientReg r ∉ [(116 : Fin 117), 107, 109, 95, 113] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          intro he
          rcases he with he | he | he | he | he <;> rw [he] at hr <;> omega
        rw [hkeep _ hn]
        exact hblank r)
      (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals rw [hkeep _ (by decide)]; exact hfresh _ (by simp)) hP hs hst hu (hlo i hi) hL
    let R' : Regs 117 A := fun k => if k.val < 63 then [] else if k = 109 then rest
      else if k = 95 then X i ++ Si.R 95 else if k = 113 then Y i ++ Si.R 113 else Si.R k
    refine ⟨vi', R', m, hu', hm, he, by simp [R'], by simp [R'], ?_⟩
    intro k hk116 hk107
    by_cases hk109 : k = 109
    · subst k; simp [R', Ψ, rest]
    by_cases hk95 : k = 95
    · subst k
      rw [show R' 95 = X i ++ Si.R 95 by simp [R'], hSi 95 (by decide) (by decide)]
      simp [Ψ, List.range_succ, List.reverse_append, List.append_assoc]
    by_cases hk113 : k = 113
    · subst k
      rw [show R' 113 = Y i ++ Si.R 113 by simp [R'], hSi 113 (by decide) (by decide)]
      simp [Ψ, List.range_succ, List.reverse_append, List.append_assoc]
    by_cases hklo : k.val < 63
    · simp [R', Ψ, hklo, hk109, hk95, hk113, hlow k hklo]
    rw [show R' k = Si.R k by simp [R', hklo, hk109, hk95, hk113], hSi k hk116 hk107]
    simp [Ψ, hk109, hk95, hk113]
  obtain ⟨v', R', m, hu', hm, he, h116, h107, hrest⟩ := scanP_exec (body := body)
    (show (116 : Fin 117) ≠ 107 by decide) hstep 0 v S (by simp [hbatch]) (by
      intro k _ _
      by_cases hk109 : k = 109
      · subst k; simpa [Ψ, F] using hpacket
      simp only [Ψ, List.range_zero, List.reverse_nil, List.flatMap_nil, List.nil_append,
        List.drop_zero]
      by_cases hk95 : k = 95
      · subst k; simp
      by_cases hk113 : k = 113
      · subst k; simp
      simp [hk109, hk95, hk113])
  have hR : R' = Ψ B := by
    funext k
    by_cases hk116 : k = 116
    · subst k; simpa [Ψ, hfresh 107 (by simp)] using h116
    by_cases hk107 : k = 107
    · subst k; simpa [Ψ, hfresh 107 (by simp)] using h107
    simpa [hbatch] using hrest k hk116 hk107
  rw [hR] at he
  refine ⟨v', m, hu', ?_, he.cast rfl ?_⟩
  · simp only [hbatch, hfresh 107 (by simp), List.length_nil, Nat.zero_add,
      Nat.mul_zero, Nat.add_zero, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul] at hm
    dsimp only [weightBatchLoopCost]
    omega
  · congr 1
    have hd : (List.range B).drop B = [] := List.drop_eq_nil_of_le (by simp)
    simp [Ψ, hd, X, Y]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
