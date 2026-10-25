module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySize

/-! # A generated logarithmic workspace width for coefficient evaluation -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

def coefficientWorkspaceWidth (P W t u band L : ℕ) : ℕ :=
  W + 13 * P + Nat.size t + Nat.size u + 2 * Nat.size L + Nat.size band + 16

/-- The chosen width contains every header and the evaluator's largest argument. -/
theorem coefficientWorkspaceWidth_bound (P W s t u band L : ℕ) (hst : s ≤ t) :
    let V := coefficientWorkspaceWidth P W t u band L
    W ≤ V ∧ P < 2 ^ V ∧ s < 2 ^ V ∧ t < 2 ^ V ∧ u < 2 ^ V ∧ band < 2 ^ V ∧ L < 2 ^ V ∧
      u * t * (L + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V := by
  let V := coefficientWorkspaceWidth P W t u band L
  have ht := Nat.lt_size_self t
  have hu := Nat.lt_size_self u
  have hL := Nat.lt_size_self L
  have hb := Nat.lt_size_self band
  have hpow (a : ℕ) (ha : a ≤ V) : 2 ^ a ≤ 2 ^ V := Nat.pow_le_pow_right (by decide) ha
  have hsizeT : Nat.size t ≤ V := by dsimp [V, coefficientWorkspaceWidth]; omega
  have hsizeU : Nat.size u ≤ V := by dsimp [V, coefficientWorkspaceWidth]; omega
  have hsizeL : Nat.size L ≤ V := by dsimp [V, coefficientWorkspaceWidth]; omega
  have hsizeB : Nat.size band ≤ V := by dsimp [V, coefficientWorkspaceWidth]; omega
  refine ⟨by dsimp [V, coefficientWorkspaceWidth]; omega,
    (show P < 2 ^ P from Nat.lt_two_pow_self).trans_le (hpow P (by dsimp [V, coefficientWorkspaceWidth]; omega)),
    hst.trans_lt (ht.trans_le (hpow _ hsizeT)), ht.trans_le (hpow _ hsizeT),
    hu.trans_le (hpow _ hsizeU), hb.trans_le (hpow _ hsizeB), hL.trans_le (hpow _ hsizeL), ?_⟩
  have hut : u * t < 2 ^ (Nat.size u + Nat.size t) := by
    simpa only [pow_add] using Nat.mul_lt_mul_of_lt_of_lt hu ht
  have hLpow : (L + 1) ^ 2 ≤ 2 ^ (2 * Nat.size L) := by
    have h := Nat.pow_le_pow_left (by omega : L + 1 ≤ 2 ^ Nat.size L) 2
    simpa only [← pow_mul, Nat.mul_comm (Nat.size L) 2] using h
  have hprod : u * t * (L + 1) ^ 2 < 2 ^ (Nat.size u + Nat.size t + 2 * Nat.size L) := by
    calc
      _ ≤ u * t * 2 ^ (2 * Nat.size L) := Nat.mul_le_mul_left _ hLpow
      _ < 2 ^ (Nat.size u + Nat.size t) * 2 ^ (2 * Nat.size L) :=
        Nat.mul_lt_mul_of_pos_right hut (by positivity)
      _ = _ := by simp only [pow_add] <;> ring
  have hfull := Nat.mul_lt_mul_of_pos_right hprod (by positivity : 0 < 2 ^ (13 * P + 8))
  rw [← pow_add] at hfull
  exact hfull.trans_le (hpow _ (by dsimp [V, coefficientWorkspaceWidth]; omega))

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateCoefficientWidth : Pr P₀ 117 Q A U :=
  .seq (ucopy 94 115 104)
    (.seq (umul 13 114 115 104)
      (.seq (.act (pushN 115 (fun _ => tick) 16 .done))
        (.seq (unarySize 98 115 0 1 2 3 4)
          (.seq (unarySize 99 115 0 1 2 3 4)
            (.seq (unarySize 102 115 0 1 2 3 4)
              (.seq (unarySize 102 115 0 1 2 3 4) (unarySize 100 115 0 1 2 3 4)))))))

def coefficientWidthCost (P W t u band L : ℕ) : ℕ := 4 * W + 4 * P + 19 * (t + u + 2 * L + band) + 49

theorem generateCoefficientWidth_exec (P W t u band L : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hW : (S.R 94).length = W)
    (ht : (S.R 98).length = t) (hu : (S.R 99).length = u) (hb : (S.R 100).length = band)
    (hL : (S.R 102).length = L)
    (hfresh : ∀ k ∈ [(0 : Fin 117), 1, 2, 3, 4, 104, 115], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ coefficientWidthCost P W t u band L ∧
      Exec body generateCoefficientWidth (mk v S) m
        (mk v' { S with R := (Function.update S.R 115
          (List.replicate (coefficientWorkspaceWidth P W t u band L) tick)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec (body := body) (a := 94) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v S (hfresh 104 (by simp))
  let B := fun (x : ℕ) => ({ S with R := Function.update S.R 115 (List.replicate x tick) } : Stacks 117 A)
  have he₁' : Exec body (ucopy 94 115 104) (mk v S) (4 * W + 4) (mk v₁ (B W)) := by
    simpa [B, hW, hfresh 115 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := umul_exec (body := body) 13 (a := 114) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v₁ (B W) (by simpa [B] using hfresh 104 (by simp))
  have he₂' : Exec body (umul 13 114 115 104) (mk v₁ (B W)) (4 * P + 4) (mk v₂ (B (W + 13 * P))) := by
    simpa [B, hP, List.replicate_append_replicate, Nat.add_comm] using he₂
  have hp := Exec.act (body := body) (pushN 115 (fun _ => tick) 16 .done) (mk v₂ (B (W + 13 * P)))
  rw [pushN_run] at hp
  have hp' : Exec body (.act (pushN 115 (fun _ => tick) 16 .done))
      (mk v₂ (B (W + 13 * P))) 1 (mk v₂ (B (W + 13 * P + 16))) := by
    rw [show (B (W + 13 * P)).R 115 = List.replicate (W + 13 * P) tick by simp [B],
      List.replicate_append_replicate, show 16 + (W + 13 * P) = W + 13 * P + 16 by omega] at hp
    simpa [B, Action.run] using hp
  have hsize (src : Fin 117) (hs : src ∈ [(98 : Fin 117), 99, 100, 102]) (n a : ℕ)
      (hn : (S.R src).length = n) (vi : HS 117 Q A U) :
      ∃ vi' m, vi'.user = vi.user ∧ m ≤ 19 * n + 8 ∧
        Exec body (unarySize src 115 0 1 2 3 4) (mk vi (B a)) m (mk vi' (B (a + Nat.size n))) := by
    have hreg : [src, (115 : Fin 117), 0, 1, 2, 3, 4].Nodup := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> decide
    have hoff : src ≠ 115 := by
      intro he
      apply (List.nodup_cons.mp hreg).1
      simp [he]
    obtain ⟨vi', m, hui, hmi, hei⟩ := unarySize_exec (body := body) hreg n vi (B a)
      (by simpa [B, hoff] using hn) (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [B] using hfresh _ (by simp))
    exact ⟨vi', m, hui, hmi, by simpa [B, List.replicate_append_replicate, Nat.add_comm] using hei⟩
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := hsize 98 (by simp) t (W + 13 * P + 16) ht v₂
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := hsize 99 (by simp) u (W + 13 * P + 16 + Nat.size t) hu v₃
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := hsize 102 (by simp) L (W + 13 * P + 16 + Nat.size t + Nat.size u) hL v₄
  obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := hsize 102 (by simp) L (W + 13 * P + 16 + Nat.size t + Nat.size u + Nat.size L) hL v₅
  obtain ⟨v₇, m₇, hu₇, hm₇, he₇⟩ := hsize 100 (by simp) band
    (W + 13 * P + 16 + Nat.size t + Nat.size u + Nat.size L + Nat.size L) hb v₆
  refine ⟨v₇, (4 * W + 4) + ((4 * P + 4) + (1 + (m₃ + (m₄ + (m₅ + (m₆ + m₇)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))),
    by unfold coefficientWidthCost; nlinarith only [hm₃, hm₄, hm₅, hm₆, hm₇],
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq hp' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ he₇))))))).cast rfl ?_⟩
  have heq : W + 13 * P + 16 + Nat.size t + Nat.size u + Nat.size L + Nat.size L + Nat.size band =
      coefficientWorkspaceWidth P W t u band L := by unfold coefficientWorkspaceWidth; omega
  rw [heq]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
