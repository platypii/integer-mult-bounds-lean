module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Construct the dimension-based arithmetic width from unary input headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateWeightWidth : Pr P₀ 117 Q A U :=
  .seq (ucopy 94 115 104) (.seq (ucopy 112 115 104)
    (.seq (umul 13 114 115 104) (.seq (.act (pushN 115 (fun _ => tick) 18 .done))
      (.seq (unarySize 98 115 0 1 2 3 4) (.seq (unarySize 99 115 0 1 2 3 4)
        (.seq (unarySize 98 115 0 1 2 3 4) (unarySize 98 115 0 1 2 3 4)))))))

def weightWidthCost (P q w t u : ℕ) : ℕ := 4 * w + 4 * q + 4 * P + 19 * (3 * t + u) + 45

theorem generateWeightWidth_exec (P q w t u : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hw : (S.R 94).length = w) (ht : (S.R 98).length = t) (hu : (S.R 99).length = u)
    (hfresh : ∀ k ∈ [(0 : Fin 117), 1, 2, 3, 4, 104, 115], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ weightWidthCost P q w t u ∧
      Exec body generateWeightWidth (mk v S) m
        (mk v' { S with R := (Function.update S.R 115
          (List.replicate (weightWorkspaceWidth P q w t u) tick)) }) := by
  let B := fun a : ℕ => ({ S with R := Function.update S.R 115 (List.replicate a tick) } : Stacks 117 A)
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec (body := body) (a := 94) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v S (hfresh 104 (by simp))
  have he₁' : Exec body (ucopy 94 115 104) (mk v S) (4 * w + 4) (mk v₁ (B w)) := by
    simpa [B, hw, hfresh 115 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := ucopy_exec (body := body) (a := 112) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v₁ (B w) (by simpa [B] using hfresh 104 (by simp))
  have he₂' : Exec body (ucopy 112 115 104) (mk v₁ (B w)) (4 * q + 4) (mk v₂ (B (w + q))) := by
    simpa [B, hq, List.replicate_append_replicate, Nat.add_comm] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := umul_exec (body := body) 13 (a := 114) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v₂ (B (w + q)) (by simpa [B] using hfresh 104 (by simp))
  have he₃' : Exec body (umul 13 114 115 104) (mk v₂ (B (w + q))) (4 * P + 4)
      (mk v₃ (B (w + q + 13 * P))) := by
    simpa [B, hP, List.replicate_append_replicate, Nat.add_comm] using he₃
  have hp := Exec.act (body := body) (pushN 115 (fun _ => tick) 18 .done) (mk v₃ (B (w + q + 13 * P)))
  rw [pushN_run] at hp
  have hp' : Exec body (.act (pushN 115 (fun _ => tick) 18 .done))
      (mk v₃ (B (w + q + 13 * P))) 1 (mk v₃ (B (w + q + 13 * P + 18))) := by
    rw [show (B (w + q + 13 * P)).R 115 = List.replicate (w + q + 13 * P) tick by simp [B],
      List.replicate_append_replicate, show 18 + (w + q + 13 * P) = w + q + 13 * P + 18 by omega] at hp
    simpa [B, Action.run] using hp
  have hsize (src : Fin 117) (hs : src ∈ [(98 : Fin 117), 99]) (n a : ℕ)
      (hn : (S.R src).length = n) (vi : HS 117 Q A U) :
      ∃ vi' m, vi'.user = vi.user ∧ m ≤ 19 * n + 8 ∧
        Exec body (unarySize src 115 0 1 2 3 4) (mk vi (B a)) m (mk vi' (B (a + Nat.size n))) := by
    have hreg : [src, (115 : Fin 117), 0, 1, 2, 3, 4].Nodup := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> decide
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
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := hsize 98 (by simp) t (w + q + 13 * P + 18) ht v₃
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := hsize 99 (by simp) u (w + q + 13 * P + 18 + Nat.size t) hu v₄
  obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := hsize 98 (by simp) t
    (w + q + 13 * P + 18 + Nat.size t + Nat.size u) ht v₅
  obtain ⟨v₇, m₇, hu₇, hm₇, he₇⟩ := hsize 98 (by simp) t
    (w + q + 13 * P + 18 + Nat.size t + Nat.size u + Nat.size t) ht v₆
  refine ⟨v₇, (4 * w + 4) + ((4 * q + 4) + ((4 * P + 4) + (1 + (m₄ + (m₅ + (m₆ + m₇)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))),
    by unfold weightWidthCost; omega,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq hp' (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ he₇))))))).cast rfl ?_⟩
  have heq : w + q + 13 * P + 18 + Nat.size t + Nat.size u + Nat.size t + Nat.size t =
      weightWorkspaceWidth P q w t u := by
    unfold weightWorkspaceWidth coefficientWorkspaceWidth
    simp only [Nat.size_zero]
    omega
  rw [heq]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
