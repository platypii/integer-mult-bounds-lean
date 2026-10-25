module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFloorWord
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Generate all counters for the column's dyadic encoding

P/n/q/W are ordinary retained unary headers. Compute the source shift P*n+1-q,
the output width 2*q+8 and the remaining padding; all arithmetic scratch restores.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareColumnEncoding : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 114 116 115 104 105)
    (.seq (.act (pushN 115 (fun _ => tick) 1 .done))
      (.seq (usub 112 115 104) (.seq (umul 2 112 98 104)
        (.seq (.act (pushN 98 (fun _ => tick) 8 .done))
          (.seq (ucopy 94 107 104) (.seq (usub 115 107 104) (usub 98 107 104)))))))

def encodingCounterBank {A : ℕ} (S : Stacks 117 A) (W q r : ℕ) : Stacks 117 A :=
  { S with R := (Function.update (Function.update (Function.update S.R
    115 (List.replicate (r - q) tick)) 98 (List.replicate (2 * q + 8) tick))
      107 (List.replicate (W - (r - q + (2 * q + 8))) tick)) }

private theorem pushTicks_exec (r : Fin 117) (c : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A) :
    Exec body (.act (pushN r (fun _ => tick) c .done)) (mk v S) 1
      (mk v { S with R := Function.update S.R r (List.replicate c tick ++ S.R r) }) := by
  have he := Exec.act (body := body) (pushN r (fun _ => tick) c .done) (mk v S)
  rw [pushN_run] at he
  exact he

theorem prepareColumnEncoding_exec (P n q W : ℕ) (hn : 1 ≤ n)
    (hscale : P * n + 1 ≤ W) (hqr : q ≤ P * n + 1)
    (hwidth : P * n + 1 - q + (2 * q + 8) ≤ W)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hnR : (S.R 116).length = n)
    (hq : (S.R 112).length = q) (hW : (S.R 94).length = W)
    (hfresh : ∀ k ∈ [(115 : Fin 117), 98, 107, 104, 105], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 29 * W + 26 ∧
      Exec body prepareColumnEncoding (mk v S) m (mk v' (encodingCounterBank S W q (P * n + 1))) := by
  let a := P * n + 1 - q
  let w := 2 * q + 8
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(114 : Fin 117), 116, 115, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 115 (List.replicate (P * n) tick) }
  have he₁' : Exec body (unaryProduct 114 116 115 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hP, hnR, hfresh 115 (by simp), List.append_nil] using he₁
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 115 (List.replicate (P * n + 1) tick) }
  have he₂ : Exec body (.act (pushN 115 (fun _ => tick) 1 .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    have hex := pushTicks_exec (body := body) 115 1 v₁ S₁
    rw [show S₁.R 115 = List.replicate (P * n) tick by simp [S₁], List.replicate_append_replicate,
      show 1 + P * n = P * n + 1 by omega] at hex
    exact hex
  obtain ⟨v₃, hu₃, he₃⟩ := usub_exec (body := body) (a := 112) (b := 115) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₂ (by simpa [S₂, S₁] using hfresh 104 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 115 (List.replicate a tick) }
  have he₃' : Exec body (usub 112 115 104) (mk v₁ S₂) (4 * q + 4) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hq, a] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := umul_exec (body := body) 2 (a := 112) (b := 98) (t := 104)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 98 (List.replicate (2 * q) tick) }
  have he₄' : Exec body (umul 2 112 98 104) (mk v₃ S₃) (4 * q + 4) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂, S₁, hq, hfresh 98 (by simp)] using he₄
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 98 (List.replicate w tick) }
  have he₅ : Exec body (.act (pushN 98 (fun _ => tick) 8 .done)) (mk v₄ S₄) 1 (mk v₄ S₅) := by
    have hex := pushTicks_exec (body := body) 98 8 v₄ S₄
    rw [show S₄.R 98 = List.replicate (2 * q) tick by simp [S₄], List.replicate_append_replicate,
      show 8 + 2 * q = 2 * q + 8 by omega] at hex
    exact hex
  obtain ⟨v₆, hu₆, he₆⟩ := ucopy_exec (body := body) (a := 94) (b := 107) (t := 104)
    (by decide) (by decide) (by decide) v₄ S₅ (by simpa [S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₆ : Stacks 117 A := { S₅ with R := Function.update S₅.R 107 (List.replicate W tick) }
  have he₆' : Exec body (ucopy 94 107 104) (mk v₄ S₅) (4 * W + 4) (mk v₆ S₆) := by
    simpa [S₆, S₅, S₄, S₃, S₂, S₁, hW, hfresh 107 (by simp)] using he₆
  obtain ⟨v₇, hu₇, he₇⟩ := usub_exec (body := body) (a := 115) (b := 107) (t := 104)
    (by decide) (by decide) (by decide) v₆ S₆ (by simpa [S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₇ : Stacks 117 A := { S₆ with R := Function.update S₆.R 107 (List.replicate (W - a) tick) }
  have he₇' : Exec body (usub 115 107 104) (mk v₆ S₆) (4 * a + 4) (mk v₇ S₇) := by
    simpa [S₇, S₆, S₅, S₄, S₃] using he₇
  obtain ⟨v₈, hu₈, he₈⟩ := usub_exec (body := body) (a := 98) (b := 107) (t := 104)
    (by decide) (by decide) (by decide) v₇ S₇ (by simpa [S₇, S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
  have hw₇ : (S₇.R 98).length = w := by simp [S₇, S₆, S₅]
  refine ⟨v₈, m₁ + 8 * q + 4 * W + 4 * a + 4 * w + 22,
    hu₈.trans (hu₇.trans (hu₆.trans (hu₄.trans (hu₃.trans hu₁)))), ?_, ?_⟩
  · rw [hP, hnR] at hm₁
    have hpW : P ≤ W := by
      have hp : P ≤ P * n := by nlinarith
      omega
    have hqW : q ≤ W := hqr.trans hscale
    change a + w ≤ W at hwidth
    nlinarith only [hm₁, hscale, hpW, hqW, hwidth]
  · refine (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄'
      (Exec.seq he₅ (Exec.seq he₆' (Exec.seq he₇' he₈))))))).cast (by rw [hw₇]; ring) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases he : k = 107
    · subst k; simp [S₇, S₆, S₅, encodingCounterBank, a, w, Nat.sub_sub]
    by_cases hs : k = 115
    · subst k; simp [S₇, S₆, S₅, S₄, S₃, encodingCounterBank, a]
    by_cases hw : k = 98
    · subst k; simp [S₇, S₆, S₅, encodingCounterBank, w]
    simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, encodingCounterBank, he, hs, hw]

theorem encodingCounterBank_ready {A : ℕ} (S : Stacks 117 A) (W q r : ℕ) (htmp : S.R 105 = []) :
    FloorSliceReady 115 98 107 105 (r - q) (2 * q + 8) (W - (r - q + (2 * q + 8)))
      (encodingCounterBank S W q r).R := by
  simp [FloorSliceReady, encodingCounterBank, htmp]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
