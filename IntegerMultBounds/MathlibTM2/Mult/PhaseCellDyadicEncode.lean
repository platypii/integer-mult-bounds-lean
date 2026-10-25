module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFloorPass

/-! # Encode a borrowed integer column through a private word stream

The complete raw column and its suffix are preserved. A generated symbol
count copies the owned prefix, the shared word pass encodes it, and two moves
publish the result in order. Every private stream and work tape is released.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def encodeDyadicColumn : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 102 94 99 104 105)
    (.seq (copyPrefix 99 110 113 104 105) (.seq (uclear 99)
      (.seq (topPass 113 96 (floorSliceWord 113 96 115 98 107 105))
        (.seq (moveR 113 96 id) (moveR 96 111 id)))))

theorem encodeDyadicColumn_exec (L W w q r : ℕ) (hW : 1 ≤ W) (hqr : q ≤ r)
    (hwidth : r - q + w ≤ W) (zs : List ℤ) (hlen : zs.length = L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hwide : (S.R 94).length = W)
    (hsrc : S.R 110 = cstream A W (zs.map (fun z => (⟨z, 0⟩ : GaussianInt))) ++ tailX)
    (hg : FloorSliceReady 115 98 107 105 (r - q) w (W - (r - q + w)) S.R)
    (hfresh : ∀ k ∈ [(99 : Fin 117), 104, 113, 96], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ L * (20 * W + 6 * w + 23) + 24 ∧
      Exec body encodeDyadicColumn (mk v S) m
        (mk v' { S with R := (Function.update S.R 111
          (cstream A w (zs.map (dyadicWord q r)) ++ S.R 111)) }) := by
  let raw := cstream A W (zs.map (fun z => (⟨z, 0⟩ : GaussianInt)))
  let encoded := cstream A w (zs.map (dyadicWord q r))
  have hraw : raw.length = L * W := by simp [raw, hlen]
  have hencoded : encoded.length = L * w := by simp [encoded, hlen]
  have htmp : S.R 105 = [] := hg.2.2.2
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(102 : Fin 117), 94, 99, 104, 105].Nodup by decide) v S (hfresh 104 (by simp)) htmp
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 99 (List.replicate (L * W) tick) }
  have he₁' : Exec body (unaryProduct 102 94 99 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hrows, hwide, hfresh 99 (by simp), List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := copyPrefix_exec (body := body)
    (show [(99 : Fin 117), 110, 113, 104, 105].Nodup by decide) v₁ S₁ raw tailX
    (by simpa [S₁, raw] using hsrc) (by simp [S₁, hraw])
    (by simpa [S₁] using hfresh 104 (by simp)) (by simpa [S₁] using htmp)
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 113 raw }
  have he₂' : Exec body (copyPrefix 99 110 113 104 105) (mk v₁ S₁) (10 * (L * W) + 10) (mk v₂ S₂) := by
    simpa [S₂, S₁, hraw, hfresh 113 (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 99 v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 99 [] }
  have hg₃ : FloorSliceReady 115 98 107 105 (r - q) w (W - (r - q + w)) S₃.R := by
    simpa [FloorSliceReady, S₃, S₂, S₁] using hg
  obtain ⟨v₄, hu₄, he₄⟩ := dyadicPass_exec (body := body)
    (show [(113 : Fin 117), 96, 115, 98, 107, 105].Nodup by decide) W w q r hW hqr hwidth zs v₃ S₃
    (by simp [S₃, S₂, raw]) (by simpa [S₃, S₂, S₁] using hfresh 96 (by simp)) hg₃
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 113 encoded }
  have he₄' : Exec body (topPass 113 96 (floorSliceWord 113 96 115 98 107 105)) (mk v₃ S₃)
      (L * (4 * W + 2 * w + 14) + 4) (mk v₄ S₄) := by simpa only [hlen] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body 113 96 (by decide) id v₄ S₄
  let S₅ : Stacks 117 A := { S₄ with R := movedR S₄.R 113 96 id (S₄.R 113) }
  obtain ⟨v₆, hu₆, he₆⟩ := moveR_exec body 96 111 (by decide) id v₅ S₅
  have hcount₂ : (S₂.R 99).length = L * W := by simp [S₂, S₁]
  have hsrc₄ : (S₄.R 113).length = L * w := by simp [S₄, hencoded]
  have hacc₅ : (S₅.R 96).length = L * w := by
    simp [S₅, movedR, S₄, S₃, S₂, S₁, hfresh 96 (by simp), hencoded]
  refine ⟨v₆, m₁ + ((10 * (L * W) + 10) + ((2 * (L * W) + 2) +
    ((L * (4 * W + 2 * w + 14) + 4) + ((2 * (L * w) + 2) + (2 * (L * w) + 2))))),
      hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))), ?_, ?_⟩
  · rw [hrows, hwide] at hm₁
    nlinarith only [hm₁]
  · refine (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅ he₆))))).cast
      (by rw [hcount₂, hsrc₄, hacc₅]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ho : k = 111
    · subst k; simp [S₅, S₄, S₃, S₂, S₁, movedR, hfresh 96 (by simp), encoded]
    by_cases ha : k = 96
    · subst k; simp [movedR, hfresh 96 (by simp)]
    by_cases hs : k = 113
    · subst k; simp [S₅, movedR, hfresh 113 (by simp)]
    by_cases hc : k = 99
    · subst k; simp [S₅, S₄, S₃, movedR, hfresh 99 (by simp)]
    simp [S₅, S₄, S₃, S₂, S₁, movedR, ho, ha, hs, hc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
