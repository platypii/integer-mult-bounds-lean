module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightBatchLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackWeightBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightPage

/-! Generate and pack the complete batch weight page from unary geometry and
owned origin packets, retaining all geometry and batch-count symbols. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def batchWeightSetup : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 103 94 64 104 105)
    (.seq weightBatchLoop (.seq packWeightBatch (uclear 64)))

def batchWeightSetupCost (P s t u q L w B : ℕ) (lo : ℕ → ℕ) : ℕ :=
  (L * (4*w+9)+4) + weightBatchLoopCost P s t u q L w B lo +
    packWeightBatchCost B (L*w) + (2*(L*w)+2)

/-- A batch-size bound independent of the particular origin schedule.
This pays for numerical initialization and unary header loading at every cell. -/
theorem batchWeightSetupCost_le (P s t u q L w B : ℕ) (lo : ℕ → ℕ)
    (hlo : ∀ i < B, lo i ≤ s) :
    batchWeightSetupCost P s t u q L w B lo ≤
      L * (6*w+9) + 40 + B * (weightBatchStepCost P s t u q L s w + 50*(L*w) + 52) := by
  have hstep (i : ℕ) (hi : i ∈ Finset.range B) :
      weightBatchStepCost P s t u q L (lo i) w ≤ weightBatchStepCost P s t u q L s w := by
    rw [weightBatchStepCost_origin P s t u q L (lo i) w, weightBatchStepCost_origin P s t u q L s w]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hlo i (Finset.mem_range.mp hi))) _
  have hh := Finset.sum_le_sum hstep
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hh
  dsimp only [batchWeightSetupCost, weightBatchLoopCost, packWeightBatchCost]
  nlinarith only [hh]

theorem batchWeightSetup_exec (P s t u q L w B : ℕ) (lo : ℕ → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hw : (S.R 94).length = w) (hbatch : (S.R 116).length = B)
    (hpacket : S.R 109 = (List.range B).flatMap (fun i => originPacket A (lo i)) ++ tail)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117), 65, 96, 104, 105, 106, 107, 108, 111, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : ∀ i < B, lo i < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ batchWeightSetupCost P s t u q L w B lo ∧
      Exec body batchWeightSetup (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R 109 tail)
          110 (batchWeightPage A w q P s t u B L lo ++ S.R 110)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(103 : Fin 117), 94, 64, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 64 (List.replicate (L*w) tick) }
  have he₁' : Exec body (unaryProduct 103 94 64 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hcount, hw, hfresh 64 (by simp)] using he₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := weightBatchLoop_exec (body := body) P s t u q L w B lo v₁ S₁ tail
    (by simpa [S₁] using hP') (by simpa [S₁] using hs') (by simpa [S₁] using ht')
    (by simpa [S₁] using hu') (by simpa [S₁] using hq) (by simpa [S₁] using hL')
    (by simpa [S₁] using hcount) (by simpa [S₁] using hw) (by simp [S₁])
    (by simpa [S₁] using hbatch) (by simpa [S₁] using hpacket)
    (by
      intro r
      have hn : coefficientReg r ≠ (64 : Fin 117) := by
        intro he; have hr := coefficientReg_range r; rw [he] at hr; omega
      simpa [S₁, hn] using hblank r)
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [S₁] using hfresh _ (by simp)) hP hs hst hu hlo hL
  let X := (List.range B).map (fun i => outputWeightRow A w q P s t u L (lo i))
  let Y := (List.range B).map (fun i => inputWeightRow A w q P s t u L (lo i))
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update (Function.update (Function.update S₁.R 109 tail)
    95 (X.reverse.flatten ++ S.R 95)) 113 (Y.reverse.flatten ++ S.R 113)) }
  have he₂' : Exec body weightBatchLoop (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂, S₁, X, Y, List.map_reverse, List.flatMap_def] using he₂
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := packWeightBatch_exec (body := body) (L*w) B X Y
    (by simp [X]) (by simp [Y])
    (by intro xs hxs; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hxs; simp)
    (by intro ys hys; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hys; simp)
    v₂ S₂ (S.R 95) (S.R 113) (by simp [S₂, S₁]) (by simpa [S₂, S₁] using hbatch)
    (by simp [S₂]) (by simp [S₂]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals simpa [S₂, S₁] using hfresh _ (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update (Function.update (Function.update S₂.R
    110 (X.flatten ++ Y.flatten ++ S.R 110)) 95 (S.R 95)) 113 (S.R 113)) }
  have he₃' : Exec body packWeightBatch (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body 64 v₃ S₃
  refine ⟨v₄, m₁ + (m₂ + (m₃ + (2*(L*w)+2))), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by simp [S₃, S₂, S₁]) ?_⟩
  · simp only [hw, hcount] at hm₁
    dsimp only [batchWeightSetupCost]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk64 : k = 64
      · subst k; simp [S₃, S₂, S₁, hfresh 64 (by simp)]
      by_cases hk95 : k = 95
      · subst k; simp [S₃, S₂, S₁]
      by_cases hk113 : k = 113
      · subst k; simp [S₃, S₂, S₁]
      by_cases hk109 : k = 109
      · subst k; simp [S₃, S₂, S₁]
      by_cases hk110 : k = 110
      · subst k; simp [S₃, S₂, S₁, X, Y, batchWeightPage, List.flatMap_def, List.append_assoc]
      simp [S₃, S₂, S₁, hk64, hk95, hk113, hk109, hk110]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
