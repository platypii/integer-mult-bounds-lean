module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedWeightSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherControl

/-! Generate one cell's two weight rows from an owned ambient-origin packet.
The separate accumulators allow the batch packer to restore cell order later. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def weightBatchStep : Pr P₀ 117 Q A U :=
  .seq (gatherRead 109 111 105) (.seq (uclear 105)
    (.seq packedWeightSetup (.seq (takePrefix 64 110 95 104 105)
      (.seq (takePrefix 64 110 113 104 105) (uclear 111)))))

def weightBatchStepCost (P s t u q L lo w : ℕ) : ℕ :=
  packedWeightSetupCost P s t u q L lo w + 12 * (L * w) + 6 * lo + 21

/-- All origin-dependent work is charged explicitly, including unary loading. -/
theorem weightBatchStepCost_origin (P s t u q L lo w : ℕ) :
    weightBatchStepCost P s t u q L lo w = weightBatchStepCost P s t u q L 0 w +
      lo * (4 * weightWorkspaceWidth P q w t u + 16) := by
  dsimp only [weightBatchStepCost, packedWeightSetupCost, weightSetupCost,
    weightFactoryCost, weightHeadersCost]
  ring

def outputWeightRow (A w q P s t u L lo : ℕ) : List (Fin (A + 4)) :=
  cstream A w ((List.range L).reverse.map (fun i => rationalWord q (ambientWeightSample P s t u lo i)))

def inputWeightRow (A w q P s t u L lo : ℕ) : List (Fin (A + 4)) :=
  cstream A w ((List.range L).map (fun i => reciprocalWeightWord q (ambientWeightSample P s t u lo i)))

@[simp] theorem outputWeightRow_length (A w q P s t u L lo : ℕ) :
    (outputWeightRow A w q P s t u L lo).length = L * w := by simp [outputWeightRow]

@[simp] theorem inputWeightRow_length (A w q P s t u L lo : ℕ) :
    (inputWeightRow A w q P s t u L lo).length = L * w := by simp [inputWeightRow]

theorem weightBatchStep_exec (P s t u q L lo w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (tail : List (Fin (A + 4)))
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hw : (S.R 94).length = w) (hrow : (S.R 64).length = L * w)
    (hpacket : S.R 109 = List.replicate lo tick ++ blank :: tail)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 104, 105, 106, 108, 111, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ weightBatchStepCost P s t u q L lo w ∧
      Exec body weightBatchStep (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 109 then tail
          else if k = 95 then outputWeightRow A w q P s t u L lo ++ S.R 95
          else if k = 113 then inputWeightRow A w q P s t u L lo ++ S.R 113 else S.R k) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := gatherRead_exec (body := body)
    (show [(109 : Fin 117), 111, 105].Nodup by decide) lo tail v S hpacket
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update (Function.update S.R
    109 tail) 111 (List.replicate lo tick)) 105 (blank :: List.replicate lo tick)) }
  have he₁' : Exec body (gatherRead 109 111 105) (mk v S) (2 * lo + 3) (mk v₁ S₁) := by
    simpa [S₁, hfresh 111 (by simp), hfresh 105 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body 105 v₁ S₁
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 105 [] }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := packedWeightSetup_exec (body := body) P s t u q L lo w v₂ S₂
    (by simpa [S₂, S₁] using hP') (by simpa [S₂, S₁] using hs')
    (by simpa [S₂, S₁] using ht') (by simpa [S₂, S₁] using hu')
    (by simpa [S₂, S₁] using hq) (by simpa [S₂, S₁] using hL')
    (by simpa [S₂, S₁] using hcount) (by simp [S₂, S₁]) (by simpa [S₂, S₁] using hw)
    (by
      intro r
      have hr := coefficientReg_range r
      have hn (n : Fin 117) (h : 63 ≤ n.val) : coefficientReg r ≠ n := by
        intro he; rw [he] at hr; omega
      simpa [S₂, S₁, hn 105 (by decide), hn 109 (by decide), hn 111 (by decide)] using hblank r)
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [S₂, S₁] using hfresh 96 (by simp)
      · simpa [S₂, S₁] using hfresh 104 (by simp)
      · simp [S₂]
      all_goals simpa [S₂, S₁] using hfresh _ (by simp)) hP hs hst hu hlo hL
  let X := outputWeightRow A w q P s t u L lo
  let Y := inputWeightRow A w q P s t u L lo
  let S₃ : Stacks 117 A := { S₂ with R := (fun k => if k.val < 63 then [] else if k = 110 then
    X ++ Y ++ S₂.R 110 else S₂.R k) }
  have he₃' : Exec body packedWeightSetup (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa [S₃, X, Y, weightPage, outputWeightRow, inputWeightRow, List.append_assoc] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := takePrefix_exec (body := body)
    (show [(64 : Fin 117), 110, 95, 104, 105].Nodup by decide) v₃ S₃ X (Y ++ S.R 110)
    (by simp [S₃, S₂, S₁]) (by simpa [S₃, S₂, S₁, X] using hrow)
    (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp)) (by simp [S₃, S₂])
  let S₄ : Stacks 117 A := { S₃ with R := (Function.update (Function.update S₃.R 110
    (Y ++ S.R 110)) 95 (X ++ S.R 95)) }
  have he₄' : Exec body (takePrefix 64 110 95 104 105) (mk v₃ S₃) (6 * (L*w) + 6) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂, S₁, X] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := takePrefix_exec (body := body)
    (show [(64 : Fin 117), 110, 113, 104, 105].Nodup by decide) v₄ S₄ Y (S.R 110)
    (by simp [S₄]) (by simpa [S₄, S₃, S₂, S₁, Y] using hrow)
    (by simpa [S₄, S₃, S₂, S₁] using hfresh 104 (by simp)) (by simp [S₄, S₃, S₂])
  let S₅ : Stacks 117 A := { S₄ with R := (Function.update (Function.update S₄.R 110 (S.R 110))
    113 (Y ++ S.R 113)) }
  have he₅' : Exec body (takePrefix 64 110 113 104 105) (mk v₄ S₄) (6 * (L*w) + 6) (mk v₅ S₅) := by
    simpa [S₅, S₄, S₃, S₂, S₁, Y] using he₅
  obtain ⟨v₆, hu₆, he₆⟩ := uclear_exec body 111 v₅ S₅
  refine ⟨v₆, (2*lo+3) + ((2*(lo+1)+2) + (m₃ + ((6*(L*w)+6) + ((6*(L*w)+6) + (2*lo+2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),
    by unfold weightBatchStepCost; omega,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' he₆))))).cast
      (by simp [S₅, S₄, S₃, S₂, S₁]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k = 111
    · subst k; simp [S₅, S₄, S₃, S₂, S₁, hfresh 111 (by simp)]
    simp only [S₅, S₄, S₃, S₂, S₁, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [X, Y]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
