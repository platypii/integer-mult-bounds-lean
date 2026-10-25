module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedWeightInit
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseWeightBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackWeightBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightPage

/-! Build a complete grouped weight page with one numerical initialization and
fixed-width binary origins. The entire retained table and all work counters
are released, and the output is the existing batch runtime weight format. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def sharedBatchWeightSetup : Pr P₀ 117 Q A U :=
  .seq sharedWeightInit (.seq (unaryProduct 103 94 64 104 105) (.seq (ucopy 116 107 104)
    (.seq retainedWeightLoop (.seq releaseWeightBank (.seq packWeightBatch (clearWords [64, 115]))))))

def sharedBatchWeightSetupCost (P s t u q L w B : ℕ) : ℕ :=
  let V := weightWorkspaceWidth P q w t u
  sharedWeightInitCost P s t u q L w + L*(6*w+9) + 128*V + 172 +
    B*(retainedWeightStepCost V w P L + 50*(L*w)+54)

theorem sharedBatchWeightSetup_exec (P s t u q L w B : ℕ) (lo : ℕ → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hrows : (S.R 103).length = L)
    (hw : (S.R 94).length = w) (hB : (S.R 116).length = B)
    (hpacket : S.R 109 = (List.range B).flatMap
      (fun i => binSyms (weightWorkspaceWidth P q w t u) (lo i)) ++ tail)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117), 65, 96, 104, 105, 106, 107, 108, 111, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : ∀ i < B, lo i < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ sharedBatchWeightSetupCost P s t u q L w B ∧
      Exec body sharedBatchWeightSetup (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R 109 tail)
          110 (batchWeightPage A w q P s t u B L lo ++ S.R 110)) }) := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, S₁, m₁, st₁, hu₁, hm₁, he₁, hr₁, hh₁, h115, hi₁, ho₁, hl₁, hf₁⟩ :=
    sharedWeightInit_exec (body := body) P s t u q L w v S hP' hs' ht' hu' hq hL' hw hblank (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      all_goals exact hfresh _ (by simp)) hP hs hst hu hL
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryProduct_exec (body := body)
    (show [(103 : Fin 117), 94, 64, 104, 105].Nodup by decide) v₁ S₁
    (by rw [hf₁ 104 (by decide) (by decide)]; exact hfresh 104 (by simp))
    (by rw [hf₁ 105 (by decide) (by decide)]; exact hfresh 105 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 64 (List.replicate (L*w) tick) }
  have he₂' : Exec body (unaryProduct 103 94 64 104 105) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂, hf₁ 103 (by decide) (by decide), hf₁ 94 (by decide) (by decide), hrows, hw,
      hf₁ 64 (by decide) (by decide), hfresh 64 (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := ucopy_exec (body := body) (a := 116) (b := 107) (t := 104)
    (by decide) (by decide) (by decide) v₂ S₂
    (by simp [S₂, hf₁ 104 (by decide) (by decide), hfresh 104 (by simp)])
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 107 (List.replicate B tick) }
  have he₃' : Exec body (ucopy 116 107 104) (mk v₂ S₂) (4*B+4) (mk v₃ S₃) := by
    simpa [S₃, S₂, hf₁ 116 (by decide) (by decide), hB,
      hf₁ 107 (by decide) (by decide), hfresh 107 (by simp)] using he₃
  have hbase (k : Fin 117) (hk : 63 ≤ k.val) (h64 : k ≠ 64) (h107 : k ≠ 107) (h115 : k ≠ 115) :
      S₃.R k = S.R k := by simp [S₃, S₂, h64, h107, hf₁ k hk h115]
  have hh₃ : tblHolds coefficientReg S₃ (tblRho V (List.replicate V tick) (List.replicate w tick) st₁) := by
    intro r
    have hr := coefficientReg_range r
    have hn (n : Fin 117) (h : 63 ≤ n.val) : coefficientReg r ≠ n := by intro he; rw [he] at hr; omega
    simpa [S₃, S₂, hn 64 (by decide), hn 107 (by decide)] using hh₁ r
  obtain ⟨v₄, S₄, m₄, st₄, hu₄, hm₄, he₄, hr₄, hh₄, h107, hp₄, hx₄, hy₄, hi₄, ho₄, hl₄, hf₄⟩ :=
    retainedWeightLoop_exec (body := body) lo st₁ hr₁ hP hs hst hu hlo hL rfl v₃ S₃ tail hh₃
      (by rw [hbase 94 (by decide) (by decide) (by decide) (by decide)]; exact hw)
      (by rw [hbase 103 (by decide) (by decide) (by decide) (by decide)]; exact hrows)
      (by simp [S₃, S₂, h115]) (by simp [S₃, S₂]) (by simp [S₃])
      (by rw [hbase 109 (by decide) (by decide) (by decide) (by decide)]; exact hpacket) (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl
        all_goals rw [hbase _ (by decide) (by decide) (by decide) (by decide)]; exact hfresh _ (by simp))
  have hwV : w ≤ V := (weightWorkspaceWidth_facts (q := q) (w := w) hP hs hst hu hs hL).1
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := releaseWeightBank_exec (body := body) V w st₄ hwV hr₄.acc v₄ S₄ hh₄
  let S₅ : Stacks 117 A := { S₄ with R := fun k => if k.val < 63 then [] else S₄.R k }
  have hkeep (k : Fin 117) (hk : 63 ≤ k.val) (hn109 : k ≠ 109) (hn95 : k ≠ 95)
      (hn113 : k ≠ 113) (hn107 : k ≠ 107) : S₅.R k = S₃.R k := by
    simpa [S₅, show ¬ k.val < 63 by omega] using hf₄ k hk hn109 hn95 hn113 hn107
  let X := (List.range B).map (fun i => outputWeightRow A w q P s t u L (lo i))
  let Y := (List.range B).map (fun i => inputWeightRow A w q P s t u L (lo i))
  obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := packWeightBatch_exec (body := body) (L*w) B X Y
    (by simp [X]) (by simp [Y])
    (by intro xs hxs; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hxs; simp)
    (by intro ys hys; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hys; simp)
    v₅ S₅ (S.R 95) (S.R 113)
    (by rw [hkeep 64 (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [S₃, S₂])
    (by rw [hkeep 116 (by decide) (by decide) (by decide) (by decide) (by decide),
      hbase 116 (by decide) (by decide) (by decide) (by decide)]; exact hB)
    (by simpa [S₅, X, List.map_reverse, List.flatMap_def, hbase 95 (by decide) (by decide) (by decide) (by decide)] using hx₄)
    (by simpa [S₅, Y, List.map_reverse, List.flatMap_def, hbase 113 (by decide) (by decide) (by decide) (by decide)] using hy₄) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals rw [hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide),
        hbase _ (by decide) (by decide) (by decide) (by decide)]; exact hfresh _ (by simp))
  have h110 : S₅.R 110 = S.R 110 := (hkeep 110 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (hbase 110 (by decide) (by decide) (by decide) (by decide))
  let S₆ : Stacks 117 A := { S₅ with R := (Function.update (Function.update (Function.update S₅.R
    110 (X.flatten ++ Y.flatten ++ S.R 110)) 95 (S.R 95)) 113 (S.R 113)) }
  have he₆' : Exec body packWeightBatch (mk v₅ S₅) m₆ (mk v₆ S₆) := by simpa [S₆, h110] using he₆
  obtain ⟨v₇, hu₇, he₇⟩ := clearWords_exec (body := body) [(64 : Fin 117), 115] (by decide) v₆ S₆
  have hsum : ([(64 : Fin 117), 115].map (fun k => (S₆.R k).length)).sum = L*w+V := by
    simp [S₆, hkeep 64 (by decide) (by decide) (by decide) (by decide) (by decide),
      hkeep 115 (by decide) (by decide) (by decide) (by decide) (by decide), S₃, S₂, h115, V]
  refine ⟨v₇, m₁+(m₂+((4*B+4)+(m₄+(m₅+(m₆+(2*(L*w+V)+5)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))), ?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆' he₇)))))).cast
      (by rw [hsum]; rfl) ?_⟩
  · have hm₂' : m₂ ≤ L*(4*w+9)+4 := by
      simpa [hf₁ 103 (by decide) (by decide), hf₁ 94 (by decide) (by decide), hrows, hw] using hm₂
    dsimp only [sharedBatchWeightSetupCost]
    dsimp only [V] at *
    unfold packWeightBatchCost at hm₆
    nlinarith only [hm₁, hm₂', hm₄, hm₅, hm₆]
  · congr 1
    ext1
    · exact hi₄.trans hi₁
    · exact ho₄.trans ho₁
    · exact hl₄.trans hl₁
    · funext k
      by_cases h64 : k = 64
      · subst k; simp [hfresh 64 (by simp)]
      by_cases h115 : k = 115
      · subst k; simp [hfresh 115 (by simp)]
      by_cases h95 : k = 95
      · subst k; simp [S₆]
      by_cases h113 : k = 113
      · subst k; simp [S₆]
      by_cases h109 : k = 109
      · subst k; simp [S₆, S₅, hp₄]
      by_cases h110 : k = 110
      · subst k; simp [S₆, X, Y, batchWeightPage, List.flatMap_def, List.append_assoc]
      by_cases h107 : k = 107
      · subst k; simp [S₆, S₅, h107, hfresh 107 (by simp)]
      by_cases hklo : k.val < 63
      · have hzero : S.R k = [] := by
          obtain ⟨r, rfl⟩ := coefficientReg_covers k hklo
          exact hblank r
        simp [S₆, S₅, h64, h115, h95, h113, h109, h110, hklo, hzero]
      simpa [S₆, Function.update_apply, h64, h115, h109, h110, h95, h113] using
        (hkeep k (by omega) h109 h95 h113 h107).trans (hbase k (by omega) h64 h107 h115)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
