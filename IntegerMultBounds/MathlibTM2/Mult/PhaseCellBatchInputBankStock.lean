module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInputBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchSetupStock

/-! The original batch input bank executes into runtime form with the shared setup reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem batchInputBank_setup_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (P N q l s t u band L B : ℕ) (lo : ℕ → ℕ) (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1))
    (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : 0 < L) (hLs : L ≤ s) (hlo : ∀ i < B, lo i < s)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (hrhs : rhs.length = B*L*(2*q+8)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedBatchSetupCost P N q s t u band l L B ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize
          (mk v (batchInputBank P N q l s t u band L B lo rhs borrowed outTail inp out))+depth+
            generatedBatchSetupWorkspace C P N q s t u band l L B)
        depth (generatedBatchSetup hQ)
        (mk v (batchInputBank P N q l s t u band L B lo rhs borrowed outTail inp out)) m
        (mk v' (inputSourceBank q l (2*q+8) B L 0
          (fun _ => columnWords P s t u band L q (N+1))
          (fun _ => reversedColumnWords P s t u band L q (N+1)) [] [] outTail
          (csyms A (2*q+8) (reciprocalWord P s t u band L q (N+1)) ++
            (List.range B).flatMap (fun i => outputWeightRow A (2*q+8) q P s t u L (lo i)) ++ rhs ++
            (List.range B).flatMap (fun i => inputWeightRow A (2*q+8) q P s t u L (lo i)) ++ borrowed) inp out))) := by
  let S := batchInputBank P N q l s t u band L B lo rhs borrowed outTail inp out
  have hlow (k : Fin 117) (hk : k.val < 93) : S.R k = [] := by
    have hn (n : ℕ) (h : 93 ≤ n) : k.val ≠ n := by omega
    simp [S, batchInputBank, hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
      hn 97 (by decide), hn 98 (by decide), hn 99 (by decide), hn 100 (by decide), hn 109 (by decide),
      hn 112 (by decide), hn 114 (by decide), hn 116 (by decide), hn 110 (by decide), hn 93 (by decide)]
  have hc : CClean mul S := by
    intro i
    refine ⟨rfl, hlow (mul i) ?_⟩
    have hi := i.isLt
    dsimp [mul]
    omega
  have hb : ∀ r, S.R (cr r) = [] := by
    intro r
    obtain ⟨_, hhi, h93, _⟩ := cr_range r
    have hn (n : ℕ) (h : 97 ≤ n) : (cr r).val ≠ n := by omega
    simp [S, batchInputBank, hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
      hn 97 (by decide), hn 98 (by decide), hn 99 (by decide), hn 100 (by decide), hn 109 (by decide),
      hn 112 (by decide), hn 114 (by decide), hn 116 (by decide), hn 110 (by decide), h93]
  obtain ⟨v', m, hu', hm, he⟩ := generatedBatchSetup_exec_within (body := body) (band := band) (l := l) (B := B)
    hQ hA lo hP hqMax hs hst hu hL hLs hlo C hpush v S rhs borrowed (List.replicate l tick)
    (by simp [S, batchInputBank]) (by simp [S, batchInputBank]) (by simp [S, batchInputBank])
    (by simp [S, batchInputBank]) (by simp [S, batchInputBank]) (by simp [S, batchInputBank])
    (by simp [S, batchInputBank]) (by simp [S, batchInputBank]) (by simp [S, batchInputBank])
    (by simp [S, batchInputBank]) (by simp) (by simp [S, batchInputBank])
    (by simp [S, batchInputBank]) hrhs hc hb (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [S, batchInputBank])
  exact ⟨v', m, hu', hm, (fun depth => (he depth).cast rfl (congrArg (mk v')
    (generatedBatchBank_eq_inputSourceBank P N q l s t u band L B lo rhs borrowed outTail inp out)))⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
