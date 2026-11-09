module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIterations
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIterationStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIterationFrameStock

/-! Repeated inverse-column iterations share one complete numerical reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

private def iterationStockLoopBank {A : ℕ} (S : Stacks 117 A) (w : ℕ) (xs : List GaussianInt)
    (tailX cs : List (Fin (A + 4))) (M : ℕ) : Stacks 117 A :=
  { S with R := (Function.update (Function.update (Function.update (Function.update S.R
    101 []) 100 (cs.reverse ++ S.R 100)) 110 (cstream A w xs ++ tailX)) 116
      (List.replicate M tick ++ S.R 116)) }

private theorem integerIterations_loop_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (C : ℕ) (hpushBound : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    {P s t u band L w : ℕ} (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (tailX tailF : List (Fin (A + 4))) (M : ℕ) :
    ∀ (n : ℕ) (cs : List (Fin (A + 4))) (v : HS 117 Q A U) (S : Stacks 117 A),
    cs.length = M → IntegerGeneratorContext P s t u band L n w tailX tailF S →
    1 ≤ n → P * (n + M + 1) + 3 ≤ w → S.R 101 = cs → v.flag = (S.R 101).head?.isSome →
    ∃ v' m, v'.user = v.user ∧ m ≤ M * (integerIterationCost L w + 3) + 1 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*M+integerIterationWorkspace C L w)
        depth (.loop (·.flag) (.seq (.act (popPush 101 100))
        (.seq (integerIteration hQ) (.act (peekR 101))))) (mk v S) m
        (mk v' (iterationStockLoopBank S w (rowColumnWords P s t u band L (n + M)) tailX cs M))) ∧
      IntegerGeneratorContext P s t u band L (n + M) w tailX tailF
        (iterationStockLoopBank S w (rowColumnWords P s t u band L (n + M)) tailX cs M) := by
  induction M with
  | zero =>
    intro n cs v S hlen hctx hn hW hcs hf
    have hc0 : cs = [] := List.eq_nil_of_length_eq_zero hlen
    have h101 : S.R 101 = [] := hcs.trans hc0
    have hstate : iterationStockLoopBank S w (rowColumnWords P s t u band L n) tailX [] 0 = S := by
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      by_cases hx : k = 110
      · subst k; simpa [iterationStockLoopBank] using hctx.row.column.symm
      by_cases hc : k = 101
      · subst k; simpa [iterationStockLoopBank] using h101.symm
      by_cases hi : k = 116
      · subst k; simp [iterationStockLoopBank]
      by_cases hs' : k = 100
      · subst k; simp [iterationStockLoopBank]
      simp [iterationStockLoopBank, hx, hc, hi, hs']
    refine ⟨v, 1, rfl, by simp, ?_, ?_⟩
    · intro depth
      simp only [hc0, Nat.add_zero, Nat.mul_zero, hstate]
      exact ExecWithin.loop_false (s := mk v S) (f := fun v : HS 117 Q A U => v.flag)
        (by simpa [h101] using hf) (by omega)
    · simpa only [hc0, hstate, Nat.add_zero] using hctx
  | succ M ih =>
    intro n cs v S hlen hctx hn hW hcs hf
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have hlen' : cs.length = M := by simpa using hlen
      let S₀ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 101 cs) 100 (c :: S.R 100)) }
      let v₀ : HS 117 Q A U := { v with sym := some c }
      have hpop : (popPush 101 100 : Act 117 Q A U).run (mk v S) = mk v₀ S₀ := by
        simp [popPush, Action.run, hcs, update_rt, S₀, v₀]
      have hctx₀ : IntegerGeneratorContext P s t u band L n w tailX tailF S₀ :=
        (hctx.update 101 (by simp) cs).update 100 (by simp) (c :: S.R 100)
      have hW₀ : P * (n + 1) + 3 ≤ w := by
        have hm := Nat.mul_le_mul_left P (show n + 1 ≤ n + (M + 1) + 1 by omega)
        omega
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hrow₁⟩ := integerIteration_exec_within (body := body) hQ hA hW₀ hP hs hst hu hn C hpushBound
        v₀ S₀ tailX tailF hctx₀.row hctx₀.count hctx₀.precision hctx₀.iteration hctx₀.saved
        hctx₀.factors hctx₀.rest hctx₀.exponent
      let S₁ := iteratedColumn S₀ w (rowColumnWords P s t u band L (n + 1)) tailX
      have hctx₁ : IntegerGeneratorContext P s t u band L (n + 1) w tailX tailF S₁ := hctx₀.next hrow₁
      have hepeek := Exec.act (body := body) (peekR 101) (mk v₁ S₁)
      rw [peekR_run] at hepeek
      have hW₁ : P * ((n + 1) + M + 1) + 3 ≤ w := by
        have heq : (n + 1) + M + 1 = n + (M + 1) + 1 := by omega
        rw [heq]
        exact hW
      obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hctx₂⟩ := ih (n + 1) cs { v₁ with flag := (S₁.R 101).head?.isSome }
        S₁ hlen' hctx₁ (by omega) hW₁ (by simp [S₁, iteratedColumn, S₀]) rfl
      have hidx : (n + 1) + M = n + (M + 1) := by omega
      rw [hidx] at he₂ hctx₂
      have hstate : iterationStockLoopBank S₁ w (rowColumnWords P s t u band L (n + (M + 1))) tailX cs M =
          iterationStockLoopBank S w (rowColumnWords P s t u band L (n + (M + 1))) tailX (c :: cs) (M + 1) := by
        ext1
        · rfl
        · rfl
        · rfl
        funext k
        by_cases hi : k = 116
        · subst k; simp [iterationStockLoopBank, S₁, S₀, iteratedColumn, List.replicate_succ', List.append_assoc]
        by_cases hx : k = 110
        · subst k; simp [iterationStockLoopBank]
        by_cases hs' : k = 100
        · subst k; simp [iterationStockLoopBank, S₁, S₀, iteratedColumn, List.reverse_cons, List.append_assoc]
        by_cases hc : k = 101
        · subst k; simp [iterationStockLoopBank]
        simp [iterationStockLoopBank, S₁, S₀, iteratedColumn, hi, hx, hs', hc]
      refine ⟨v₂, 1 + (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_, ?_, hstate ▸ hctx₂⟩
      · nlinarith only [hm₁, hm₂]
      · intro depth
        let cap := mnSize (mk v S)+depth+2*(M+1)+integerIterationWorkspace C L w
        have hp := mn_native_exec_within (hpop ▸ Exec.act (body := body) (popPush 101 100) (mk v S))
          1 (by simp [popPush,mnNativePushBound,mnActPush]) depth
          (mnSize (mk v S)+depth+1) (by omega)
        have hs₀ : mnSize (mk v₀ S₀) ≤ mnSize (mk v S)+1 := by have hh := hp.final; omega
        have hs₁ : mnSize (mk v₁ S₁) = mnSize (mk v₀ S₀)+1 :=
          iteratedColumn_stock_eq v₀ v₁ S₀ _ _ tailX hctx₀.row.column (by simp [rowColumnWords])
        have ht₁ := (he₁ depth).mono (J := fun d z => mnSize z+d ≤ cap)
          (by intro d z hz; dsimp only [cap]; omega)
        have htpeek := mn_native_exec_within hepeek 0
          (by simp [peekR,mnNativePushBound,mnActPush]) depth cap (by have hh := ht₁.final; omega)
        have ht₂ := (he₂ depth).mono (J := fun d z => mnSize z+d ≤ cap) (by
          intro d z hz
          change mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+2*M+integerIterationWorkspace C L w at hz
          dsimp only [cap]
          omega)
        exact (ExecWithin.loop_true (by simpa [hcs] using hf)
          (.seq (hp.mono (by intro d z hz; dsimp only [cap]; omega))
            (.seq ht₁ htpeek)) ht₂).cast rfl (congrArg (mk v₂) hstate)

/-- The iteration count is executed through its original unary symbols and
restored, with a uniform paid bound and a retained ready context. -/
theorem integerIterations_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (C : ℕ) (hpushBound : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    {P s t u band L n w M : ℕ} (hW : P * (n + M + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailF : List (Fin (A + 4)))
    (hctx : IntegerGeneratorContext P s t u band L n w tailX tailF S)
    (hcount : (S.R 101).length = M) (hsaved : S.R 100 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ M * (integerIterationCost L w + 5) + 4 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(4*M+integerIterationWorkspace C L w+2))
        depth (integerIterations hQ) (mk v S) m
        (mk v' (iteratedColumns S w (rowColumnWords P s t u band L (n + M)) tailX M))) ∧
      IntegerGeneratorContext P s t u band L (n + M) w tailX tailF
        (iteratedColumns S w (rowColumnWords P s t u band L (n + M)) tailX M) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hctx₁⟩ := integerIterations_loop_within (body := body) hQ hA C hpushBound hP hs hst hu tailX tailF M
    n (S.R 101) { v with flag := (S.R 101).head?.isSome } S hcount hctx hn hW rfl rfl
  let S₁ := iterationStockLoopBank S w (rowColumnWords P s t u band L (n + M)) tailX (S.R 101) M
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body 100 101 (by decide) id v₁ S₁
  have hlen : (S₁.R 100).length = M := by simp [S₁, iterationStockLoopBank, hsaved, hcount]
  have hstate : ({ S₁ with R := movedR S₁.R 100 101 id (S₁.R 100) } : Stacks 117 A) =
      iteratedColumns S w (rowColumnWords P s t u band L (n + M)) tailX M := by
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hc : k = 101
    · subst k; simp [S₁, iterationStockLoopBank, iteratedColumns, movedR, hsaved]
    by_cases hs' : k = 100
    · subst k; simp [S₁, iterationStockLoopBank, iteratedColumns, movedR, hsaved]
    simp [S₁, iterationStockLoopBank, iteratedColumns, movedR, Function.update_apply, hc, hs']
  have hctx₂ := (hctx₁.update 100 (by simp) []).update 101 (by simp)
    (((S₁.R 100).map id).reverse ++ S₁.R 101)
  change IntegerGeneratorContext P s t u band L (n + M) w tailX tailF
    { S₁ with R := movedR S₁.R 100 101 id (S₁.R 100) } at hctx₂
  refine ⟨v₂, 1 + (m₁ + (2 * M + 2)), hu₂.trans hu₁, ?_, ?_, hstate ▸ hctx₂⟩
  · nlinarith only [hm₁]
  · intro depth
    let cap := mnSize (mk v S)+depth+(4*M+integerIterationWorkspace C L w+2)
    have hpeek := peekR_run 101 v S ▸ Exec.act (body := body) (peekR 101) (mk v S)
    have ht₀ := mn_native_exec_within hpeek 0
      (by simp [peekR,mnNativePushBound,mnActPush]) depth cap (by dsimp only [cap]; omega)
    have ht₁ : ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(2*M+integerIterationWorkspace C L w))
        depth (.loop (·.flag) (.seq (.act (popPush 101 100))
          (.seq (integerIteration hQ) (.act (peekR 101)))))
        (mk {v with flag := (S.R 101).head?.isSome} S) m₁ (mk v₁ S₁) :=
      (he₁ depth).mono (by
        intro d z hz
        change mnSize z+d ≤ mnSize (mk v S)+depth+2*M+integerIterationWorkspace C L w at hz
        omega)
    have ht₂ := mn_native_exec_within he₂ 1 (by
      simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]) depth cap (by
        have hh := ht₁.final
        rw [hlen]
        dsimp only [cap]
        omega)
    exact (ExecWithin.seq ht₀ (.seq (ht₁.mono (by intro d z hz; dsimp only [cap]; omega)) ht₂)).cast
      (by rw [hlen]) (congrArg (mk v₂) hstate)
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
