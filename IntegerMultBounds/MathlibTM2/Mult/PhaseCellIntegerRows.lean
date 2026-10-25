module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowContext

/-! # Execute a finite list of integer generator rows

The existing unary program scanner drives the actual row call. It restores
the original count symbols, consumes owned factor/RHS prefixes, and reuses
one borrowed column and one installed readiness bank throughout the loop.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def integerRowResult (xs : List GaussianInt) (job : List GaussianInt × GaussianInt) : GaussianInt :=
  job.2 - (List.zipWith (· * ·) xs job.1).sum

noncomputable def integerRows (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  scanP 103 108 (consumeIntegerRow hQ)

private theorem integerRows_loop (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L w : ℕ} (xs : List GaussianInt) (tailX tailA tailR : List (Fin (A + 4)))
    (jobs : List (List GaussianInt × GaussianInt)) :
    ∀ (cs : List (Fin (A + 4))) (v : HS 117 Q A U) (S : Stacks 117 A),
    cs.length = jobs.length → IntegerRowContext L w xs tailX S →
    (∀ job ∈ jobs, job.1.length = L ∧ ∀ a ∈ job.1, Fits w a ∧ a.im = 0) →
    S.R 103 = cs → S.R 111 = cstream A w (jobs.flatMap Prod.fst) ++ tailA →
    S.R 112 = cstream A w (jobs.map Prod.snd) ++ tailR → v.flag = (S.R 103).head?.isSome →
    ∃ v' m, v'.user = v.user ∧ m ≤ jobs.length * (integerRowCost L w + 3) + 1 ∧
      Exec body (.loop (·.flag) (.seq (.act (popPush 103 108))
        (.seq (consumeIntegerRow hQ) (.act (peekR 103))))) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update S.R 103 []) 108 (cs.reverse ++ S.R 108)) 111 tailA) 112 tailR) 113
            (cstream A w ((jobs.map (integerRowResult xs)).reverse) ++ S.R 113)) }) := by
  induction jobs with
  | nil =>
    intro cs v S hlen hctx hjobs hcs ha hr hf
    have hcs0 : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst cs
    have ha0 : S.R 111 = tailA := by simpa [cstream] using ha
    have hr0 : S.R 112 = tailR := by simpa [cstream] using hr
    refine ⟨v, 1, rfl, by simp, ?_⟩
    have hstate : ({ S with R := (Function.update (Function.update (Function.update (Function.update
        (Function.update S.R 103 []) 108 (([] : List (Fin (A + 4))).reverse ++ S.R 108)) 111 tailA)
          112 tailR) 113 (cstream A w (([] : List (List GaussianInt × GaussianInt)).map
            (integerRowResult xs)).reverse ++ S.R 113)) } : Stacks 117 A) = S := by
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      simp only [List.reverse_nil, List.nil_append, List.map_nil, cstream, List.flatMap_nil,
        Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    rw [hcs0, hstate]
    exact Exec.loop_false (s := mk v S) (f := fun v : HS 117 Q A U => v.flag)
      (by simpa [hcs0] using hf)
  | cons job jobs ih =>
    intro cs v S hlen hctx hjobs hcs ha hr hf
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have hlen' : cs.length = jobs.length := by simpa using hlen
      have hj := hjobs job (by simp)
      let S₀ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 103 cs) 108 (c :: S.R 108)) }
      let v₀ : HS 117 Q A U := { v with sym := some c }
      have hpop : (popPush 103 108 : Act 117 Q A U).run (mk v S) = mk v₀ S₀ := by
        simp [popPush, Action.run, hcs, update_rt, S₀, v₀]
      have hctx₀ : IntegerRowContext L w xs tailX S₀ :=
        (hctx.update 103 (by simp) cs).update 108 (by simp) (c :: S.R 108)
      let restA := cstream A w (jobs.flatMap Prod.fst) ++ tailA
      let restR := cstream A w (jobs.map Prod.snd) ++ tailR
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := consumeIntegerRow_exec (body := body) hQ hA hctx₀.width_pos
        xs job.1 job.2 hctx₀.length hj.1 hctx₀.fits hj.2 v₀ S₀ tailX restA restR hctx₀.rows hctx₀.width
        hctx₀.column (by simpa [S₀, restA, cstream, List.append_assoc] using ha)
        (by simpa [S₀, restR, cstream, List.append_assoc] using hr) hctx₀.clean hctx₀.ready hctx₀.work
      let word := csyms A w (integerRowResult xs job)
      let S₁ : Stacks 117 A := { S₀ with R := (Function.update (Function.update (Function.update S₀.R
        111 restA) 112 restR) 113 (word ++ S₀.R 113)) }
      have hctx₁ : IntegerRowContext L w xs tailX S₁ :=
        ((hctx₀.update 111 (by simp) restA).update 112 (by simp) restR).update 113 (by simp)
          (word ++ S₀.R 113)
      have he₂ := Exec.act (body := body) (peekR 103) (mk v₁ S₁)
      rw [peekR_run] at he₂
      obtain ⟨v₂, m₂, hu₂, hm₂, he₃⟩ := ih cs { v₁ with flag := (S₁.R 103).head?.isSome } S₁
        hlen' hctx₁ (fun j hj => hjobs j (by simp [hj]))
        (by simp [S₁, S₀]) (by simp [S₁, restA]) (by simp [S₁, restR]) rfl
      refine ⟨v₂, 1 + (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_,
        (Exec.loop_true (by simpa [hcs] using hf)
          (Exec.seq (hpop ▸ Exec.act (body := body) (popPush 103 108) (mk v S))
            (Exec.seq he₁ he₂)) he₃).cast rfl ?_⟩
      · simp only [List.length_cons]
        nlinarith only [hm₁, hm₂]
      · congr 1
        ext1
        · rfl
        · rfl
        · rfl
        funext k
        by_cases hc : k = 103
        · subst k; simp
        by_cases hs : k = 108
        · subst k; simp [S₁, S₀, List.reverse_cons, List.append_assoc]
        by_cases ha' : k = 111
        · subst k; simp
        by_cases hr' : k = 112
        · subst k; simp
        by_cases ho : k = 113
        · subst k
          simp [S₁, S₀, word, cstream, List.reverse_cons, List.append_assoc]
        simp [S₁, S₀, hc, hs, ha', hr', ho]

/-- A dimension-independent row loop with exact borrowed-column, counter,
workspace and suffix restoration. Results are prepended in reverse row order. -/
theorem integerRows_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A) {L w : ℕ}
    (xs : List GaussianInt) (jobs : List (List GaussianInt × GaussianInt))
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A + 4)))
    (hctx : IntegerRowContext L w xs tailX S)
    (hjobs : ∀ job ∈ jobs, job.1.length = L ∧ ∀ a ∈ job.1, Fits w a ∧ a.im = 0)
    (hcount : (S.R 103).length = jobs.length) (hsaved : S.R 108 = [])
    (ha : S.R 111 = cstream A w (jobs.flatMap Prod.fst) ++ tailA)
    (hr : S.R 112 = cstream A w (jobs.map Prod.snd) ++ tailR) :
    ∃ v' m, v'.user = v.user ∧ m ≤ jobs.length * (integerRowCost L w + 5) + 4 ∧
      Exec body (integerRows hQ) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 111 tailA) 112 tailR)
          113 (cstream A w ((jobs.map (integerRowResult xs)).reverse) ++ S.R 113)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := integerRows_loop (body := body) hQ hA xs tailX tailA tailR jobs
    (S.R 103) { v with flag := (S.R 103).head?.isSome } S hcount hctx hjobs rfl ha hr rfl
  let result := cstream A w ((jobs.map (integerRowResult xs)).reverse) ++ S.R 113
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update (Function.update (Function.update
    (Function.update S.R 103 []) 108 ((S.R 103).reverse ++ S.R 108)) 111 tailA) 112 tailR) 113 result) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body 108 103 (by decide) id v₁ S₁
  have hlen : (S₁.R 108).length = jobs.length := by simp [S₁, hsaved, hcount]
  refine ⟨v₂, 1 + (m₁ + (2 * jobs.length + 2)), hu₂.trans hu₁, ?_, ?_⟩
  · nlinarith only [hm₁]
  · refine (Exec.seq (peekR_run 103 v S ▸ Exec.act (body := body) (peekR 103) (mk v S))
      (Exec.seq he₁ he₂)).cast (by rw [hlen]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hc : k = 103
    · subst k; simp [S₁, movedR, hsaved]
    by_cases hs : k = 108
    · subst k; simp [S₁, movedR, hsaved]
    simp [S₁, movedR, Function.update_apply, hc, hs, result]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
