module

public import IntegerMultBounds.MathlibTM2.Routing.RowTransfer

/-! A fixed counted loop over routed rows. The one-step contract includes the
count advance and restores the reusable row bank; all remaining tapes are framed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def rowRoutingLoopBody (count : Fin T) (step : Pr P T Q A U) : Pr P T Q A U :=
  .seq step (.act (peekR count))

theorem rowRoutingLoop_exec (body : P → Pr P T Q A U)
    (count saved src output : Fin T) (hreg : [count, saved, src, output].Nodup)
    (effect : List (Fin (A + 4)) → List (Fin (A + 4)))
    (Ready : Stacks T A → Prop) (step : Pr P T Q A U) (price : ℝ)
    (rows : List (List (Fin (A + 4))))
    (hstep : ∀ xs ∈ rows, ∀ (c : Fin (A + 4)) cs rest (u : HS T Q A U) (B : Stacks T A),
      Ready B → B.R count = c :: cs → B.R src = xs ++ rest →
      let C : Stacks T A := { B with R := (Function.update (Function.update
        (Function.update (Function.update B.R count cs) saved (c :: B.R saved)) src rest)
        output ((effect xs).reverse ++ B.R output)) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ (m : ℝ) ≤ price ∧ Ready C ∧
        Exec body step (mk u B) m (mk u' C))
    (cs : List (Fin (A + 4))) (hcs : cs.length = rows.length)
    (tail : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : Ready S) (hcount : S.R count = cs)
    (hsrc : S.R src = rows.flatten ++ tail) (hflag : v.flag = cs.head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ rows.length * (price + 2) + 1 ∧
      Exec body (.loop (·.flag) (rowRoutingLoopBody count step)) (mk v S) steps
        (mk v' { S with R := (Function.update (Function.update
          (Function.update (Function.update S.R count []) saved (cs.reverse ++ S.R saved)) src tail)
          output ((rows.map effect).flatten.reverse ++ S.R output)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  induction rows generalizing cs v S with
  | nil =>
    have hc : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hcs)
    rw [hc] at hcount hflag ⊢
    have ht : S.R src = tail := by simpa using hsrc
    refine ⟨v, 1, rfl, by simp, ?_⟩
    convert Exec.loop_false (body := body)
      (p := rowRoutingLoopBody count step) (s := mk v S) (show v.flag = false by simpa using hflag) using 1
    congr 1
    congr 1
    funext r
    simp only [Function.update_apply, List.map_nil, List.flatten_nil, List.reverse_nil, List.nil_append]
    split_ifs <;> subst_vars <;> simp_all
  | cons xs rows ih =>
    cases cs with
    | nil => simp at hcs
    | cons c cs =>
      obtain ⟨v₁, m₁, hu₁, hm₁, hr₁, he₁⟩ := hstep xs (by simp) c cs
        (rows.flatten ++ tail) v S hready hcount
        (by simpa [List.flatten_cons, List.append_assoc] using hsrc)
      let C : Stacks T A := { S with R := (Function.update (Function.update
        (Function.update (Function.update S.R count cs) saved (c :: S.R saved)) src
        (rows.flatten ++ tail)) output ((effect xs).reverse ++ S.R output)) }
      have hc : C.R count = cs := by simp [C, ‹count ≠ output›, ‹count ≠ src›, ‹count ≠ saved›]
      have ht : C.R src = rows.flatten ++ tail := by simp [C, ‹src ≠ output›]
      let u := { v₁ with flag := cs.head?.isSome }
      have hp : (peekR count : Act T Q A U).run (mk v₁ C) = mk u C := by
        simp only [peekR_run, hc]; rfl
      obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ih
        (fun ys hy => hstep ys (by simp [hy])) cs (by simpa using hcs)
        u C hr₁ hc ht rfl
      have htrue : v.flag = true := by simpa using hflag
      refine ⟨v₂, (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_, ?_⟩
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hm₂ ⊢
        linarith only [hm₁, hm₂]
      · have he := Exec.loop_true htrue (Exec.seq he₁
          (hp ▸ Exec.act (body := body) (peekR count) (mk v₁ C))) he₂
        apply he.cast rfl
        congr 1
        congr 1
        funext r
        simp only [C, Function.update_apply]
        split_ifs <;> subst_vars <;>
          simp_all [List.map_cons, List.flatten_cons, List.reverse_append, List.reverse_cons,
            List.append_assoc]

/-- Run the counted row loop and restore both archives and the original counter. -/
def rowRoutingProgram (count saved src output : Fin T) (step : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR count)) (.seq (.loop (·.flag) (rowRoutingLoopBody count step))
    (rowRoutingRewind count saved src output))

theorem rowRoutingProgram_exec (body : P → Pr P T Q A U)
    (count saved src output : Fin T) (hreg : [count, saved, src, output].Nodup)
    (effect : List (Fin (A + 4)) → List (Fin (A + 4)))
    (Ready : Stacks T A → Prop) (step : Pr P T Q A U) (price : ℝ)
    (rows : List (List (Fin (A + 4))))
    (hstep : ∀ xs ∈ rows, ∀ (c : Fin (A + 4)) cs rest (u : HS T Q A U) (B : Stacks T A),
      Ready B → B.R count = c :: cs → B.R src = xs ++ rest →
      let C : Stacks T A := { B with R := (Function.update (Function.update
        (Function.update (Function.update B.R count cs) saved (c :: B.R saved)) src rest)
        output ((effect xs).reverse ++ B.R output)) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ (m : ℝ) ≤ price ∧ Ready C ∧
        Exec body step (mk u B) m (mk u' C))
    (cs : List (Fin (A + 4))) (hcs : cs.length = rows.length)
    (tail : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : Ready S) (hcount : S.R count = cs)
    (hsrc : S.R src = rows.flatten ++ tail)
    (hsaved : S.R saved = []) (houtput : S.R output = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ rows.length * (price + 4) +
        2 * ((rows.map effect).flatten.length : ℕ) + 6 ∧
      Exec body (rowRoutingProgram count saved src output step) (mk v S) steps
        (mk v' { S with R := Function.update S.R src ((rows.map effect).flatten ++ tail) }) := by
  have hreg' := hreg
  regs_ne hreg'
  let u := { v with flag := cs.head?.isSome }
  have hp : (peekR count : Act T Q A U).run (mk v S) = mk u S := by
    simp only [peekR_run, hcount]; rfl
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := rowRoutingLoop_exec body count saved src output hreg
    effect Ready step price rows hstep cs hcs tail u S hready hcount hsrc rfl
  let C : Stacks T A := { S with R := (Function.update (Function.update
    (Function.update (Function.update S.R count []) saved (cs.reverse ++ S.R saved)) src tail)
    output ((rows.map effect).flatten.reverse ++ S.R output)) }
  obtain ⟨v₂, hu₂, he₂⟩ := rowRoutingRewind_exec body count saved src output hreg cs
    (rows.map effect).flatten v₁ C
    (by simp [C, ‹count ≠ output›, ‹count ≠ src›, ‹count ≠ saved›])
    (by simp [C, ‹saved ≠ output›, ‹saved ≠ src›, hsaved])
    (by simp [C, houtput])
  have hf : ({ C with R := (Function.update (Function.update
      (Function.update (Function.update C.R saved []) count cs) output []) src
      ((rows.map effect).flatten ++ C.R src)) } : Stacks T A) =
      { S with R := Function.update S.R src ((rows.map effect).flatten ++ tail) } := by
    congr 1
    funext r
    simp only [C, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [hf] at he₂
  refine ⟨v₂, 1 + (m₁ + (2 * cs.length + 2 * (rows.map effect).flatten.length + 4)),
    hu₂.trans hu₁, ?_, Exec.seq (hp ▸ Exec.act (body := body) (peekR count) (mk v S))
      (Exec.seq he₁ he₂)⟩
  rw [hcs]
  push_cast at hm₁ ⊢
  linarith only [hm₁]

end IntegerMultBounds.MathlibTM2.Routing
