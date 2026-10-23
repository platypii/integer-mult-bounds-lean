module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCall

/-! A fixed call loop over framed metadata. Each iteration restores its reusable
bank; only the input cursor, rewind archive and routed stream advance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U I : Type}

def delimitedScheduleInput (frame : I → List (Fin (A + 4))) : List I → List (Fin (A + 4))
  | [] => []
  | i :: is => frame i ++ delimitedScheduleInput frame is

def delimitedCallAdvanced (R : Fin T → List (Fin (A + 4))) (src saved str : Fin T)
    (frame rest output : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R src rest) saved (frame.reverse ++ R saved)) str output

def delimitedScheduleBank (src saved str : Fin T) (frame : I → List (Fin (A + 4)))
    (effect : I → List (Fin (A + 4)) → List (Fin (A + 4))) :
    List I → (Fin T → List (Fin (A + 4))) → Fin T → List (Fin (A + 4))
  | [], R => R
  | i :: is, R => delimitedScheduleBank src saved str frame effect is
      (delimitedCallAdvanced R src saved str (frame i) (delimitedScheduleInput frame is) (effect i (R str)))

def delimitedCallLoopBody (src : Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq call (.act (peekR src))

def delimitedSchedulePrice (price : I → ℝ) : List I → ℝ
  | [] => 1
  | i :: is => price i + 2 + delimitedSchedulePrice price is

/-- Sum call costs and charge one common overhead per actual loop iteration. -/
theorem delimitedSchedulePrice_le (price base : I → ℝ) (C : ℕ) (stages : List I)
    (hprice : ∀ i ∈ stages, price i ≤ base i + C) :
    delimitedSchedulePrice price stages ≤ (stages.map base).sum + (stages.length * (C + 2) + 1 : ℕ) := by
  induction stages with
  | nil => simp [delimitedSchedulePrice]
  | cons i stages ih =>
    have hi := hprice i (by simp)
    have ht := ih (fun j hj => hprice j (by simp [hj]))
    simp only [delimitedSchedulePrice, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    push_cast at hi ht ⊢
    linarith

/-- The schedule input is the concatenation of its bounded frames. -/
theorem delimitedScheduleInput_length_le (frame : I → List (Fin (A + 4))) (F : ℕ) (stages : List I)
    (hframe : ∀ i ∈ stages, (frame i).length ≤ F) :
    (delimitedScheduleInput frame stages).length ≤ stages.length * F := by
  induction stages with
  | nil => simp [delimitedScheduleInput]
  | cons i stages ih =>
    have hi := hframe i (by simp)
    have ht := ih (fun j hj => hframe j (by simp [hj]))
    simp only [delimitedScheduleInput, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Lift a priced, invariant-preserving one-call execution theorem to a uniform
loop. Neither the code nor its register bank depends on the number of calls. -/
theorem delimitedCallLoop_exec (body : P → Pr P T Q A U)
    (src saved str : Fin T) (hsa : src ≠ saved) (hss : src ≠ str)
    (frame : I → List (Fin (A + 4)))
    (effect : I → List (Fin (A + 4)) → List (Fin (A + 4))) (price : I → ℝ)
    (Ready : Stacks T A → Prop) (call : Pr P T Q A U) (stages : List I)
    (hnonempty : ∀ i ∈ stages, frame i ≠ [])
    (hstep : ∀ i ∈ stages, ∀ (rest : List (Fin (A + 4))) (u : HS T Q A U) (B : Stacks T A),
      Ready B → B.R src = frame i ++ rest →
      let C : Stacks T A := { B with R := delimitedCallAdvanced B.R src saved str (frame i) rest (effect i (B.R str)) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ (m : ℝ) ≤ price i ∧ Ready C ∧
        Exec body call (mk u B) m (mk u' C))
    (v : HS T Q A U) (S : Stacks T A) (hready : Ready S)
    (hsrc : S.R src = delimitedScheduleInput frame stages)
    (hflag : v.flag = (S.R src).head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice price stages ∧
      Ready { S with R := delimitedScheduleBank src saved str frame effect stages S.R } ∧
      Exec body (.loop (·.flag) (delimitedCallLoopBody src call)) (mk v S) steps
        (mk v' { S with R := delimitedScheduleBank src saved str frame effect stages S.R }) := by
  induction stages generalizing v S with
  | nil =>
    refine ⟨v, 1, rfl, by simp [delimitedSchedulePrice], hready, ?_⟩
    exact Exec.loop_false (by simpa only [hsrc, delimitedScheduleInput, List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons i is ih =>
    let rest := delimitedScheduleInput frame is
    obtain ⟨v₁, m₁, hu₁, hm₁, hr₁, hx₁⟩ := hstep i (by simp) rest v S hready hsrc
    let C : Stacks T A := { S with R := delimitedCallAdvanced S.R src saved str (frame i) rest (effect i (S.R str)) }
    have hc : C.R src = rest := by simp [C, delimitedCallAdvanced, hsa, hss]
    let u := { v₁ with flag := rest.head?.isSome }
    have hp : (peekR src : Act T Q A U).run (mk v₁ C) = mk u C := by
      simp only [peekR_run, hc]; rfl
    obtain ⟨v₂, m₂, hu₂, hm₂, hr₂, hx₂⟩ := ih
      (fun j hj => hnonempty j (by simp [hj])) (fun j hj => hstep j (by simp [hj]))
      u C hr₁ hc (by simp only [u, hc])
    have htrue : v.flag = true := by
      rw [hflag, hsrc]
      cases hf : frame i with
      | nil => exact (hnonempty i (by simp) hf).elim
      | cons a as => simp [delimitedScheduleInput, hf]
    refine ⟨v₂, (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_, hr₂, ?_⟩
    · dsimp only [delimitedSchedulePrice]
      push_cast
      linarith
    · exact Exec.loop_true (by simpa only [mk_var] using htrue)
        (Exec.seq hx₁ (hp ▸ Exec.act (body := body) (peekR src) (mk v₁ C))) hx₂

end IntegerMultBounds.MathlibTM2.Routing
