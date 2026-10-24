module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationOrbitStep

/-! Advance toward a fixed orbit target and append one unary step marker.
Once the query reaches the target, further iterations leave all registers alone. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
variable {N T Q A : ℕ} {P U : Type}

def permutationReturnStepProgram (rg : Fin 10 → Fin T) (out target steps : Fin T) : Pr P T Q A U :=
  .seq (beq (rg 2) target (rg 3) (rg 4) (rg 5) (rg 6))
    (.cond (fun v => symBit (v.scan (rg 6))) (.act .done)
      (.seq (matchingTableLookupInPlaceProgram rg out)
        (.act (Action.push (.rt steps) (fun _ => tick) .done))))

def permutationReturnStepBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 10 → Fin T)
    (steps : Fin T) (L : ℕ) (f : Fin N → Fin N) (query target : Fin N) :
    Fin T → List (Fin (A + 4)) :=
  if query = target then R else Function.update
    (Function.update R (rg 2) (binSyms L (f query).val)) steps (tick :: R steps)

theorem permutationReturnStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (out target steps : Fin T)
    (hout : ∀ j, out ≠ rg j) (htarget : ∀ j, target ≠ rg j) (hsteps : ∀ j, steps ≠ rg j)
    (L : ℕ) (hN : N ≤ 2 ^ L) (f : Fin N → Fin N) (query goal : Fin N)
    (v : HS T Q A U) (S : Stacks T A) (ready : MatchingLookupReady rg L query S)
    (htable : S.R (rg 7) = matchingEntryWords L (matchingTableEntries N (matchingMateCoordinate f)))
    (htableSaved : S.R (rg 8) = []) (houtput : S.R out = [])
    (hgoal : S.R target = binSyms L goal.val) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ N * (30 * L + 39) + 18 * L + 24 ∧
      Exec body (permutationReturnStepProgram rg out target steps) (mk v S) m
        (mk v' { S with R := permutationReturnStepBank S.R rg steps L f query goal }) := by
  obtain ⟨v₁, hu₁, hscan, _, he₁⟩ := beq_exec (body := body)
    (a := rg 2) (b := target) (tx := rg 3) (ty := rg 4) (tz := rg 5) (cy := rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff, htarget, ne_comm])
    (hrg.ne (by decide)) (htarget 6).symm
    (query.isLt.trans_le hN) (goal.isLt.trans_le hN) v S ready.request hgoal
    (ready.blank 3 (by simp)) (ready.blank 4 (by simp)) (ready.blank 5 (by simp))
  by_cases h : query = goal
  · have hv : query.val = goal.val := congrArg Fin.val h
    refine ⟨v₁, (8 * L + 8) + (1 + 1), hu₁, by omega, ?_⟩
    simp only [permutationReturnStepBank, h, ite_true]
    exact Exec.seq he₁ (Exec.cond_true (by simp [mk_var, hscan, hv]) (Exec.act (body := body) .done (mk v₁ S)))
  · have hv : query.val ≠ goal.val := fun he => h (Fin.ext he)
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := matchingTableLookupInPlace_exec body rg hrg out hout L hN f query
      v₁ S ready htable htableSaved houtput
    let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (f query).val) }
    have hp : (Action.push (.rt steps) (fun _ => tick) .done : Act T Q A U).run (mk v₂ C) =
        mk v₂ { S with R := permutationReturnStepBank S.R rg steps L f query goal } := by
      simp [Action.run, update_rt, permutationReturnStepBank, h, C, hsteps 2]
    exact ⟨v₂, (8 * L + 8) + (m₂ + 1 + 1), hu₂.trans hu₁, by omega,
      Exec.seq he₁ (Exec.cond_false (by simp [mk_var, hscan, hv])
        (Exec.seq he₂ (hp ▸ Exec.act (body := body) _ (mk v₂ C))))⟩

end IntegerMultBounds.MathlibTM2.Routing
