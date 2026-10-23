module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! One live table lookup comparison: copy the mate only at the requested
coordinate, preserving the row, query and all arithmetic scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingLookupCallProgram (rg : Fin 7 → Fin T) (out : Fin T) : Pr P T Q A U :=
  .seq (beq (rg 0) (rg 2) (rg 3) (rg 4) (rg 5) (rg 6))
    (.cond (fun v => symBit (v.scan (rg 6))) (bcopy (rg 1) out (rg 3) (rg 4)) (.act .done))

theorem matchingLookupCall_exec (body : P → Pr P T Q A U)
    (rg : Fin 7 → Fin T) (hrg : Function.Injective rg) (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (L q mate query : ℕ) (hq : q < 2 ^ L) (hquery : query < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hcoordinate : S.R (rg 0) = binSyms L q) (hmate : S.R (rg 1) = binSyms L mate)
    (hrequest : S.R (rg 2) = binSyms L query)
    (hblank : ∀ j : Fin 7, j = 3 ∨ j = 4 ∨ j = 5 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 14 * L + 15 ∧
      Exec body (matchingLookupCallProgram rg out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out ((if q = query then binSyms L mate else []) ++ S.R out) }) := by
  obtain ⟨v₁, hu₁, hscan, _, he₁⟩ := beq_exec body
    (a := rg 0) (b := rg 2) (tx := rg 3) (ty := rg 4) (tz := rg 5) (cy := rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    hq hquery v S hcoordinate hrequest (hblank 3 (by simp)) (hblank 4 (by simp)) (hblank 5 (by simp))
  by_cases h : q = query
  · obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec body (a := rg 1) (c := out) (t₁ := rg 3) (t₂ := rg 4)
      (by simp [List.nodup_cons, hrg.eq_iff, hout, ne_comm]) v₁ S (hblank 3 (by simp)) (hblank 4 (by simp))
    rw [hmate, length_binSyms] at he₂
    refine ⟨v₂, (8 * L + 8) + ((6 * L + 6) + 1), hu₂.trans hu₁, by omega, ?_⟩
    simp only [h, ite_true]
    exact Exec.seq he₁ (Exec.cond_true (by simp [mk_var, hscan, h]) he₂)
  · refine ⟨v₁, (8 * L + 8) + (1 + 1), hu₁, by omega, ?_⟩
    simp only [h, ite_false, List.nil_append, Function.update_eq_self]
    exact Exec.seq he₁ (Exec.cond_false (by simp [mk_var, hscan, h]) (Exec.act (body := body) .done (mk v₁ S)))

end IntegerMultBounds.MathlibTM2.Routing
