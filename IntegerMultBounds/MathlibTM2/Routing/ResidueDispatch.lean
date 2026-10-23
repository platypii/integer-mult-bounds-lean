module

public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv

/-! Test a live coordinate's residue with executed division and comparison.
Both arithmetic outputs and all scratch restore before the chosen branch runs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def residueDispatchProgram (rg : Fin 12 → Fin T) (branch : Bool → Pr P T Q A U) : Pr P T Q A U :=
  .seq (bdivmod (rg 0) (rg 1) (rg 2) (rg 3) (rg 4) (rg 5) (rg 6) (rg 7) (rg 8) (rg 9) (rg 10))
    (.seq (beq (rg 3) (rg 11) (rg 7) (rg 8) (rg 9) (rg 10))
      (.seq (bclear (rg 2)) (.seq (bclear (rg 3))
        (.cond (fun v => symBit (v.scan (rg 10))) (branch true) (branch false)))))

def residueDispatchCost (L Lk : ℕ) := L * (12 * Lk + 35) + 2 * L + 30 * Lk + 49

theorem residueDispatch_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (branch : Bool → Pr P T Q A U)
    (L Lk q k r C : ℕ) (hq : q < 2 ^ L) (hk : k < 2 ^ Lk) (hk0 : 0 < k) (hr : r < 2 ^ Lk)
    (v : HS T Q A U) (S S' : Stacks T A)
    (hcoordinate : S.R (rg 0) = binSyms L q) (hstride : S.R (rg 1) = binSyms Lk k)
    (hresidue : S.R (rg 11) = binSyms Lk r)
    (hblank : ∀ j : Fin 12, 2 ≤ j.val → j.val < 10 → S.R (rg j) = [])
    (hbranch : ∀ u : HS T Q A U, ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ steps ≤ C ∧
      Exec body (branch (decide (q % k = r))) (mk u S) steps (mk u' S')) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ residueDispatchCost L Lk + C ∧
      Exec body (residueDispatchProgram rg branch) (mk v S) steps (mk v' S') := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := bdivmod_exec body
    (a := rg 0) (b := rg 1) (q := rg 2) (r := rg 3) (bw := rg 4) (rr := rg 5) (t := rg 6)
    (tx := rg 7) (ty := rg 8) (tz := rg 9) (cy := rg 10)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    hq hk hk0 v S hcoordinate hstride
    (hblank 4 (by decide) (by decide)) (hblank 5 (by decide) (by decide))
    (hblank 6 (by decide) (by decide)) (hblank 7 (by decide) (by decide))
    (hblank 8 (by decide) (by decide)) (hblank 9 (by decide) (by decide))
  rw [hblank 2 (by decide) (by decide), hblank 3 (by decide) (by decide), List.append_nil, List.append_nil] at he₁
  let G : Stacks T A := { S with R := Function.update (Function.update S.R (rg 2) (binSyms L (q / k))) (rg 3) (binSyms Lk (q % k)) }
  obtain ⟨v₂, hu₂, hscan₂, _, he₂⟩ := beq_exec body
    (a := rg 3) (b := rg 11) (tx := rg 7) (ty := rg 8) (tz := rg 9) (cy := rg 10)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    ((Nat.mod_lt q hk0).trans hk) hr v₁ G (by simp [G])
    (by simpa [G, hrg.eq_iff] using hresidue)
    (by simpa [G, hrg.eq_iff] using hblank 7 (by decide) (by decide))
    (by simpa [G, hrg.eq_iff] using hblank 8 (by decide) (by decide))
    (by simpa [G, hrg.eq_iff] using hblank 9 (by decide) (by decide))
  obtain ⟨v₃, hu₃, hscan₃, he₃⟩ := bclear_exec body (rg 2) v₂ G
  let H : Stacks T A := { G with R := Function.update G.R (rg 2) [] }
  obtain ⟨v₄, hu₄, hscan₄, he₄⟩ := bclear_exec body (rg 3) v₃ H
  have h2 : (G.R (rg 2)).length = L := by simp [G, hrg.eq_iff]
  have h3 : (H.R (rg 3)).length = Lk := by simp [H, G, hrg.eq_iff]
  have hf : Function.update H.R (rg 3) [] = S.R := by
    funext j
    by_cases h3 : j = rg 3
    · subst j; simp [hblank 3 (by decide) (by decide)]
    by_cases h2 : j = rg 2
    · subst j; simp [H, G, h3, hblank 2 (by decide) (by decide)]
    · simp [H, G, h3, h2]
  rw [h2] at he₃
  rw [h3, hf] at he₄
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := hbranch v₄
  have hc : v₄.scan (rg 10) = bitSymbol (decide (q % k = r)) := by rw [hscan₄, hscan₃, hscan₂]
  have hcond : Exec body (.cond (fun v => symBit (v.scan (rg 10))) (branch true) (branch false))
      (mk v₄ S) (m₅ + 1) (mk v₅ S') := by
    by_cases h : q % k = r
    · simp only [h, decide_true] at he₅
      exact Exec.cond_true (by simp [mk_var, hc, h]) he₅
    · simp only [h, decide_false] at he₅
      exact Exec.cond_false (by simp [mk_var, hc, h]) he₅
  exact ⟨v₅, m₁ + ((8 * Lk + 8) + ((2 * L + 2) + ((2 * Lk + 2) + (m₅ + 1)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by unfold residueDispatchCost; omega,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ hcond)))⟩

end IntegerMultBounds.MathlibTM2.Routing
