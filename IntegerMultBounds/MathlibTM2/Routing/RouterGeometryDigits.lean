module

public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometryDivisor
public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv

/-! Compute the common routing digit count and remainder from compact dimension,
stride and gap inputs. The divisor and numerator temporaries are erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerGeometryDivisorSlot : Fin 9 → Fin 14 := ![1,2,3,4,5,6,7,8,9]
theorem routerGeometryDivisorSlot_injective : Function.Injective routerGeometryDivisorSlot := by decide +kernel

def routerGeometryDigitsProgram (rg : Fin 14 → Fin T) : Pr P T Q A U :=
  .seq (routerGeometryDivisorProgram (rg ∘ routerGeometryDivisorSlot))
    (.seq (bsub (rg 0) (rg 1) (rg 10) (rg 6) (rg 7) (rg 8) (rg 9))
      (.seq (bdivmod (rg 10) (rg 5) (rg 11) (rg 12) (rg 3) (rg 4) (rg 13) (rg 6) (rg 7) (rg 8) (rg 9))
        (.seq (bclear (rg 5)) (bclear (rg 10)))))

theorem routerGeometryDigits_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg) (L n K G : ℕ)
    (hn : n < 2 ^ L) (hK : 0 < K) (hKn : K ≤ n) (hdivisor : K + 3 * G < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hstride : S.R (rg 1) = binSyms L K)
    (hgap : S.R (rg 2) = binSyms L G)
    (hblank : ∀ j : Fin 14, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 9 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 12 * L * L + 97 * L + 82 ∧
      Exec body (routerGeometryDigitsProgram rg) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R (rg 11)
          (binSyms L (routerDigits n K G))) (rg 12) (binSyms L ((n - K) % (K + 3 * G)))) }) := by
  have hdivBlank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 8 → S.R ((rg ∘ routerGeometryDivisorSlot) j) = [] := by
    intro j hj0 hj1 hj8
    fin_cases j <;> simp only [routerGeometryDivisorSlot, Function.comp_apply, Fin.isValue] <;>
      first | contradiction | (apply hblank <;> decide)
  obtain ⟨v₁, hu₁, he₁⟩ := routerGeometryDivisor_exec body (rg ∘ routerGeometryDivisorSlot)
    (hrg.comp routerGeometryDivisorSlot_injective) L K G hdivisor v S hstride hgap hdivBlank
  let C : Stacks T A := { S with R := Function.update S.R (rg 5) (binSyms L (K + 3 * G)) }
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := bsub_exec (body := body)
    (a := rg 0) (b := rg 1) (c := rg 10) (tx := rg 6) (ty := rg 7) (tz := rg 8) (cy := rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hn (hKn.trans_lt hn) v₁ C
    (by simp [C, hrg.eq_iff, hdimension]) (by simp [C, hrg.eq_iff, hstride])
    (by simp [C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 8 (by decide) (by decide) (by decide) (by decide)])
  have hsub : (n + 2 ^ L - K) % 2 ^ L = n - K := by
    rw [show n + 2 ^ L - K = (n - K) + 2 ^ L by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt ((Nat.sub_le n K).trans_lt hn)]
  have hc10 : C.R (rg 10) = [] := by simp [C, hrg.eq_iff, hblank 10 (by decide) (by decide) (by decide) (by decide)]
  rw [hsub, hc10, List.append_nil] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 10) (binSyms L (n - K)) }
  have keep (j : Fin 14) (hj5 : j ≠ 5) (hj10 : j ≠ 10) : D.R (rg j) = S.R (rg j) := by
    simp [D, C, hrg.eq_iff, hj5, hj10]
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := bdivmod_exec (body := body)
    (a := rg 10) (b := rg 5) (q := rg 11) (r := rg 12) (bw := rg 3) (rr := rg 4) (t := rg 13)
    (tx := rg 6) (ty := rg 7) (tz := rg 8) (cy := rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    ((Nat.sub_le n K).trans_lt hn) hdivisor (by omega : 0 < K + 3 * G) v₂ D
    (by simp [D]) (by simp [D, C, hrg.eq_iff])
    ((keep 3 (by decide) (by decide)).trans (hblank 3 (by decide) (by decide) (by decide) (by decide)))
    ((keep 4 (by decide) (by decide)).trans (hblank 4 (by decide) (by decide) (by decide) (by decide)))
    ((keep 13 (by decide) (by decide)).trans (hblank 13 (by decide) (by decide) (by decide) (by decide)))
    ((keep 6 (by decide) (by decide)).trans (hblank 6 (by decide) (by decide) (by decide) (by decide)))
    ((keep 7 (by decide) (by decide)).trans (hblank 7 (by decide) (by decide) (by decide) (by decide)))
    ((keep 8 (by decide) (by decide)).trans (hblank 8 (by decide) (by decide) (by decide) (by decide)))
  rw [(keep 11 (by decide) (by decide)).trans (hblank 11 (by decide) (by decide) (by decide) (by decide)),
    (keep 12 (by decide) (by decide)).trans (hblank 12 (by decide) (by decide) (by decide) (by decide)), List.append_nil] at he₃
  simp only [List.append_nil] at he₃
  let E : Stacks T A := { D with R := (Function.update (Function.update D.R (rg 11)
    (binSyms L ((n - K) / (K + 3 * G)))) (rg 12) (binSyms L ((n - K) % (K + 3 * G)))) }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec (body := body) (rg 5) v₃ E
  have hlen5 : (E.R (rg 5)).length = L := by simp [E, D, C, hrg.eq_iff, length_binSyms]
  rw [hlen5] at he₄
  let F : Stacks T A := { E with R := Function.update E.R (rg 5) [] }
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec (body := body) (rg 10) v₄ F
  have hlen10 : (F.R (rg 10)).length = L := by simp [F, E, D, C, hrg.eq_iff, length_binSyms]
  have hfinal : ({ F with R := Function.update F.R (rg 10) [] } : Stacks T A) =
      { S with R := (Function.update (Function.update S.R (rg 11) (binSyms L (routerDigits n K G)))
        (rg 12) (binSyms L ((n - K) % (K + 3 * G)))) } := by
    congr 1
    funext x
    by_cases h5 : x = rg 5
    · subst x; simp [F, E, D, C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide) (by decide)]
    · by_cases h10 : x = rg 10
      · subst x; simp [hrg.eq_iff, hblank 10 (by decide) (by decide) (by decide) (by decide)]
      · by_cases h11 : x = rg 11 <;> by_cases h12 : x = rg 12 <;>
          simp [F, E, D, C, h5, h10, h11, h12, hrg.eq_iff, routerDigits]
  rw [hlen10, hfinal] at he₅
  refine ⟨v₅, (30 * L + 34) + ((8 * L + 8) + (m₃ + ((2 * L + 2) + (2 * L + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩
  nlinarith only [hm₃]

end IntegerMultBounds.MathlibTM2.Routing
