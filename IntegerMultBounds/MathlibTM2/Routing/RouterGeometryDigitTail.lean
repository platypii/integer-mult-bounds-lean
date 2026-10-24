module

public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometryDigits

/-! Generate the routing digit count and terminal tail from compact inputs.
The division remainder is consumed by the tail addition and then erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerGeometryDigitsSlot : Fin 14 → Fin 15 := Fin.castSucc
theorem routerGeometryDigitsSlot_injective : Function.Injective routerGeometryDigitsSlot := by decide +kernel

def routerGeometryDigitTailProgram (rg : Fin 15 → Fin T) : Pr P T Q A U :=
  .seq (routerGeometryDigitsProgram (rg ∘ routerGeometryDigitsSlot))
    (.seq (badd (rg 1) (rg 12) (rg 14) (rg 6) (rg 7) (rg 8) (rg 9)) (bclear (rg 12)))

theorem routerGeometryDigitTail_exec (body : P → Pr P T Q A U)
    (rg : Fin 15 → Fin T) (hrg : Function.Injective rg) (L n K G : ℕ)
    (hn : n < 2 ^ L) (hK : 0 < K) (hKn : K ≤ n) (hdivisor : K + 3 * G < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hstride : S.R (rg 1) = binSyms L K)
    (hgap : S.R (rg 2) = binSyms L G)
    (hblank : ∀ j : Fin 15, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 9 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 12 * L * L + 107 * L + 92 ∧
      Exec body (routerGeometryDigitTailProgram rg) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R (rg 11)
          (binSyms L (routerDigits n K G))) (rg 14) (binSyms L (routerTail n K G))) }) := by
  let small := rg ∘ routerGeometryDigitsSlot
  have hs : Function.Injective small := hrg.comp routerGeometryDigitsSlot_injective
  have hsmallBlank : ∀ j : Fin 14, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 9 → S.R (small j) = [] := by
    intro j hj0 hj1 hj2 hj9
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 15 => a.val) he))
    · exact fun he => hj1 (Fin.ext (congrArg (fun a : Fin 15 => a.val) he))
    · exact fun he => hj2 (Fin.ext (congrArg (fun a : Fin 15 => a.val) he))
    · exact fun he => hj9 (Fin.ext (congrArg (fun a : Fin 15 => a.val) he))
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := routerGeometryDigits_exec body small hs L n K G hn hK hKn hdivisor
    v S hdimension hstride hgap hsmallBlank
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R (rg 11)
    (binSyms L (routerDigits n K G))) (rg 12) (binSyms L ((n - K) % (K + 3 * G)))) }
  have htail : K + (n - K) % (K + 3 * G) ≤ n := by
    have he := routerGeometry_decomposition n K G hKn
    omega
  have keep (j : Fin 15) (hj11 : j ≠ 11) (hj12 : j ≠ 12) : C.R (rg j) = S.R (rg j) := by
    simp [C, hrg.eq_iff, hj11, hj12]
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := badd_exec (body := body)
    (a := rg 1) (b := rg 12) (c := rg 14) (tx := rg 6) (ty := rg 7) (tz := rg 8) (cy := rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (hKn.trans_lt hn) (by omega : (n - K) % (K + 3 * G) < 2 ^ L) v₁ C
    ((keep 1 (by decide) (by decide)).trans hstride) (by simp [C])
    ((keep 6 (by decide) (by decide)).trans (hblank 6 (by decide) (by decide) (by decide) (by decide)))
    ((keep 7 (by decide) (by decide)).trans (hblank 7 (by decide) (by decide) (by decide) (by decide)))
    ((keep 8 (by decide) (by decide)).trans (hblank 8 (by decide) (by decide) (by decide) (by decide)))
  have hc14 : C.R (rg 14) = [] := (keep 14 (by decide) (by decide)).trans
    (hblank 14 (by decide) (by decide) (by decide) (by decide))
  rw [Nat.mod_eq_of_lt (htail.trans_lt hn), ← routerTail_eq n K G hKn, hc14, List.append_nil] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 14) (binSyms L (routerTail n K G)) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (rg 12) v₂ D
  have hlen : (D.R (rg 12)).length = L := by simp [D, C, hrg.eq_iff, length_binSyms]
  have hfinal : ({ D with R := Function.update D.R (rg 12) [] } : Stacks T A) =
      { S with R := (Function.update (Function.update S.R (rg 11) (binSyms L (routerDigits n K G)))
        (rg 14) (binSyms L (routerTail n K G))) } := by
    congr 1
    funext x
    by_cases h12 : x = rg 12
    · subst x; simp [hrg.eq_iff, hblank 12 (by decide) (by decide) (by decide) (by decide)]
    · by_cases h11 : x = rg 11 <;> by_cases h14 : x = rg 14 <;>
        simp [D, C, h12, h11, h14, hrg.eq_iff]
  rw [hlen, hfinal] at he₃
  exact ⟨v₃, m₁ + ((8 * L + 8) + (2 * L + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
