module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFixedScale
public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometry

/-! Generate `K + 3*G`, the routing digit divisor, from two binary inputs.
Double/triple temporaries are erased and only the divisor output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerGeometryDivisorProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (binaryDoubleCopyProgram (rg 1) (rg 2) (rg 5) (rg 6))
    (.seq (badd (rg 1) (rg 2) (rg 3) (rg 5) (rg 6) (rg 7) (rg 8))
      (.seq (badd (rg 0) (rg 3) (rg 4) (rg 5) (rg 6) (rg 7) (rg 8))
        (.seq (bclear (rg 2)) (bclear (rg 3)))))

theorem routerGeometryDivisor_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (L K G : ℕ)
    (hfit : K + 3 * G < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hstride : S.R (rg 0) = binSyms L K) (hgap : S.R (rg 1) = binSyms L G)
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 8 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (routerGeometryDivisorProgram rg) (mk v S) (30 * L + 34)
        (mk v' { S with R := Function.update S.R (rg 4) (binSyms L (K + 3 * G)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := binaryDoubleCopy_exec body (rg 1) (rg 2) (rg 5) (rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) L G v S hgap
    (hblank 2 (by decide) (by decide) (by decide)) (hblank 5 (by decide) (by decide) (by decide))
    (hblank 6 (by decide) (by decide) (by decide))
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (2 * G)) }
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := badd_exec (body := body)
    (a := rg 1) (b := rg 2) (c := rg 3) (tx := rg 5) (ty := rg 6) (tz := rg 7) (cy := rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : G < 2 ^ L) (by omega : 2 * G < 2 ^ L) v₁ C
    (by simp [C, hrg.eq_iff, hgap]) (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
  have hc3 : C.R (rg 3) = [] := by simp [C, hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide)]
  rw [show G + 2 * G = 3 * G by omega, Nat.mod_eq_of_lt (by omega : 3 * G < 2 ^ L), hc3, List.append_nil] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 3) (binSyms L (3 * G)) }
  obtain ⟨v₃, hu₃, _, _, he₃⟩ := badd_exec (body := body)
    (a := rg 0) (b := rg 3) (c := rg 4) (tx := rg 5) (ty := rg 6) (tz := rg 7) (cy := rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : K < 2 ^ L) (by omega : 3 * G < 2 ^ L) v₂ D
    (by simp [D, C, hrg.eq_iff, hstride]) (by simp [D])
    (by simp [D, C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
  have hd4 : D.R (rg 4) = [] := by simp [D, C, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide)]
  rw [Nat.mod_eq_of_lt hfit, hd4, List.append_nil] at he₃
  let E : Stacks T A := { D with R := Function.update D.R (rg 4) (binSyms L (K + 3 * G)) }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec (body := body) (rg 2) v₃ E
  have hlen2 : (E.R (rg 2)).length = L := by simp [E, D, C, hrg.eq_iff, length_binSyms]
  rw [hlen2] at he₄
  let F : Stacks T A := { E with R := Function.update E.R (rg 2) [] }
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec (body := body) (rg 3) v₄ F
  have hlen3 : (F.R (rg 3)).length = L := by simp [F, E, D, C, hrg.eq_iff, length_binSyms]
  have hfinal : ({ F with R := Function.update F.R (rg 3) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 4) (binSyms L (K + 3 * G)) } := by
    congr 1
    funext x
    by_cases h2 : x = rg 2
    · subst x; simp [F, E, D, C, hrg.eq_iff, hblank 2 (by decide) (by decide) (by decide)]
    · by_cases h3 : x = rg 3
      · subst x; simp [hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide)]
      · by_cases h4 : x = rg 4 <;> simp [F, E, D, C, h2, h3, h4, hrg.eq_iff]
  rw [hlen3, hfinal] at he₅
  exact ⟨v₅, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
