module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFixedScale
public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometry

/-! Generate the common target width from dimension and borrowed span. The
borrowed double/triple are temporary and erased; input words and scratch restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerTargetWidthGenerateProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (binaryDoubleCopyProgram (rg 1) (rg 2) (rg 5) (rg 6))
    (.seq (badd (rg 1) (rg 2) (rg 3) (rg 5) (rg 6) (rg 7) (rg 8))
      (.seq (bsub (rg 0) (rg 3) (rg 4) (rg 5) (rg 6) (rg 7) (rg 8))
        (.seq (bclear (rg 2)) (bclear (rg 3)))))

theorem routerTargetWidthGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (L n w : ℕ)
    (hn : n < 2 ^ L) (hw : 3 * w ≤ n) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hborrowed : S.R (rg 1) = binSyms L w)
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 8 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (routerTargetWidthGenerateProgram rg) (mk v S) (30 * L + 34)
        (mk v' { S with R := Function.update S.R (rg 4) (binSyms L (n - 3 * w)) }) := by
  obtain ⟨v₁, hu₁, hex₁⟩ := binaryDoubleCopy_exec body (rg 1) (rg 2) (rg 5) (rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) L w v S hborrowed
    (hblank 2 (by decide) (by decide) (by decide)) (hblank 5 (by decide) (by decide) (by decide))
    (hblank 6 (by decide) (by decide) (by decide))
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (2 * w)) }
  obtain ⟨v₂, hu₂, _, _, hex₂⟩ := badd_exec (body := body)
    (a := rg 1) (b := rg 2) (c := rg 3) (tx := rg 5) (ty := rg 6) (tz := rg 7) (cy := rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : w < 2 ^ L) (by omega : 2 * w < 2 ^ L) v₁ C
    (by simp [C, hrg.eq_iff, hborrowed]) (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
  have hsum : w + 2 * w = 3 * w := by omega
  have hc3 : C.R (rg 3) = [] := by simp [C, hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide)]
  rw [hsum, Nat.mod_eq_of_lt (hw.trans_lt hn), hc3, List.append_nil] at hex₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 3) (binSyms L (3 * w)) }
  obtain ⟨v₃, hu₃, _, _, hex₃⟩ := bsub_exec (body := body)
    (a := rg 0) (b := rg 3) (c := rg 4) (tx := rg 5) (ty := rg 6) (tz := rg 7) (cy := rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hn (hw.trans_lt hn) v₂ D
    (by simp [D, C, hrg.eq_iff, hdimension]) (by simp [D])
    (by simp [D, C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 7 (by decide) (by decide) (by decide)])
  have hsub : (n + 2 ^ L - 3 * w) % 2 ^ L = n - 3 * w := by
    rw [show n + 2 ^ L - 3 * w = (n - 3 * w) + 2 ^ L by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt hn)]
  have hd4 : D.R (rg 4) = [] := by simp [D, C, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide)]
  rw [hsub, hd4, List.append_nil] at hex₃
  let E : Stacks T A := { D with R := Function.update D.R (rg 4) (binSyms L (n - 3 * w)) }
  obtain ⟨v₄, hu₄, _, hex₄⟩ := bclear_exec body (rg 2) v₃ E
  let F : Stacks T A := { E with R := Function.update E.R (rg 2) [] }
  obtain ⟨v₅, hu₅, _, hex₅⟩ := bclear_exec body (rg 3) v₄ F
  have he2 : (E.R (rg 2)).length = L := by simp [E, D, C, hrg.eq_iff, length_binSyms]
  have hf3 : (F.R (rg 3)).length = L := by simp [F, E, D, hrg.eq_iff, length_binSyms]
  have hf : ({ F with R := Function.update F.R (rg 3) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 4) (binSyms L (n - 3 * w)) } := by
    congr 1
    funext j
    by_cases h2 : j = rg 2
    · subst j; simp [F, hrg.eq_iff, hblank 2 (by decide) (by decide) (by decide)]
    by_cases h3 : j = rg 3
    · subst j; simp [hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide)]
    by_cases h4 : j = rg 4
    · subst j; simp [F, E, D, C, hrg.eq_iff]
    · simp [F, E, D, C, h2, h3, h4]
  rw [he2] at hex₄
  rw [hf3, hf] at hex₅
  exact ⟨v₅, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    (Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ (Exec.seq hex₄ hex₅)))).cast (by omega) rfl⟩

/-- All canonical residues share the generated target-width operand. -/
theorem routerTargetWidthGenerate_canonical_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (L n K G : ℕ)
    (hn : n < 2 ^ L) (hlarge : K ≤ n) (r : Fin K)
    (v : HS T Q A U) (S : Stacks T A) (hdimension : S.R (rg 0) = binSyms L n)
    (hborrowed : S.R (rg 1) = binSyms L (routerBorrowed n K G))
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 8 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (routerTargetWidthGenerateProgram rg) (mk v S) (30 * L + 34)
        (mk v' { S with R := Function.update S.R (rg 4) (binSyms L (routerProfileParameters n K G r.val).wy) }) := by
  rw [routerProfileParameters_width n K G hlarge r]
  have hdecomp := routerGeometry_decomposition n K G hlarge
  exact routerTargetWidthGenerate_exec body rg hrg L n (routerBorrowed n K G) hn (by omega)
    v S hdimension hborrowed hblank

end IntegerMultBounds.MathlibTM2.Routing
