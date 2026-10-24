module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStrideGenerate

/-! Generate the residue-loop count from binary dimension alone. Temporary gap
and stride words are erased before the loop; only the unary count changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalResidueCountProgram (rg : Fin 10 → Fin T) (count : Fin T) : Pr P T Q A U :=
  .seq (canonicalStrideGenerateProgram rg)
    (.seq (toUnary (rg 9) count (rg 1) (rg 2) (rg 3))
      (.seq (bclear (rg 4)) (bclear (rg 9))))

theorem canonicalResidueCount_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (count : Fin T) (hcountOff : ∀ j, count ≠ rg j)
    (L n : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (v : HS T Q A U) (S : Stacks T A) (hdimension : S.R (rg 0) = binSyms L n)
    (hblank : ∀ j : Fin 10, j ≠ 0 → j ≠ 8 → S.R (rg j) = []) (hcount : S.R count = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 4 * L * L + 123 * L + 180 + 6 * canonicalRouterStride n ∧
      Exec body (canonicalResidueCountProgram rg count) (mk v S) m
        (mk v' { S with R := Function.update S.R count (List.replicate (canonicalRouterStride n) IntegerMultBounds.MathlibTM2.Node.tick) }) := by
  have hfit := hlarge.trans_lt hn
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := canonicalStrideGenerate_exec body rg hrg L n hn hfit v S hdimension hblank
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R (rg 4)
    (binSyms L (canonicalRouterGap n))) (rg 9) (binSyms L (canonicalRouterStride n))) }
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := toUnary_exec_linear (body := body)
    (a := rg 9) (z := count) (w := rg 1) (t := rg 2) (t₂ := rg 3)
    (by simp [List.nodup_cons, hrg.eq_iff, hcountOff, fun j => (hcountOff j).symm]) hfit v₁ C
    (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 1 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 2 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
  have hc : C.R count = [] := by simp [C, hcountOff, hcount]
  rw [hc, List.append_nil] at hex₂
  let D : Stacks T A := { C with R := (Function.update C.R count
    (List.replicate (canonicalRouterStride n) IntegerMultBounds.MathlibTM2.Node.tick)) }
  obtain ⟨v₃, hu₃, _, hex₃⟩ := bclear_exec body (rg 4) v₂ D
  let E : Stacks T A := { D with R := Function.update D.R (rg 4) [] }
  obtain ⟨v₄, hu₄, _, hex₄⟩ := bclear_exec body (rg 9) v₃ E
  have hlen4 : (D.R (rg 4)).length = L := by simp [D, C, (hcountOff 4).symm, hrg.eq_iff, length_binSyms]
  have hlen9 : (E.R (rg 9)).length = L := by simp [E, D, C, (hcountOff 9).symm, hrg.eq_iff, length_binSyms]
  have hf : ({ E with R := Function.update E.R (rg 9) [] } : Stacks T A) =
      { S with R := Function.update S.R count (List.replicate (canonicalRouterStride n) IntegerMultBounds.MathlibTM2.Node.tick) } := by
    congr 1
    funext j
    by_cases h4 : j = rg 4
    · subst j; simp [E, D, C, hrg.eq_iff, (hcountOff 4).symm, hblank 4 (by decide) (by decide)]
    by_cases h9 : j = rg 9
    · subst j; simp [E, D, C, (hcountOff 9).symm, hblank 9 (by decide) (by decide)]
    by_cases hz : j = count
    · subst j; simp [E, D, C, hcountOff]
    · simp [E, D, C, h4, h9, hz]
  rw [hlen4] at hex₃
  rw [hlen9, hf] at hex₄
  exact ⟨v₄, m₁ + (m₂ + ((2 * L + 2) + (2 * L + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by omega, Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ hex₄))⟩

def canonicalResidueCountScope (rg : Fin 10 → Fin T) (count : Fin T)
    (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (canonicalResidueCountProgram rg count) (.seq call (bclear count))

theorem canonicalResidueCountScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 10 → Fin T) (hrg : Function.Injective rg) (count : Fin T) (hcountOff : ∀ j, count ≠ rg j)
    (L n : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (v : HS T Q A U) (S : Stacks T A) (hdimension : S.R (rg 0) = binSyms L n)
    (hblank : ∀ j : Fin 10, j ≠ 0 → j ≠ 8 → S.R (rg j) = []) (hcount : S.R count = [])
    (dst : Fin T) (hdst : dst ≠ count) (output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := (Function.update S.R count
        (List.replicate (canonicalRouterStride n) IntegerMultBounds.MathlibTM2.Node.tick)) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R dst output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ price + 4 * L * L + 123 * L + 182 + 8 * canonicalRouterStride n ∧
      Exec body (canonicalResidueCountScope rg count call) (mk v S) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := canonicalResidueCount_exec body rg hrg count hcountOff L n hn hlarge v S
    hdimension hblank hcount
  let C : Stacks T A := { S with R := (Function.update S.R count
    (List.replicate (canonicalRouterStride n) IntegerMultBounds.MathlibTM2.Node.tick)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R dst output }
  obtain ⟨v₃, hu₃, _, hex₃⟩ := bclear_exec body count v₂ D
  have hlen : (D.R count).length = canonicalRouterStride n := by simp [D, C, hdst.symm]
  have hf : ({ D with R := Function.update D.R count [] } : Stacks T A) =
      { S with R := Function.update S.R dst output } := by
    congr 1
    funext j
    by_cases hc : j = count
    · subst j; simp [hdst.symm, hcount]
    · by_cases hd : j = dst <;> simp [D, C, hc, hd, hdst]
  rw [hlen, hf] at hex₃
  exact ⟨v₃, m₁ + (m₂ + (2 * canonicalRouterStride n + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hex₁ (Exec.seq hex₂ hex₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
