module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingTableResize

/-! Borrow a resized matching table for an executed call, then erase the table.
The source table and all workspace restore; only the call output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingTableResizeScope (rg : Fin 14 → Fin T) (table : Fin T)
    (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (matchingTableResizeProgram rg table) (.seq call (bclear table))

theorem matchingTableResizeScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 14 → Fin T) (hrg : Function.Injective rg)
    (table : Fin T) (htable : ∀ j, table ≠ rg j) (M L W : ℕ) (hW : W < 2 ^ M)
    (xs : List (ℕ × ℕ)) (hfit : ∀ x ∈ xs, x.1 < 2 ^ L ∧ x.2 < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms M W) (hinput : S.R (rg 10) = matchingEntryWords L xs)
    (hblank : ∀ j : Fin 14, j ≠ 0 → j ≠ 10 → S.R (rg j) = []) (htableBlank : S.R table = [])
    (dst : Fin T) (hdst : dst ≠ table) (output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := Function.update S.R table (matchingEntryWords W xs) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R dst output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ price + xs.length * (4 * M * (4 * W + 11) + 40 * L + 64 * W + 122) + 8 ∧
      Exec body (matchingTableResizeScope rg table call) (mk v S) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := matchingTableResize_exec body rg hrg table htable M L W hW
    xs hfit v S hwidth hinput hblank
  rw [htableBlank, List.append_nil] at hex₁
  let C : Stacks T A := { S with R := Function.update S.R table (matchingEntryWords W xs) }
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R dst output }
  obtain ⟨v₃, hu₃, _, hex₃⟩ := bclear_exec body table v₂ D
  have hlen : (D.R table).length = xs.length * (2 * W + 2) := by
    simp [D, C, hdst.symm, matchingEntryWords_length]
  have hf : ({ D with R := Function.update D.R table [] } : Stacks T A) =
      { S with R := Function.update S.R dst output } := by
    congr 1
    funext j
    by_cases ht : j = table
    · subst j; simp [hdst.symm, htableBlank]
    · by_cases hd : j = dst <;> simp [D, C, ht, hd, hdst]
  rw [hlen, hf] at hex₃
  refine ⟨v₃, m₁ + (m₂ + (2 * (xs.length * (2 * W + 2)) + 2)),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq hex₁ (Exec.seq hex₂ hex₃)⟩
  nlinarith only [hm₁, hm₂]

end IntegerMultBounds.MathlibTM2.Routing
