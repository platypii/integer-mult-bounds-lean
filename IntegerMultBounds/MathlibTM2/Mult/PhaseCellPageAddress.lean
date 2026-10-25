module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplementHeader

/-! # Addresses of retained setup and per-call payload pages

The number of preceding banks is a fixed program parameter. Repeated copies
preserve the actual source header and return private workspace empty.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def copyRepeated (src dst saved : Fin T) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | n + 1 => .seq (copyR src dst saved id) (copyRepeated src dst saved n)

theorem copyRepeated_exec {src dst saved : Fin T} (hreg : [src, dst, saved].Nodup)
    (n : ℕ) (v : HS T Q A U) (S : Stacks T A) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyRepeated src dst saved n) (mk v S) (n * (4 * (S.R src).length + 4) + 1)
        (mk v' { S with R := (Function.update S.R dst
          ((List.replicate n (S.R src).reverse).flatten ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  induction n generalizing v S with
  | zero =>
      refine ⟨v, rfl, ?_⟩
      simpa [copyRepeated] using Exec.act (body := body) (.done : Act T Q A U) (mk v S)
  | succ n ih =>
      obtain ⟨v₁, hu₁, he₁⟩ := copyR_exec body src dst saved
        ‹src ≠ dst› ‹src ≠ saved› ‹dst ≠ saved› id v S hsaved
      let S₁ : Stacks T A := { S with R := Function.update S.R dst ((S.R src).reverse ++ S.R dst) }
      have he₁' : Exec body (copyR src dst saved id) (mk v S)
          (4 * (S.R src).length + 4) (mk v₁ S₁) := by simpa only [List.map_id] using he₁
      obtain ⟨v₂, hu₂, he₂⟩ := ih v₁ S₁ (by simpa [S₁, ‹dst ≠ saved›.symm] using hsaved)
      refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' he₂).cast ?_ ?_⟩
      · simp only [S₁, Function.update_of_ne ‹src ≠ dst›]; ring
      · congr 1
        ext1
        · rfl
        · rfl
        · rfl
        funext k
        by_cases hk : k = dst
        · subst k
          simp [S₁, ‹src ≠ dst›, List.replicate_succ', List.flatten_append, List.append_assoc]
        · simp [S₁, hk]

def pageAddress (banks : ℕ) (bank width skip saved : Fin T) : Pr P T Q A U :=
  .seq (copyR width skip saved id) (copyRepeated bank skip saved banks)

theorem pageAddress_exec {bank width skip saved : Fin T}
    (hreg : [bank, width, skip, saved].Nodup) (banks : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hskip : S.R skip = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (pageAddress banks bank width skip saved) (mk v S)
        (banks * (4 * (S.R bank).length + 4) + 4 * (S.R width).length + 5)
        (mk v' { S with R := (Function.update S.R skip
          ((List.replicate banks (S.R bank).reverse).flatten ++ (S.R width).reverse)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := copyR_exec body width skip saved
    ‹width ≠ skip› ‹width ≠ saved› ‹skip ≠ saved› id v S hsaved
  let S₁ : Stacks T A := { S with R := Function.update S.R skip (S.R width).reverse }
  have he₁' : Exec body (copyR width skip saved id) (mk v S)
      (4 * (S.R width).length + 4) (mk v₁ S₁) := by simpa only [List.map_id, hskip, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := copyRepeated_exec (body := body)
    (show [bank, skip, saved].Nodup by simp_all) banks v₁ S₁
    (by simpa [S₁, ‹skip ≠ saved›.symm] using hsaved)
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp [S₁, ‹bank ≠ skip›]; omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = skip
    · subst k; simp [S₁, ‹bank ≠ skip›]
    · simp [S₁, hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
