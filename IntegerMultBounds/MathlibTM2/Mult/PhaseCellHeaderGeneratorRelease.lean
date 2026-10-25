module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderGeneratorSetup

/-! # Teardown of the setup built from ordinary unary headers

The owned geometry inputs are consumed. Every borrowed stack, suffix and header
returns, including the initially empty slot used for the generated setup width.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def consumedGeometryBank {A : ℕ} (S : Stacks 117 A) : Stacks 117 A :=
  { S with R := fun k => if k ∈ geometryHeaderPorts then [] else S.R k }

def headerGeneratorRelease : Pr P₀ 117 Q A U := .seq numericalGeneratorRelease (uclear 94)

/-- All generated pages, counters, widths and binary table words are released. -/
theorem headerGeneratorRelease_exec (P s t u band L q M : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L) (hq : (S.R 112).length = q)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 105, 106, 116], S.R k = []) :
    let W := integerSetupWidth P q (M + 1) 0
    ∃ v' m, v'.user = v.user ∧
      m ≤ releasePackedSetupCost L q W (M + 1) + releaseFactorPageCost L W + 2 * W + 2 ∧
      Exec body headerGeneratorRelease
        (mk v (packedGeneratorBank (constructedFactorBank (unaryGeometryBase S P q M) P s t u band L W)
          P s t u band L q W (M + 1))) m (mk v' (consumedGeometryBank S)) := by
  let W := integerSetupWidth P q (M + 1) 0
  let B := unaryGeometryBase S P q M
  have hcore (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
    have hh := (hclean ⟨k.val, by omega⟩).2
    simpa [mul] using hh
  have hblankB : ∀ r, B.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hg : cr r ∉ geometryHeaderPorts := by
      intro hk
      simp only [geometryHeaderPorts, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with he | he | he | he | he <;> have hv := congrArg Fin.val he <;> omega
    have h94 : cr r ≠ (94 : Fin 117) := by intro he; exact hr.2.2.2 (congrArg Fin.val he)
    simpa [B, unaryGeometryBase, setupWidthBank, hg, h94] using hblank r
  have hfreshB : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106], B.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [B, unaryGeometryBase, geometryHeaderPorts]
    · simp [B, unaryGeometryBase, geometryHeaderPorts]
    · simp [B, unaryGeometryBase, geometryHeaderPorts]
    · simpa [B, unaryGeometryBase, geometryHeaderPorts, setupWidthBank] using hfresh 104 (by simp)
    · simpa [B, unaryGeometryBase, geometryHeaderPorts, setupWidthBank] using hfresh 105 (by simp)
    · simpa [B, unaryGeometryBase, geometryHeaderPorts, setupWidthBank] using hfresh 106 (by simp)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := numericalGeneratorRelease_exec (body := body)
    P s t u band L q W (M + 1) v B
    (by simpa [B, unaryGeometryBase, geometryHeaderPorts, setupWidthBank] using hrows)
    (by simpa [B, unaryGeometryBase, geometryHeaderPorts, setupWidthBank] using hcount)
    (by simpa [B, unaryGeometryBase, geometryHeaderPorts, setupWidthBank] using hq)
    (by simp [B, unaryGeometryBase, geometryHeaderPorts, setupWidthBank, W]) hblankB
    (by simpa [B, unaryGeometryBase, geometryHeaderPorts, setupWidthBank] using hfresh 116 (by simp)) hfreshB
  have hrestore : ({ B with R := fun k => if k.val < 63 then [] else B.R k } : Stacks 117 A) = B := by
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k.val < 63
    · have h94 : k ≠ (94 : Fin 117) := by intro he; have hv := congrArg Fin.val he; omega
      have hg : k ∉ geometryHeaderPorts := by
        intro hg
        simp only [geometryHeaderPorts, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with he | he | he | he | he <;> have hv := congrArg Fin.val he <;> omega
      simp [hk, B, unaryGeometryBase, setupWidthBank, hg, h94, hcore k hk]
    simp [hk]
  rw [hrestore] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body 94 v₁ B
  have hlen : (B.R 94).length = W := by simp [B, unaryGeometryBase, geometryHeaderPorts, setupWidthBank, W]
  refine ⟨v₂, m₁ + (2 * W + 2), hu₂.trans hu₁, by dsimp [W] at hm₁ ⊢; omega,
    (Exec.seq he₁ he₂).cast (by rw [hlen]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = 94
  · subst k; simp [consumedGeometryBank, geometryHeaderPorts, hfresh 94 (by simp)]
  simp [B, unaryGeometryBase, setupWidthBank, consumedGeometryBank, hk, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
