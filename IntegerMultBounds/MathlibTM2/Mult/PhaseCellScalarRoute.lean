module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarPrepare

/-! # Route the merged prefix and stored scalar into the generated-ready multiplier -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def route : Pr P 117 Q A U :=
  .seq (branchWords 108 3 2 103 1 7 8)
    (.seq (takeFromWords 1 94 2 93 84 7 8)
      (.seq (uclear 1) (copyPrefix 94 96 85 26 27)))

def routeR (R : Regs 117 A) (xs tail scalar : List (Fin (A + 4))) : Regs 117 A :=
  Function.update (Function.update (Function.update R 93 tail) 84 xs) 85 scalar

def routeCost (M L w : ℕ) : ℕ := 12 * (M * L * w) + 15 * (M * L) + 17 * M + 10 * w + 34

/-- All routing counters are generated and released before multiplication. The
factor source is preserved; only the input prefix and the two operand slots change. -/
theorem route_exec (M L w : ℕ) (xs : List GaussianInt) (a : GaussianInt)
    (hlen : xs.length = M * L) (v : HS 117 Q A U) (S : Stacks 117 A)
    (tail : List (Fin (A + 4)))
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hwidth : (S.R 94).length = w)
    (hsrc : S.R 93 = cstream A w xs ++ tail) (hscalar : S.R 96 = csyms A w a)
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 7, 8, 26, 27, 84, 85], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ routeCost M L w ∧
      Exec body route (mk v S) m
        (mk v' { S with R := routeR S.R (cstream A w xs) tail (csyms A w a) }) := by
  have hxs : (cstream A w xs).length = (M * L) * w := by simp [hlen]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := branchWords_exec (body := body)
    (batch := 108) (saved := 3) (half := 2) (rows := 103) (words := 1) (buf := 7) (tmp := 8)
    (by decide) M L v S (by omega) hrows (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 1 (List.replicate (M * L) tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := takeFromWords_exec (body := body)
    (words := 1) (width := 94) (count := 2) (src := 93) (dst := 84) (buf := 7) (tmp := 8)
    (by decide) (M * L) w v₁ S₁ (cstream A w xs) tail
    (by simp [S₁]) (by simpa [S₁] using hwidth) hxs (by simpa [S₁] using hsrc)
    (by simp [S₁, hclean _ (by simp : (2 : Fin 117) ∈ [1, 2, 3, 7, 8, 26, 27, 84, 85])])
    (by simp [S₁, hclean _ (by simp : (7 : Fin 117) ∈ [1, 2, 3, 7, 8, 26, 27, 84, 85])])
    (by simp [S₁, hclean _ (by simp : (8 : Fin 117) ∈ [1, 2, 3, 7, 8, 26, 27, 84, 85])])
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update (Function.update S₁.R 93 tail) 84 (cstream A w xs)) }
  have he₂' : Exec body (takeFromWords 1 94 2 93 84 7 8) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₁, Function.update_of_ne (show (84 : Fin 117) ≠ 1 by decide),
      hclean 84 (by simp), List.append_nil] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 1 v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 1 [] }
  have hwords : (S₂.R 1).length = M * L := by simp [S₂, S₁]
  obtain ⟨v₄, hu₄, he₄⟩ := copyPrefix_exec (body := body)
    (count := 94) (src := 96) (dst := 85) (saved := 26) (tmp := 27) (by decide)
    v₃ S₃ (csyms A w a) []
    (by simpa [S₃, S₂, S₁] using hscalar)
    (by simpa [S₃, S₂, S₁] using hwidth)
    (by simp [S₃, S₂, S₁, hclean _ (by simp : (26 : Fin 117) ∈ [1, 2, 3, 7, 8, 26, 27, 84, 85])])
    (by simp [S₃, S₂, S₁, hclean _ (by simp : (27 : Fin 117) ∈ [1, 2, 3, 7, 8, 26, 27, 84, 85])])
  refine ⟨v₄, m₁ + (m₂ + ((2 * (M * L) + 2) + (10 * w + 10))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · unfold routeCost
    nlinarith only [hm₁, hm₂]
  · refine (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hwords]; simp [csyms]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₂' he₃ he₄ hu₁ hu₂ hu₃ hu₄
    funext k
    simp only [S₃, S₂, S₁, routeR, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

/-- Routing changes only the two allowed operand roles inside the scalar bank. -/
theorem routeR_ready (q w : ℕ) (R : Regs 117 A) (xs tail scalar : List (Fin (A + 4)))
    (hr : Ready (fun r => R (cr r)) w q) :
    Ready (fun r => routeR R xs tail scalar (cr r)) w q := by
  have h93 (r : CR) : cr r ≠ (93 : Fin 117) := by
    intro h
    exact (cr_range r).2.2.1 (congrArg Fin.val h)
  have he : (fun r => routeR R xs tail scalar (cr r)) =
      Function.update (Function.update (fun r => R (cr r)) .xs xs) .ys scalar := by
    funext r
    simp only [routeR, show (84 : Fin 117) = cr .xs from rfl,
      show (85 : Fin 117) = cr .ys from rfl, Function.update_apply, cr_injective.eq_iff,
      ite_eq_right (h93 r)]
  rw [he]
  exact (hr.update .xs (by simp) xs).update .ys (by simp) scalar

/-- The routing scratch is restored before the scalar multiplication borrows it. -/
theorem routeR_clean (S : Stacks 117 A) (xs tail scalar : List (Fin (A + 4)))
    (hc : CClean mul S) : CClean mul { S with R := routeR S.R xs tail scalar } := by
  intro i
  have hi := i.isLt
  constructor
  · exact (hc i).1
  · have hh := (hc i).2
    have hn (k : Fin 117) (hk : 64 ≤ k.val) : mul i ≠ k := by
      intro h
      have he := congrArg Fin.val h
      simp only [mul] at he
      omega
    simpa [routeR, hn 93 (by decide), hn 84 (by decide), hn 85 (by decide)] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
