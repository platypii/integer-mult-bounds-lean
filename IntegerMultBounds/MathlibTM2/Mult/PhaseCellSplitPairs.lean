module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSplitPair

/-! Separate an interleaved page structurally. Both output banks accumulate
whole words in descending row order; all count symbols and suffixes survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def pairStream (A w L : ℕ) (X Y : ℕ → GaussianInt) : List (Fin (A + 4)) :=
  (List.range L).flatMap (fun i => csyms A w (X i) ++ csyms A w (Y i))

def splitPairs : Pr P₀ 117 Q A U := scanP 103 108 splitPair

theorem splitPairs_exec (w L : ℕ) (X Y : ℕ → GaussianInt)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hw : (S.R 94).length = w) (hcount : (S.R 103).length = L)
    (hsrc : S.R 110 = pairStream A w L X Y ++ tail)
    (hfresh : ∀ k ∈ [(104 : Fin 117), 105, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ L * (12 * w + 17) + 4 ∧
      Exec body splitPairs (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 110 tail)
          111 (cstream A w ((List.range L).reverse.map X) ++ S.R 111))
          113 (cstream A w ((List.range L).reverse.map Y) ++ S.R 113)) }) := by
  let F := fun i => csyms A w (X i) ++ csyms A w (Y i)
  let Ψ : ℕ → Regs 117 A := fun i => Function.update (Function.update (Function.update S.R
    110 (((List.range L).drop i).flatMap F ++ tail))
    111 (cstream A w ((List.range i).reverse.map X) ++ S.R 111))
    113 (cstream A w ((List.range i).reverse.map Y) ++ S.R 113)
  have hstep : IterSpec body splitPair 103 108 Ψ (fun _ => 12 * w + 12) L := by
    intro i hi vi Si hSi
    have hd : (List.range L).drop i = i :: (List.range L).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]
      simp
    let rest := ((List.range L).drop (i + 1)).flatMap F ++ tail
    obtain ⟨vi', hu, he⟩ := splitPair_exec (body := body) w (X i) (Y i) vi Si rest
      (by rw [hSi 94 (by decide) (by decide)]; simpa [Ψ] using hw)
      (by rw [hSi 110 (by decide) (by decide)]; simp [Ψ, hd, F, rest, List.append_assoc])
      (by rw [hSi 104 (by decide) (by decide)]; simpa [Ψ] using hfresh 104 (by simp))
      (by rw [hSi 105 (by decide) (by decide)]; simpa [Ψ] using hfresh 105 (by simp))
    let R' := Function.update (Function.update (Function.update Si.R 110 rest)
      111 (csyms A w (X i) ++ Si.R 111)) 113 (csyms A w (Y i) ++ Si.R 113)
    refine ⟨vi', R', 12 * w + 12, hu, le_rfl, he, by simp [R'], by simp [R'], ?_⟩
    intro k hk103 hk108
    by_cases hk110 : k = 110
    · subst k; simp [R', Ψ, rest]
    by_cases hk111 : k = 111
    · subst k
      rw [show R' 111 = csyms A w (X i) ++ Si.R 111 by simp [R'], hSi 111 (by decide) (by decide)]
      simp [Ψ, List.range_succ, List.reverse_append, cstream, List.append_assoc]
    by_cases hk113 : k = 113
    · subst k
      rw [show R' 113 = csyms A w (Y i) ++ Si.R 113 by simp [R'], hSi 113 (by decide) (by decide)]
      simp [Ψ, List.range_succ, List.reverse_append, cstream, List.append_assoc]
    rw [show R' k = Si.R k by simp [R', hk110, hk111, hk113], hSi k hk103 hk108]
    simp [Ψ, hk110, hk111, hk113]
  obtain ⟨v', R', m, hu, hm, he, h103, h108, hrest⟩ := scanP_exec (body := body)
    (show (103 : Fin 117) ≠ 108 by decide) hstep 0 v S (by simp [hcount]) (by
      intro k _ _
      by_cases hk110 : k = 110
      · subst k; simpa [Ψ, F, pairStream] using hsrc
      simp only [Ψ, List.range_zero, List.reverse_nil, List.map_nil, cstream_nil, List.nil_append, List.drop_zero]
      by_cases hk111 : k = 111
      · subst k; simp
      by_cases hk113 : k = 113
      · subst k; simp
      simp [hk110, hk111, hk113])
  have hR : R' = Ψ L := by
    funext k
    by_cases hk103 : k = 103
    · subst k; simpa [Ψ, hfresh 108 (by simp)] using h103
    by_cases hk108 : k = 108
    · subst k; simpa [Ψ, hfresh 108 (by simp)] using h108
    simpa [hcount] using hrest k hk103 hk108
  rw [hR] at he
  refine ⟨v', m, hu, ?_, he.cast rfl ?_⟩
  · simp [hcount, hfresh 108 (by simp)] at hm
    nlinarith only [hm]
  · congr 1
    have hd : (List.range L).drop L = [] := List.drop_eq_nil_of_le (by simp)
    simp [Ψ, hd]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
