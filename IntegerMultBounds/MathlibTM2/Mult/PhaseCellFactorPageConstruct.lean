module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRowCounters

/-! # Construct the whole factor page from the distance vector

An existing unary scanner restores its original count symbols. Each generated
row is prefixed, so the page has the descending row order used by the solver.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def constructFactorPage : Pr P₀ 117 Q A U :=
  .seq (scanP 103 108 factorRowStep) (uclear 97)

def constructFactorPageCost (L W : ℕ) : ℕ := L * (factorRowStepCost L W + 7) + 6

/-- Exponential data are supplied only once per distance. No matrix row or page
is an input; row counts, offsets, assembly and workspace release all execute. -/
theorem constructFactorPage_exec (P s t u band L W : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hW : (S.R 94).length = W) (hL : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hsrc : S.R 110 = cstream A W (distanceFactorWords P s t u band L) ++ tail)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 100, 104, 105, 106, 107, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ constructFactorPageCost L W ∧
      Exec body constructFactorPage (mk v S) m
        (mk v' { S with R := (Function.update S.R 109
          (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ S.R 109)) }) := by
  let Ψ : ℕ → Regs 117 A := fun i => (Function.update (Function.update S.R 97 (List.replicate i tick)) 109
    (cstream A W ((List.range i).reverse.flatMap (rowFactorWords P s t u band L)) ++ S.R 109))
  have hstep : IterSpec body factorRowStep 103 108 Ψ (fun _ => factorRowStepCost L W) L := by
    intro i hi vi Si hSi
    obtain ⟨vi', m, hu, hm, he⟩ := factorRowStep_exec (body := body) P s t u band L W i hi vi Si tail
      (by rw [hSi 94 (by decide) (by decide)]; simpa [Ψ] using hW)
      (by rw [hSi 102 (by decide) (by decide)]; simpa [Ψ] using hL)
      (by rw [hSi 97 (by decide) (by decide)]; simp [Ψ])
      (by rw [hSi 110 (by decide) (by decide)]; simpa [Ψ] using hsrc) (by
        intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rw [hSi _ (by decide) (by decide)] <;> simpa [Ψ] using hfresh _ (by simp))
    let R' := Function.update (Function.update Si.R 109
      (cstream A W (rowFactorWords P s t u band L i) ++ Si.R 109)) 97 (tick :: Si.R 97)
    refine ⟨vi', R', m, hu, hm, he, by simp [R'], by simp [R'], ?_⟩
    intro k hk103 hk108
    by_cases hk97 : k = 97
    · subst k
      rw [show R' 97 = tick :: Si.R 97 by simp [R'], hSi 97 (by decide) (by decide)]
      simp [Ψ, List.replicate_succ]
    by_cases hk109 : k = 109
    · subst k
      rw [show R' 109 = cstream A W (rowFactorWords P s t u band L i) ++ Si.R 109 by simp [R'],
        hSi 109 (by decide) (by decide)]
      simp [Ψ, List.range_succ, List.reverse_append, cstream_append, List.append_assoc]
    rw [show R' k = Si.R k by simp [R', hk97, hk109], hSi k hk103 hk108]
    simp [Ψ, hk97, hk109]
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, h103, h108, hrest⟩ := scanP_exec (body := body)
    (show (103 : Fin 117) ≠ 108 by decide) hstep 0 v S (by simpa [hcount]) (by
      intro k _ _
      by_cases hk : k = 97
      · subst k; simp [Ψ, hfresh 97 (by simp)]
      by_cases h109 : k = 109
      · subst k; simp [Ψ]
      simp [Ψ, hk, h109])
  have hR : R₁ = Ψ L := by
    funext k
    by_cases h103' : k = 103
    · subst k
      simpa [Ψ, hfresh 108 (by simp)] using h103
    by_cases h108' : k = 108
    · subst k; simpa [Ψ, hfresh 108 (by simp)] using h108
    simpa [hcount] using hrest k h103' h108'
  rw [hR] at he₁
  let S₁ : Stacks 117 A := { S with R := Ψ L }
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body 97 v₁ S₁
  have hidx : (S₁.R 97).length = L := by simp [S₁, Ψ]
  have hcost : m₁ ≤ L * (factorRowStepCost L W + 5) + 4 := by
    have hb := hm₁
    simp [hcount, hfresh 108 (by simp)] at hb
    nlinarith only [hb]
  refine ⟨v₂, m₁ + (2 * L + 2), hu₂.trans hu₁, by unfold constructFactorPageCost; nlinarith only [hcost],
    (Exec.seq he₁ he₂).cast (by rw [hidx]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = 97
  · subst k; simp [hfresh 97 (by simp)]
  simp [S₁, Ψ, hk, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
