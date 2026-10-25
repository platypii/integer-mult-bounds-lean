module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowCall
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! # Consume owned row descriptors after an executed integer-row call

The column remains borrowed. Factor-row and RHS prefixes are owned input to
the row loop; their exact suffixes survive and all release counts are generated.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def consumeIntegerRow (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq (integerRowCall hQ)
    (.seq (releaseFromDimensions 102 94 99 111 104 106 105) (releasePrefix 94 112 104 105))

def integerRowCost (L w : ℕ) : ℕ := L * (rmulCost w + 55 * w + 30) + 20 * w + 73

theorem consumeIntegerRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L w : ℕ} (hw : 1 ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs ++ tailX) (ha : S.R 111 = cstream A w as ++ tailA)
    (hrhs : S.R 112 = csyms A w rhs ++ tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w 0)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ integerRowCost L w ∧
      Exec body (consumeIntegerRow hQ) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R
          111 tailA) 112 tailR) 113
            (csyms A w (rhs - (List.zipWith (· * ·) xs as).sum) ++ S.R 113)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := integerRowCall_exec (body := body) hQ hA hw xs as rhs hxlen halen
    hxs has v S tailX tailA tailR hL hwR hx ha hrhs hc hready hwork
  let result := csyms A w (rhs - (List.zipWith (· * ·) xs as).sum)
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 113 (result ++ S.R 113) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseFromDimensions_exec (body := body)
    (show [(102 : Fin 117), 94, 99, 111, 104, 106, 105].Nodup by decide) v₁ S₁
    (cstream A w as) tailA (by simpa [S₁] using ha)
    (by simp [S₁, halen, hL, hwR])
    (by simpa [S₁] using hwork 99 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 104 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 106 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 105 (by simp [integerRowWork]))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 111 tailA }
  obtain ⟨v₃, hu₃, he₃⟩ := releasePrefix_exec (body := body)
    (show [(94 : Fin 117), 112, 104, 105].Nodup by decide) v₂ S₂ (csyms A w rhs) tailR
    (by simpa [S₂, S₁] using hrhs) (by simpa [S₂, S₁, csyms] using hwR)
    (by simpa [S₂, S₁] using hwork 104 (by simp [integerRowWork]))
    (by simpa [S₂, S₁] using hwork 105 (by simp [integerRowWork]))
  refine ⟨v₃, m₁ + (m₂ + (6 * w + 6)), hu₃.trans (hu₂.trans hu₁), ?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by simp [csyms]) ?_⟩
  · simp only [S₁, Function.update_of_ne (show (102 : Fin 117) ≠ 113 by decide), hL] at hm₂
    have hlen : (cstream A w as).length = L * w := by simp [halen]
    rw [hlen] at hm₂
    unfold integerRowCost
    nlinarith only [hm₁, hm₂]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ha' : k = 111
    · subst k; simp [S₂, S₁]
    by_cases hr : k = 112
    · subst k; simp
    by_cases ho : k = 113
    · subst k; simp [S₂, S₁, result]
    simp [S₂, S₁, ha', hr, ho]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
