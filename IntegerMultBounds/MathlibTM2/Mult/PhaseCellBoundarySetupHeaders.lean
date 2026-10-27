module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Install and release only the five geometry headers needed by folded-page setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

def boundarySetupCopies : List (Fin 154 × Fin 154) := [(121,97),(122,98),(124,100),(141,101),(142,103)]
def boundarySetupHeaders : List (Fin 154) := [97,98,100,101,103]
def boundarySetupValue (s t band a b : ℕ) (k : Fin 154) : ℕ :=
  if k = 121 then s else if k = 122 then t else if k = 124 then band else if k = 141 then a else if k = 142 then b else 0

def boundarySetupR {A : ℕ} (s t band a b : ℕ) (R : Regs 154 A) : Regs 154 A :=
  unaryCopiesR (boundarySetupValue s t band a b) R boundarySetupCopies

theorem boundarySetupR_off {A : ℕ} (s t band a b : ℕ) (R : Regs 154 A) (k : Fin 154)
    (hk : k ∉ boundarySetupHeaders) : boundarySetupR s t band a b R k = R k := by
  apply unaryCopiesR_off
  intro r hr he
  apply hk
  rw [← he]
  simp only [boundarySetupCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [boundarySetupHeaders]


theorem boundarySetupR_update {A : ℕ} (s t band a b : ℕ) (R : Regs 154 A)
    (k : Fin 154) (xs : List (Fin (A+4))) (hk : k ∉ boundarySetupHeaders) :
    boundarySetupR s t band a b (Function.update R k xs) =
      Function.update (boundarySetupR s t band a b R) k xs := by
  have hd : ∀ r ∈ boundarySetupCopies, r.2 ≠ k := by
    intro r hr he
    apply hk
    rw [← he]
    simp only [boundarySetupCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [boundarySetupHeaders]
  funext j
  by_cases hj : j = k
  · subst j
    rw [boundarySetupR_off s t band a b _ k hk]
    simp
  · rw [Function.update_of_ne hj]
    exact unaryCopiesR_congr_base _ _ _ _ j
      (fun r hr => Function.update_of_ne (hd r hr) xs R) (Function.update_of_ne hj xs R)

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def installBoundarySetupHeaders : Pr P 154 Q A U := copyUnaryHeaders 135 boundarySetupCopies
def releaseBoundarySetupHeaders : Pr P 154 Q A U := clearWords boundarySetupHeaders

theorem installBoundarySetupHeaders_exec (s t band a b : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hs : (S.R 121).length = s) (ht : (S.R 122).length = t) (hband : (S.R 124).length = band)
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body installBoundarySetupHeaders (mk v S)
      (4*(s+t+band+a+b)+21) (mk v' {S with R := boundarySetupR s t band a b S.R}) := by
  obtain ⟨v',hu,he⟩ := copyUnaryHeaders_exec (body := body) 135 boundarySetupCopies
    (by intro r hr; simp only [boundarySetupCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro r hr p hp
        have hd : r.2.val < 117 := by
          simp only [boundarySetupCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
        have hs : 117 ≤ p.1.val := by
          simp only [boundarySetupCopies,List.mem_cons,List.not_mem_nil,or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
        intro he; have hh := congrArg Fin.val he; omega)
    (boundarySetupValue s t band a b) v S (by
      intro r hr
      simp only [boundarySetupCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simpa [boundarySetupValue] using hs
      · simpa [boundarySetupValue] using ht
      · simpa [boundarySetupValue] using hband
      · simpa [boundarySetupValue] using ha
      · simpa [boundarySetupValue] using hb) h135
  refine ⟨v',hu,he.cast ?_ rfl⟩
  simp [copyUnaryHeadersCost,boundarySetupCopies,boundarySetupValue]
  omega

theorem releaseBoundarySetupHeaders_exec (s t band a b : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hblank : ∀ k ∈ boundarySetupHeaders, S.R k = []) :
    ∃ v', v'.user = v.user ∧ Exec body releaseBoundarySetupHeaders
      (mk v {S with R := boundarySetupR s t band a b S.R}) (2*(s+t+band+a+b)+11) (mk v' S) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) boundarySetupHeaders (by decide) v
    {S with R := boundarySetupR s t band a b S.R}
  refine ⟨v',hu,he.cast ?_ ?_⟩
  · simp [boundarySetupHeaders,boundarySetupR,unaryCopiesR,boundarySetupCopies,boundarySetupValue,
      hblank 97 (by decide),hblank 98 (by decide),hblank 100 (by decide),hblank 101 (by decide),hblank 103 (by decide)]
    omega
  · apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ boundarySetupHeaders
    · simpa [hk] using (hblank k hk).symm
    · simpa [hk] using boundarySetupR_off s t band a b S.R k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
