module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupInput

/-! Retained master parameters initialize the private solver's ordinary input
headers. Every master stack survives, including the selected key and key queue. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def groupHeaderCopies : List (Fin 144 × Fin 144) :=
  [(117,114),(118,101),(119,112),(120,109),(121,97),(122,98),(123,99),(124,100),(128,102),(128,103)]

def groupHeaderValue (P N q l s t u band L : ℕ) (k : Fin 144) : ℕ :=
  if k.val = 117 then P else if k.val = 118 then N else if k.val = 119 then q else
  if k.val = 120 then l else if k.val = 121 then s else if k.val = 122 then t else
  if k.val = 123 then u else if k.val = 124 then band else if k.val = 128 then L else 0

def copiedGroupR {A : ℕ} (P N q l s t u band L : ℕ) (R : Fin 144 → List (Fin (A+4))) :=
  unaryCopiesR (groupHeaderValue P N q l s t u band L) R groupHeaderCopies

theorem copiedGroupR_off {A : ℕ} (P N q l s t u band L : ℕ) (R : Fin 144 → List (Fin (A+4)))
    (k : Fin 144) (hk : 117 ≤ k.val) : copiedGroupR P N q l s t u band L R k = R k := by
  apply unaryCopiesR_off
  intro r hr he
  have hlo : r.2.val < 117 := by
    simp only [groupHeaderCopies, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hv := congrArg (fun k : Fin 144 => k.val) he
  omega

theorem copiedGroup_project {A : ℕ} (P N q l s t u band L : ℕ) (S : Stacks 144 A)
    (raw borrowed : List (Fin (A+4)))
    (hL : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hR : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = raw++borrowed) :
    embStk groupReg { S with R := copiedGroupR P N q l s t u band L S.R } =
      naturalGroupInputBank P N q l s t u band L raw borrowed (S.R 93) S.inp S.out := by
  have hat (r : Fin 144 × Fin 144) (hr : r ∈ groupHeaderCopies) :
      copiedGroupR P N q l s t u band L S.R r.2 =
        List.replicate (groupHeaderValue P N q l s t u band L r.1) tick := by
    have hfresh : r.2.val < 117 ∧ r.2 ≠ 93 ∧ r.2 ≠ 110 := by
      simp only [groupHeaderCopies, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [copiedGroupR, unaryCopiesR_at _ _ _ (by decide) r hr,
      hR r.2 hfresh.1 hfresh.2.1 hfresh.2.2, List.append_nil]
  ext1
  · rfl
  · rfl
  · funext i; exact hL (groupReg i) i.isLt
  · funext i
    by_cases hi : i.val ∈ [114,101,112,109,97,98,99,100,102,103]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h | h | h | h | h | h | h | h | h
      · have he : i = (114 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (117,114) (by decide)
      · have he : i = (101 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (118,101) (by decide)
      · have he : i = (112 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (119,112) (by decide)
      · have he : i = (109 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (120,109) (by decide)
      · have he : i = (97 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (121,97) (by decide)
      · have he : i = (98 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (122,98) (by decide)
      · have he : i = (99 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (123,99) (by decide)
      · have he : i = (100 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (124,100) (by decide)
      · have he : i = (102 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (128,102) (by decide)
      · have he : i = (103 : Fin 117) := Fin.ext h
        subst i
        simpa [embStk, groupReg, groupHeaderValue, naturalGroupInputBank, batchInputBank] using
          hat (128,103) (by decide)
    · have hn (n : ℕ) (hn : n ∈ [114,101,112,109,97,98,99,100,102,103]) : i.val ≠ n := fun he => hi (he ▸ hn)
      have hoff : copiedGroupR P N q l s t u band L S.R (groupReg i) = S.R (groupReg i) := by
        apply unaryCopiesR_off
        intro r hr he
        have hv := congrArg (fun k : Fin 144 => k.val) he
        simp only [groupHeaderCopies, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp only [groupReg] at hv
        all_goals apply hi; simp [← hv]
      change copiedGroupR P N q l s t u band L S.R (groupReg i) = _
      rw [hoff]
      by_cases h93 : i.val = 93
      · have he : groupReg i = (93 : Fin 144) := Fin.ext h93
        simp [naturalGroupInputBank, batchInputBank, h93, he]
      by_cases h110 : i.val = 110
      · have he : groupReg i = (110 : Fin 144) := Fin.ext h110
        simp [naturalGroupInputBank, batchInputBank, h110, he, hsrc]
      rw [hR _ i.isLt (by simpa [groupReg, Fin.ext_iff] using h93) (by simpa [groupReg, Fin.ext_iff] using h110)]
      simp [naturalGroupInputBank, batchInputBank, h93, h110, hn 114 (by decide), hn 101 (by decide),
        hn 112 (by decide), hn 109 (by decide), hn 97 (by decide), hn 98 (by decide), hn 99 (by decide),
        hn 100 (by decide), hn 102 (by decide), hn 103 (by decide)]

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 144 Q A U}

def installGroupHeaders : Pr P₀ 144 Q A U := copyUnaryHeaders 133 groupHeaderCopies

def installGroupHeadersCost (P N q l s t u band L : ℕ) : ℕ :=
  4*(P+N+q+l+s+t+u+band+2*L)+41

theorem installGroupHeaders_exec (P N q l s t u band L : ℕ)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hsrc : ∀ r ∈ groupHeaderCopies, (S.R r.1).length = groupHeaderValue P N q l s t u band L r.1)
    (h133 : S.R 133 = []) :
    ∃ v', v'.user = v.user ∧ Exec body installGroupHeaders (mk v S)
      (installGroupHeadersCost P N q l s t u band L)
      (mk v' { S with R := copiedGroupR P N q l s t u band L S.R }) := by
  have hregs : ∀ r ∈ groupHeaderCopies, [r.1,r.2,(133 : Fin 144)].Nodup := by
    intro r hr
    simp only [groupHeaderCopies, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hsep : ∀ r ∈ groupHeaderCopies, ∀ p ∈ groupHeaderCopies, r.2 ≠ p.1 := by
    intro r hr p hp he
    have hlo : r.2.val < 117 := by
      simp only [groupHeaderCopies, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hhi : 117 ≤ p.1.val := by
      simp only [groupHeaderCopies, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hv := congrArg (fun k : Fin 144 => k.val) he
    omega
  obtain ⟨v', hu, he⟩ := copyUnaryHeaders_exec (body := body) 133 groupHeaderCopies hregs hsep
    (groupHeaderValue P N q l s t u band L) v S hsrc h133
  refine ⟨v', hu, he.cast ?_ rfl⟩
  simp [copyUnaryHeadersCost, groupHeaderCopies, groupHeaderValue, installGroupHeadersCost]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
