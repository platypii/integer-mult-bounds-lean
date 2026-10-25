module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientWidth

/-! # Prepare the numerical table input from owned unary geometry headers

All source symbols survive loading. The owned geometry headers and the generated
workspace-width source are released only after the binary state is complete.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def geometryHeaderPorts : List (Fin 117) := [97, 98, 99, 100, 115]

def prepareCoefficientHeaders : Pr P₀ 117 Q A U :=
  .seq initializeCoefficientBank (.seq loadCoefficientHeaders (clearWords geometryHeaderPorts))

def prepareCoefficientHeadersCost (P s t u band L V W : ℕ) : ℕ :=
  (292 * V + 4 * W + 393) + coefficientHeadersCost P s t u band L V +
    (2 * (s + t + u + band + V) + 11)

/-- A concrete loader supplies every table precondition and preserves all
borrowed stacks outside the owned geometry-header ports. -/
theorem prepareCoefficientHeaders_exec (P s t u band L V W : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hu : (S.R 99).length = u) (hb : (S.R 100).length = band) (hL : (S.R 102).length = L)
    (hV : (S.R 115).length = V) (hW : (S.R 94).length = W) (hz : S.R 106 = [])
    (hblank : ∀ r, S.R (coefficientReg r) = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ prepareCoefficientHeadersCost P s t u band L V W ∧
      Exec body prepareCoefficientHeaders (mk v S) m (mk v' S') ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate W tick)
        (coefficientHeaderState P s t u band L)) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, 63 ≤ k.val → S'.R k = if k ∈ geometryHeaderPorts then [] else S.R k := by
  obtain ⟨v₁, hu₁, he₁, hholds₁⟩ := initializeCoefficientBank_exec (body := body) V W v S hV hW hz hblank
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR coefficientReg (fun _ => 106) V W (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : 63 ≤ k.val) : S₁.R k = S.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := coefficientReg_range r
    rw [he] at hk
    omega
  obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hholds₂, hframe₂⟩ := loadCoefficientHeaders_exec (body := body)
    P s t u band L V W v₁ S₁
    (by rw [hoff₁ 114 (by decide)]; exact hP) (by rw [hoff₁ 97 (by decide)]; exact hs)
    (by rw [hoff₁ 98 (by decide)]; exact ht) (by rw [hoff₁ 99 (by decide)]; exact hu)
    (by rw [hoff₁ 100 (by decide)]; exact hb) (by rw [hoff₁ 102 (by decide)]; exact hL) hholds₁
  have hoff₂ (k : Fin 117) (hk : 63 ≤ k.val) : S₂.R k = S.R k := by
    rw [hframe₂.2.2.2 k (fun r he => by have hr := coefficientReg_range r; rw [he] at hr; omega)]
    exact hoff₁ k hk
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) geometryHeaderPorts (by decide) v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := fun k => if k ∈ geometryHeaderPorts then [] else S₂.R k }
  have hsum : (geometryHeaderPorts.map (fun k => (S₂.R k).length)).sum = s + t + u + band + V := by
    simp [geometryHeaderPorts, hoff₂ 97 (by decide), hoff₂ 98 (by decide), hoff₂ 99 (by decide),
      hoff₂ 100 (by decide), hoff₂ 115 (by decide), hs, ht, hu, hb, hV]
    omega
  refine ⟨v₃, S₃, (292 * V + 4 * W + 393) + (m₂ + (2 * (s + t + u + band + V) + 11)),
    hu₃.trans (hu₂.trans hu₁), by unfold prepareCoefficientHeadersCost; omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) rfl, ?_,
    hframe₂.1, hframe₂.2.1, hframe₂.2.2.1, ?_⟩
  · intro r
    have hn : coefficientReg r ∉ geometryHeaderPorts := by
      have hr := coefficientReg_range r
      intro hk
      simp only [geometryHeaderPorts, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with he | he | he | he | he <;> rw [he] at hr <;> omega
    simpa [S₃, hn] using hholds₂ r
  · intro k hk
    by_cases hg : k ∈ geometryHeaderPorts
    · simp [S₃, hg]
    simpa [S₃, hg] using hoff₂ k hk

/-- Workspace sizing discharges every binary header fit without a supplied
numerical-state boundedness hypothesis. -/
theorem coefficientHeaderState_fits (P W s t u band L : ℕ) (hst : s ≤ t) :
    ∀ j, (coefficientHeaderState P s t u band L : TblSt 48 A).val j <
      2 ^ coefficientWorkspaceWidth P W t u band L := by
  obtain ⟨_, hP, hs, ht, hu, hb, hL, _⟩ := coefficientWorkspaceWidth_bound P W s t u band L hst
  intro j
  by_cases h19 : j = 19
  · subst j; simpa [coefficientHeaderState] using hP
  by_cases h34 : j = 34
  · subst j; simpa [coefficientHeaderState] using hs
  by_cases h35 : j = 35
  · subst j; simpa [coefficientHeaderState] using ht
  by_cases h36 : j = 36
  · subst j; simpa [coefficientHeaderState] using hu
  by_cases h38 : j = 38
  · subst j; simpa [coefficientHeaderState] using hb
  by_cases h42 : j = 42
  · subst j; simpa [coefficientHeaderState] using hL
  simp [coefficientHeaderState, h19, h34, h35, h36, h38, h42]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
