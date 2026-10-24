module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingPrefixCount
public import IntegerMultBounds.MathlibTM2.Routing.MatchingEntryWidth

/-! Generate the complete serialized profile prefix count from binary row count,
stride and coordinate width. Only the count output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingPrefixOperandSlot : Fin 11 → Fin 13 := Fin.castLE (by decide)
def matchingEntryWidthSlot : Fin 6 → Fin 13 := ![11,12,2,7,8,10]

theorem matchingPrefixOperandSlot_injective : Function.Injective matchingPrefixOperandSlot := by decide +kernel
theorem matchingEntryWidthSlot_injective : Function.Injective matchingEntryWidthSlot := by decide +kernel

def matchingPrefixCountFromWidthProgram (rg : Fin 13 → Fin T) : Pr P T Q A U :=
  .seq (matchingEntryWidthProgram (rg ∘ matchingEntryWidthSlot))
    (.seq (matchingPrefixCountProgram (rg ∘ matchingPrefixOperandSlot)) (bclear (rg 2)))

theorem matchingPrefixCountFromWidth_exec (body : P → Pr P T Q A U)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg) (Ln Lk Le n K L : ℕ)
    (hn : n < 2 ^ Ln) (hk : K < 2 ^ Lk) (he : 2 * L + 2 < 2 ^ Le)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : S.R (rg 0) = binSyms Ln n) (hstride : S.R (rg 1) = binSyms Lk K)
    (hwidth : S.R (rg 11) = binSyms Le L)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 10 → j ≠ 11 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ matchingPrefixCountCost Ln Lk Le + 24 * Le + 29 ∧
      Exec body (matchingPrefixCountFromWidthProgram rg) (mk v S) m
        (mk v' { S with R := (Function.update S.R (rg 4)
          (binSyms (Ln + Lk + Le) ((n * K) * (2 * L + 2)))) }) := by
  have hentryBlank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → S.R ((rg ∘ matchingEntryWidthSlot) j) = [] := by
    intro j hj0 hj5
    fin_cases j <;> simp only [Fin.isValue, matchingEntryWidthSlot, Function.comp_apply] <;>
      first | contradiction | (apply hblank <;> decide)
  obtain ⟨v₁, hu₁, he₁⟩ := matchingEntryWidth_exec body (rg ∘ matchingEntryWidthSlot)
    (hrg.comp matchingEntryWidthSlot_injective) Le L v S hwidth hentryBlank
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms Le (2 * L + 2)) }
  let small := rg ∘ matchingPrefixOperandSlot
  have hs : Function.Injective small := hrg.comp matchingPrefixOperandSlot_injective
  have keep (j : Fin 11) (hj : j ≠ 2) : C.R (small j) = S.R (small j) := by
    apply Function.update_of_ne
    apply hrg.ne
    exact fun he => hj (Fin.ext (congrArg (fun a : Fin 13 => a.val) he))
  have hprefixBlank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 → C.R (small j) = [] := by
    intro j hj0 hj1 hj2 hj10
    rw [keep j hj2]
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 13 => a.val) he))
    · exact fun he => hj1 (Fin.ext (congrArg (fun a : Fin 13 => a.val) he))
    · exact fun he => hj10 (Fin.ext (congrArg (fun a : Fin 13 => a.val) he))
    · intro he
      have hv := congrArg Fin.val he
      change j.val = 11 at hv
      exact (Nat.ne_of_lt j.isLt) hv
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := matchingPrefixCount_exec body small hs Ln Lk Le n K (2 * L + 2)
    hn hk he v₁ C ((keep 0 (by decide)).trans hrows) ((keep 1 (by decide)).trans hstride)
    (by simp [C, small, matchingPrefixOperandSlot]) hprefixBlank
  let D : Stacks T A := { C with R := (Function.update C.R (rg 4)
    (binSyms (Ln + Lk + Le) ((n * K) * (2 * L + 2)))) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (rg 2) v₂ D
  have hlen : (D.R (rg 2)).length = Le := by simp [D, C, hrg.eq_iff, length_binSyms]
  have hfinal : ({ D with R := Function.update D.R (rg 2) [] } : Stacks T A) =
      { S with R := (Function.update S.R (rg 4) (binSyms (Ln + Lk + Le) ((n * K) * (2 * L + 2)))) } := by
    congr 1
    funext x
    by_cases hx : x = rg 2
    · subst x; simp [hrg.eq_iff, hblank 2 (by decide) (by decide) (by decide) (by decide)]
    · by_cases hy : x = rg 4 <;> simp [D, C, hx, hy, hrg.eq_iff]
  rw [hlen, hfinal] at he₃
  exact ⟨v₃, (22 * Le + 27) + (m₂ + (2 * Le + 2)), hu₃.trans (hu₂.trans hu₁),
    by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

def matchingPrefixCountScope (rg : Fin 13 → Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (matchingPrefixCountFromWidthProgram rg) (.seq call (bclear (rg 4)))

/-- A compiler call may borrow the generated count without retaining any new tape. -/
theorem matchingPrefixCountScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg) (Ln Lk Le n K L : ℕ)
    (hn : n < 2 ^ Ln) (hk : K < 2 ^ Lk) (he : 2 * L + 2 < 2 ^ Le)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : S.R (rg 0) = binSyms Ln n) (hstride : S.R (rg 1) = binSyms Lk K)
    (hwidth : S.R (rg 11) = binSyms Le L)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 10 → j ≠ 11 → S.R (rg j) = [])
    (str : Fin T) (hstr : str ≠ rg 4) (output : List (Fin (A + 4))) (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := (Function.update S.R (rg 4)
        (binSyms (Ln + Lk + Le) ((n * K) * (2 * L + 2)))) }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R str output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ matchingPrefixCountCost Ln Lk Le + 24 * Le + 29 + price + 2 * (Ln + Lk + Le) + 2 ∧
      Exec body (matchingPrefixCountScope rg call) (mk v S) m
        (mk v' { S with R := Function.update S.R str output }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := matchingPrefixCountFromWidth_exec body rg hrg Ln Lk Le n K L
    hn hk he v S hrows hstride hwidth hblank
  let C : Stacks T A := { S with R := (Function.update S.R (rg 4)
    (binSyms (Ln + Lk + Le) ((n * K) * (2 * L + 2)))) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R str output }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (rg 4) v₂ D
  have hlen : (D.R (rg 4)).length = Ln + Lk + Le := by
    simp [D, C, hstr.symm, length_binSyms]
  have hfinal : ({ D with R := Function.update D.R (rg 4) [] } : Stacks T A) =
      { S with R := Function.update S.R str output } := by
    congr 1
    funext x
    by_cases hx : x = rg 4
    · subst x; simp [hstr.symm, hblank 4 (by decide) (by decide) (by decide) (by decide)]
    · by_cases hy : x = str <;> simp [D, C, hx, hy, hstr]
  rw [hlen, hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + (2 * (Ln + Lk + Le) + 2)), hu₃.trans (hu₂.trans hu₁),
    by omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
