module

public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometryDigitTail
public import IntegerMultBounds.MathlibTM2.Routing.RouterBorrowedWidth

/-! Generate the common routing geometry from binary dimension, stride, gap and
word width. Only digit count, terminal tail and borrowed-span outputs change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerGeometryTailSlot : Fin 15 → Fin 17 := Fin.castLE (by decide)
def routerGeometryBorrowedSlot : Fin 11 → Fin 17 := ![11,2,15,3,4,5,6,7,16,8,9]

theorem routerGeometryTailSlot_injective : Function.Injective routerGeometryTailSlot := by decide +kernel
theorem routerGeometryBorrowedSlot_injective : Function.Injective routerGeometryBorrowedSlot := by decide +kernel

def routerGeometryGenerateProgram (rg : Fin 17 → Fin T) : Pr P T Q A U :=
  .seq (routerGeometryDigitTailProgram (rg ∘ routerGeometryTailSlot))
    (routerBorrowedWidthProgram (rg ∘ routerGeometryBorrowedSlot))

def routerGeometryBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 17 → Fin T)
    (L n K G : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R (rg 11) (binSyms L (routerDigits n K G)))
    (rg 14) (binSyms L (routerTail n K G))) (rg 16) (binSyms L (routerBorrowed n K G))

theorem routerGeometryGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 17 → Fin T) (hrg : Function.Injective rg) (M L n K G : ℕ)
    (hL : L < 2 ^ M) (hn : n < 2 ^ L) (hK : 0 < K) (hKn : K ≤ n) (hdivisor : K + 3 * G < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hstride : S.R (rg 1) = binSyms L K)
    (hgap : S.R (rg 2) = binSyms L G) (hwidth : S.R (rg 15) = binSyms M L)
    (hblank : ∀ j : Fin 17, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 9 → j ≠ 15 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 36 * L * L + 177 * L + 136 + M * (4 * L + 11) ∧
      Exec body (routerGeometryGenerateProgram rg) (mk v S) m
        (mk v' { S with R := routerGeometryBank S.R rg L n K G }) := by
  have htailBlank : ∀ j : Fin 15, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 9 →
      S.R ((rg ∘ routerGeometryTailSlot) j) = [] := by
    intro j hj0 hj1 hj2 hj9
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 17 => a.val) he))
    · exact fun he => hj1 (Fin.ext (congrArg (fun a : Fin 17 => a.val) he))
    · exact fun he => hj2 (Fin.ext (congrArg (fun a : Fin 17 => a.val) he))
    · exact fun he => hj9 (Fin.ext (congrArg (fun a : Fin 17 => a.val) he))
    · intro he
      have hv := congrArg Fin.val he
      change j.val = 15 at hv
      exact (Nat.ne_of_lt j.isLt) hv
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := routerGeometryDigitTail_exec body (rg ∘ routerGeometryTailSlot)
    (hrg.comp routerGeometryTailSlot_injective) L n K G hn hK hKn hdivisor v S hdimension hstride hgap htailBlank
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R (rg 11)
    (binSyms L (routerDigits n K G))) (rg 14) (binSyms L (routerTail n K G))) }
  have keep (j : Fin 17) (hj11 : j ≠ 11) (hj14 : j ≠ 14) : C.R (rg j) = S.R (rg j) := by
    simp [C, hrg.eq_iff, hj11, hj14]
  have hsep : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 →
      let a := routerGeometryBorrowedSlot j
      a ≠ 11 ∧ a ≠ 14 ∧ a ≠ 0 ∧ a ≠ 1 ∧ a ≠ 2 ∧ a ≠ 9 ∧ a ≠ 15 := by decide +kernel
  have hborrowedBlank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 →
      C.R ((rg ∘ routerGeometryBorrowedSlot) j) = [] := by
    intro j hj0 hj1 hj2 hj10
    obtain ⟨h11,h14,h0,h1,h2,h9,h15⟩ := hsep j hj0 hj1 hj2 hj10
    exact (keep _ h11 h14).trans (hblank _ h0 h1 h2 h9 h15)
  have hdigits : routerDigits n K G < 2 ^ L :=
    ((Nat.div_le_self (n - K) (K + 3 * G)).trans (Nat.sub_le n K)).trans_lt hn
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := routerBorrowedWidth_exec body (rg ∘ routerGeometryBorrowedSlot)
    (hrg.comp routerGeometryBorrowedSlot_injective) M L n K G hL hdigits (by omega) v₁ C
    (by change C.R (rg 11) = _; simp [C, hrg.eq_iff])
    ((keep 2 (by decide) (by decide)).trans hgap)
    ((keep 15 (by decide) (by decide)).trans hwidth) hborrowedBlank
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  nlinarith only [hm₁, hm₂]

end IntegerMultBounds.MathlibTM2.Routing
