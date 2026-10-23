module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryAffinePosition
public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Generate grouped positions floor(index / group) * stride + index % group +
base from live binary dimensions. Division and affine arithmetic restore their
inputs; all generated operands are erased. Only the position output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive GroupedPositionReg where
  | index | group | stride | base | quotient | remainder | divWide | divRem | divTmp
  | offset | product | dst | muls | mult | tx | ty | tz
  deriving DecidableEq

variable {T Q A : ℕ} {P U : Type}

def binaryGroupedPositionProgram (rg : GroupedPositionReg → Fin T) : Pr P T Q A U :=
  .seq (bdivmod (rg .index) (rg .group) (rg .quotient) (rg .remainder)
    (rg .divWide) (rg .divRem) (rg .divTmp) (rg .tx) (rg .ty) (rg .tz) (rg .divTmp))
    (.seq (bwiden (rg .remainder) (rg .base) (rg .divWide) (rg .tx) (rg .ty))
      (.seq (badd (rg .remainder) (rg .base) (rg .offset) (rg .tx) (rg .ty) (rg .tz) (rg .divTmp))
        (.seq (binaryAffinePositionProgram (rg .quotient) (rg .stride) (rg .product) (rg .offset)
          (rg .dst) (rg .muls) (rg .mult) (rg .tx) (rg .ty) (rg .tz) (rg .divTmp))
          (metadataClean [rg .quotient, rg .remainder, rg .offset]))))

def binaryGroupedPositionCost (Li Lg Lk : ℕ) :=
  Li * (12 * Lg + 35) + Li * (12 * (Li + Lk) + 20) +
    20 * Lg + 50 * (Li + Lk) + 2 * Li + 103

theorem binaryGroupedPosition_exec (body : P → Pr P T Q A U)
    (rg : GroupedPositionReg → Fin T) (hrg : Function.Injective rg)
    (Li Lg Lk i g k b : ℕ) (hi : i < 2 ^ Li) (hg : g < 2 ^ Lg) (hgpositive : 0 < g)
    (hk : k < 2 ^ Lk) (hwidth : Lg ≤ Li + Lk)
    (hfit : i / g * k + (i % g + b) < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R (rg .index) = binSyms Li i) (hgroup : S.R (rg .group) = binSyms Lg g)
    (hstride : S.R (rg .stride) = binSyms Lk k) (hbase : S.R (rg .base) = binSyms (Li + Lk) b)
    (hblank : ∀ r, r ≠ .index → r ≠ .group → r ≠ .stride → r ≠ .base → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ binaryGroupedPositionCost Li Lg Lk ∧
      Exec body (binaryGroupedPositionProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (binSyms (Li + Lk) (i / g * k + (i % g + b))) }) := by
  have hquot : i / g < 2 ^ Li := (Nat.div_le_self i g).trans_lt hi
  have hrem : i % g < 2 ^ Lg := (Nat.mod_lt i hgpositive).trans hg
  have hsum : i % g + b < 2 ^ (Li + Lk) := by omega
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := bdivmod_exec body
    (a := rg .index) (b := rg .group) (q := rg .quotient) (r := rg .remainder)
    (bw := rg .divWide) (rr := rg .divRem) (t := rg .divTmp) (tx := rg .tx) (ty := rg .ty)
    (tz := rg .tz) (cy := rg .divTmp)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    hi hg hgpositive v S hindex hgroup
    (by apply hblank <;> decide) (by apply hblank <;> decide) (by apply hblank <;> decide)
    (by apply hblank <;> decide) (by apply hblank <;> decide) (by apply hblank <;> decide)
  have hqzero := hblank .quotient (by decide) (by decide) (by decide) (by decide)
  have hrzero := hblank .remainder (by decide) (by decide) (by decide) (by decide)
  rw [hqzero, hrzero, List.append_nil, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update (Function.update S.R (rg .quotient) (binSyms Li (i / g))) (rg .remainder) (binSyms Lg (i % g)) }
  obtain ⟨v₂, hu₂, he₂⟩ := bwiden_exec body
    (a := rg .remainder) (wR := rg .base) (cnt := rg .divWide) (t₁ := rg .tx) (t₂ := rg .ty)
    (by simp [List.nodup_cons, hrg.eq_iff]) hwidth hrem v₁ S₁
    (by simp [S₁]) (by simp [S₁, hrg.eq_iff, hbase])
    (by simp [S₁, hrg.eq_iff, hblank]) (by simp [S₁, hrg.eq_iff, hblank]) (by simp [S₁, hrg.eq_iff, hblank])
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .remainder) (binSyms (Li + Lk) (i % g)) }
  obtain ⟨v₃, hu₃, _, _, he₃⟩ := badd_exec body
    (a := rg .remainder) (b := rg .base) (c := rg .offset) (tx := rg .tx) (ty := rg .ty) (tz := rg .tz) (cy := rg .divTmp)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    (by omega : i % g < 2 ^ (Li + Lk)) (by omega : b < 2 ^ (Li + Lk)) v₂ S₂
    (by simp [S₂]) (by simp [S₂, S₁, hrg.eq_iff, hbase])
    (by simp [S₂, S₁, hrg.eq_iff, hblank]) (by simp [S₂, S₁, hrg.eq_iff, hblank]) (by simp [S₂, S₁, hrg.eq_iff, hblank])
  have ho : S₂.R (rg .offset) = [] := by simp [S₂, S₁, hrg.eq_iff, hblank]
  rw [Nat.mod_eq_of_lt hsum, ho, List.append_nil] at he₃
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R (rg .offset) (binSyms (Li + Lk) (i % g + b)) }
  obtain ⟨v₄, n₄, hu₄, ht₄, he₄⟩ := binaryAffinePosition_exec body
    (rg .quotient) (rg .stride) (rg .product) (rg .offset) (rg .dst) (rg .muls) (rg .mult)
    (rg .tx) (rg .ty) (rg .tz) (rg .divTmp)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    Li Lk (i / g) k (i % g + b) hquot hk hfit v₃ S₃
    (by simp [S₃, S₂, S₁, hrg.eq_iff]) (by simp [S₃, S₂, S₁, hrg.eq_iff, hstride]) (by simp [S₃])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hblank]) (by simp [S₃, S₂, S₁, hrg.eq_iff, hblank])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hblank]) (by simp [S₃, S₂, S₁, hrg.eq_iff, hblank])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hblank]) (by simp [S₃, S₂, S₁, hrg.eq_iff, hblank])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hblank])
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R (rg .dst) (binSyms (Li + Lk) (i / g * k + (i % g + b))) }
  obtain ⟨v₅, hu₅, he₅⟩ := metadataClean_exec body [rg .quotient, rg .remainder, rg .offset]
    (by simp [List.nodup_cons, hrg.eq_iff]) v₄ S₄
  have hc : metadataCleanCost S₄.R [rg .quotient, rg .remainder, rg .offset] = 2 * Li + 4 * (Li + Lk) + 7 := by
    simp [metadataCleanCost, S₄, S₃, S₂, S₁, hrg.eq_iff]; omega
  have hf : metadataCleared S₄.R [rg .quotient, rg .remainder, rg .offset] =
      Function.update S.R (rg .dst) (binSyms (Li + Lk) (i / g * k + (i % g + b))) := by
    funext j
    by_cases hq : j = rg .quotient
    · subst j; simp [metadataCleared, hrg.eq_iff, hblank]
    · by_cases hr : j = rg .remainder
      · subst j; simp [metadataCleared, hrg.eq_iff, hblank]
      · by_cases ho : j = rg .offset
        · subst j; simp [metadataCleared, hrg.eq_iff, hblank]
        · by_cases hd : j = rg .dst
          · subst j; simp [metadataCleared, S₄, hrg.eq_iff]
          · simp [metadataCleared, S₄, S₃, S₂, S₁, hq, hr, ho, hd]
  rw [hc, hf] at he₅
  refine ⟨v₅, n₁ + ((12 * (Li + Lk) + 18) + ((8 * (Li + Lk) + 8) + (n₄ + (2 * Li + 4 * (Li + Lk) + 7)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by dsimp only [binaryGroupedPositionCost]; omega, ?_⟩
  exact Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))

end IntegerMultBounds.MathlibTM2.Routing
