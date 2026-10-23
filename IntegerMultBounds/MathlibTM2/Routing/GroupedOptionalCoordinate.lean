module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryGroupedPosition
public import IntegerMultBounds.MathlibTM2.Routing.SparseOptionalCoordinateEmit

/-! Generate and emit grouped sparse coordinates from live dimensions, source
operands and activity. The generated position is erased after emission. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive GroupedCoordinateReg where
  | arithmetic (r : GroupedPositionReg)
  | last | wire | one | selector | gap | dst
  deriving DecidableEq

variable {T Q A : ℕ} {P U : Type}

def groupedOptionalCoordinateProgram (activity : Fin T) (rg : GroupedCoordinateReg → Fin T) : Pr P T Q A U :=
  .seq (binaryGroupedPositionProgram (fun r => rg (.arithmetic r)))
    (.seq (sparseOptionalCoordinateProgram activity (rg .last) (rg (.arithmetic .dst))
      (rg .wire) (rg .one) (rg .selector) (rg .gap) (rg .dst)
      (rg (.arithmetic .tx)) (rg (.arithmetic .ty)) (rg (.arithmetic .tz)) (rg (.arithmetic .divTmp)))
      (bclear (rg (.arithmetic .dst))))

theorem groupedOptionalCoordinate_exec (body : P → Pr P T Q A U)
    (activity : Fin T) (rg : GroupedCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (hactivityPos : activity ≠ rg (.arithmetic .dst))
    (Li Lg Lk Ls i g k b N q : ℕ) (enabled : Bool) (activityRest : List (Fin (A + 4)))
    (hi : i < 2 ^ Li) (hg : g < 2 ^ Lg) (hgpositive : 0 < g) (hk : k < 2 ^ Lk)
    (hwidth : Lg ≤ Li + Lk) (hN : N < 2 ^ (Li + Lk))
    (hpos : i / g * k + (i % g + b) < N) (hq : q + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R (rg (.arithmetic .index)) = binSyms Li i)
    (hgroup : S.R (rg (.arithmetic .group)) = binSyms Lg g)
    (hstride : S.R (rg (.arithmetic .stride)) = binSyms Lk k)
    (hbase : S.R (rg (.arithmetic .base)) = binSyms (Li + Lk) b)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (N - 1))
    (hwire : S.R (rg .wire) = binSyms Ls q) (hone : S.R (rg .one) = binSyms Ls 1)
    (hactivity : S.R activity = bitSymbol enabled :: activityRest)
    (hblank : ∀ r, r ≠ .arithmetic .index → r ≠ .arithmetic .group → r ≠ .arithmetic .stride →
      r ≠ .arithmetic .base → r ≠ .last → r ≠ .wire → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryGroupedPositionCost Li Lg Lk + 18 * (Li + Lk) + 16 * Ls + 39 ∧
      Exec body (groupedOptionalCoordinateProgram activity rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (binSyms (Li + Lk) (N - 1 - (i / g * k + (i % g + b))) ++ separator ::
            (binSyms Ls (if enabled then q + 1 else 0) ++ separator :: S.R (rg .dst))) }) := by
  have harithmetic : Function.Injective (fun r => rg (.arithmetic r)) :=
    fun _ _ h => GroupedCoordinateReg.arithmetic.inj (hrg h)
  have ha (r : GroupedPositionReg) (hi : r ≠ .index) (hg : r ≠ .group) (hk : r ≠ .stride) (hb : r ≠ .base) :
      S.R (rg (.arithmetic r)) = [] := by
    apply hblank <;> simp [hi, hg, hk, hb]
  obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := binaryGroupedPosition_exec body (fun r => rg (.arithmetic r)) harithmetic
    Li Lg Lk i g k b hi hg hgpositive hk hwidth (by omega) v S hindex hgroup hstride hbase ha
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg (.arithmetic .dst)) (binSyms (Li + Lk) (i / g * k + (i % g + b))) }
  have hkeep (r : GroupedCoordinateReg) (hr : r ≠ .arithmetic .dst) : S₁.R (rg r) = S.R (rg r) := by
    simp [S₁, hrg.eq_iff, hr]
  have hb (r : GroupedCoordinateReg) (hr : r ≠ .arithmetic .dst)
      (hi : r ≠ .arithmetic .index) (hg : r ≠ .arithmetic .group) (hk : r ≠ .arithmetic .stride)
      (hb : r ≠ .arithmetic .base) (hl : r ≠ .last) (hw : r ≠ .wire) (h1 : r ≠ .one) (hd : r ≠ .dst) :
      S₁.R (rg r) = [] := (hkeep r hr).trans (hblank r hi hg hk hb hl hw h1 hd)
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := sparseOptionalCoordinate_exec body
    (rg .last) (rg (.arithmetic .dst)) (rg .wire) (rg .one) (rg .selector) (rg .gap) (rg .dst)
    (rg (.arithmetic .tx)) (rg (.arithmetic .ty)) (rg (.arithmetic .tz)) (rg (.arithmetic .divTmp))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff]) activity enabled activityRest (Li + Lk) Ls N
    (i / g * k + (i % g + b)) q hN hpos hq v₁ S₁
    ((hkeep .last (by decide)).trans hlast) (by simp [S₁]) ((hkeep .wire (by decide)).trans hwire)
    ((hkeep .one (by decide)).trans hone)
    (by apply hb <;> decide) (by apply hb <;> decide)
    ((Function.update_of_ne hactivityPos _ _).trans hactivity)
    (by apply hb <;> decide) (by apply hb <;> decide) (by apply hb <;> decide)
  rw [hkeep .dst (by decide)] at he₂
  let out := binSyms (Li + Lk) (N - 1 - (i / g * k + (i % g + b))) ++ separator ::
    (binSyms Ls (if enabled then q + 1 else 0) ++ separator :: S.R (rg .dst))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .dst) out }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg (.arithmetic .dst)) v₂ S₂
  have hp : S₂.R (rg (.arithmetic .dst)) = binSyms (Li + Lk) (i / g * k + (i % g + b)) := by
    simp [S₂, S₁, hrg.eq_iff]
  have hf : Function.update S₂.R (rg (.arithmetic .dst)) [] = Function.update S.R (rg .dst) out := by
    funext j
    by_cases hp : j = rg (.arithmetic .dst)
    · subst j; simp [hrg.eq_iff, hblank]
    · by_cases hd : j = rg .dst
      · subst j; simp [S₂, S₁, hp]
      · simp [S₂, S₁, hp, hd]
  rw [hf, hp, length_binSyms] at he₃
  exact ⟨v₃, n₁ + (n₂ + (2 * (Li + Lk) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
