module

public import IntegerMultBounds.MathlibTM2.Routing.SharedInputBank

/-! Actual generation of all shared raw words from three binary inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

/-- For positive address width, generate record count, unary width and first-bit
mask, preserving binary inputs and restoring all five scratch tapes. -/
theorem sharedInput_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (rg : SharedInputReg → Fin T) (hrg : Function.Injective rg) (L n rows : ℕ) (hn : n < 2 ^ L) (hn0 : 0 < n)
    (rowBits : List Bool) (hrowValue : Counter.value rowBits = rows)
    (v : HS T Q A U) (S : Stacks T A) (hwidth : S.R (rg .width) = binSyms L n)
    (hrows : S.R (rg .rows) = rowBits.map bitSymbol)
    (hfield0 : S.R (rg .field) = []) (hrecords0 : S.R (rg .records) = []) (hmask0 : S.R (rg .mask) = [])
    (hscratch : ∀ i, S.R (rg (.scratch i)) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (4 * n + 11) + 22 * n + 6 * rowBits.length + 46 ∧
      Exec body (sharedInputProgram rg) (mk v S) m
        (mk v' { S with R := sharedInputBank S.R rg n rows rowBits.length }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body (a := rg .width) (z := rg .field)
    (w := rg (.scratch 0)) (t := rg (.scratch 1)) (t₂ := rg (.scratch 2))
    (by simp [List.nodup_cons, hrg.eq_iff]) hn v S hwidth (hscratch 0) (hscratch 1) (hscratch 2)
  rw [hfield0, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .field) (List.replicate n tick) }
  let recordWord : List (Fin (A + 4)) := binSyms (n + rowBits.length) (rows * 2 ^ n)
  have hrecord : List.replicate n (bitSymbol false) ++ rowBits.map bitSymbol = recordWord := by
    rw [binaryScale_binSyms, hrowValue]
    simp only [recordWord, Nat.mul_comm]
  have hfield₁ : S₁.R (rg .field) = List.replicate n tick := by simp [S₁]
  have hrows₁ : S₁.R (rg .rows) = rowBits.map bitSymbol := by simp [S₁, hrg.eq_iff, hrows]
  obtain ⟨v₂, hu₂, he₂⟩ := binaryScale_exec body (rg .field) (rg .rows) (rg .records) (rg (.scratch 1)) (rg (.scratch 2))
    (by simp [List.nodup_cons, hrg.eq_iff]) v₁ S₁
    (by simp [S₁, hrg.eq_iff, hrecords0]) (by simp [S₁, hrg.eq_iff, hscratch]) (by simp [S₁, hrg.eq_iff, hscratch])
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .records) recordWord }
  have he₂' : Exec body (binaryScaleProgram (rg .field) (rg .rows) (rg .records) (rg (.scratch 1)) (rg (.scratch 2)))
      (mk v₁ S₁) (6 * (rowBits.length + n) + 12) (mk v₂ S₂) := by
    simpa only [hfield₁, hrows₁, List.length_replicate, List.length_map, hrecord] using he₂
  have hfield₂ : S₂.R (rg .field) = List.replicate n tick := by simp [S₂, S₁, hrg.eq_iff]
  obtain ⟨v₃, hu₃, he₃⟩ := unaryPredecessor_exec body (rg .field) (rg (.scratch 3)) (rg (.scratch 1)) (rg (.scratch 2))
    (by simp [List.nodup_cons, hrg.eq_iff]) v₂ S₂
    (by simp [S₂, S₁, hrg.eq_iff, hscratch]) (by simp [S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₂, S₁, hrg.eq_iff, hscratch])
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R (rg (.scratch 3)) (List.replicate (n - 1) tick) }
  have he₃' : Exec body (unaryPredecessorProgram (rg .field) (rg (.scratch 3)) (rg (.scratch 1)) (rg (.scratch 2)))
      (mk v₂ S₂) (6 * n + 7) (mk v₃ S₃) := by
    simpa only [hfield₂, List.length_replicate, List.tail_replicate] using he₃
  have hzero₃ : S₃.R (rg (.scratch 4)) = [] := by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch]
  have hhigh₃ : S₃.R (rg (.scratch 3)) = List.replicate (n - 1) tick := by simp [S₃]
  obtain ⟨v₄, hu₄, he₄⟩ := sourceMask_exec body (rg (.scratch 4)) (rg (.scratch 3)) (rg .mask)
    (rg (.scratch 1)) (rg (.scratch 2)) (by simp [List.nodup_cons, hrg.eq_iff]) v₃ S₃
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hmask0]) (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch])
    (by simp [S₃, S₂, S₁, hrg.eq_iff, hscratch])
  have hsize : (S₃.R (rg (.scratch 4))).length + 1 + (S₃.R (rg (.scratch 3))).length = n := by
    rw [hzero₃, hhigh₃, List.length_nil, List.length_replicate]
    omega
  rw [hsize] at he₄
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R (rg .mask) (binSyms n 1) }
  have he₄' : Exec body (sourceMaskProgram (rg (.scratch 4)) (rg (.scratch 3)) (rg .mask) (rg (.scratch 1)) (rg (.scratch 2)))
      (mk v₃ S₃) (6 * (n - 1) + 19) (mk v₄ S₄) := by
    simpa only [hzero₃, hhigh₃, List.length_nil, List.length_replicate, pow_zero, Nat.mul_zero, Nat.zero_add] using he₄
  have hhigh₄ : S₄.R (rg (.scratch 3)) = List.replicate (n - 1) tick := by simp [S₄, S₃, hrg.eq_iff]
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec body (rg (.scratch 3)) v₄ S₄
  have hfinal : Function.update S₄.R (rg (.scratch 3)) [] = sharedInputBank S.R rg n rows rowBits.length := by
    funext j
    by_cases hj : j = rg (.scratch 3)
    · subst j
      simp [sharedInputBank, hrg.eq_iff, hscratch]
    · by_cases hm : j = rg .mask
      · subst j; simp [S₄, sharedInputBank, hj]
      · simp [S₄, S₃, S₂, S₁, sharedInputBank, recordWord, hj, hm]
  have he₅' : Exec body (bclear (rg (.scratch 3))) (mk v₄ S₄) (2 * (n - 1) + 2)
      (mk v₅ { S with R := sharedInputBank S.R rg n rows rowBits.length }) := by
    simpa only [hhigh₄, List.length_replicate, hfinal] using he₅
  refine ⟨v₅, m₁ + ((6 * (rowBits.length + n) + 12) + ((6 * n + 7) + ((6 * (n - 1) + 19) + (2 * (n - 1) + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), by omega, ?_⟩
  exact Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅')))


/-- Binary dimensions are the only nonempty initial shared-input operands. -/
def sharedInputInitialWords {A : ℕ} (L n Lb B : ℕ) (rowBits : List Bool) :
    SharedInputReg → List (Fin (A + 4))
  | .width => binSyms L n
  | .rows => rowBits.map bitSymbol
  | .block => binSyms Lb B
  | _ => []

noncomputable def sharedInputInitialBank {T A : ℕ} (rg : SharedInputReg → Fin T)
    (outside : Fin T → List (Fin (A + 4))) (L n Lb B : ℕ) (rowBits : List Bool) :
    Fin T → List (Fin (A + 4)) :=
  Function.extend rg (sharedInputInitialWords L n Lb B rowBits) outside

/-- Generate all shared raw counters from the constructed operand bank. -/
theorem sharedInputInitial_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (rg : SharedInputReg → Fin T) (hrg : Function.Injective rg)
    (outside : Fin T → List (Fin (A + 4))) (L n Lb B rows : ℕ)
    (hn : n < 2 ^ L) (hn0 : 0 < n) (rowBits : List Bool)
    (hrowValue : Counter.value rowBits = rows) (v : HS T Q A U) (S : Stacks T A)
    (hbank : S.R = sharedInputInitialBank rg outside L n Lb B rowBits) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (4 * n + 11) + 22 * n + 6 * rowBits.length + 46 ∧
      Exec body (sharedInputProgram rg) (mk v S) m
        (mk v' { S with R := sharedInputBank S.R rg n rows rowBits.length }) := by
  have hat (r : SharedInputReg) : S.R (rg r) = sharedInputInitialWords L n Lb B rowBits r := by
    rw [hbank]
    exact hrg.extend_apply _ _ r
  exact sharedInput_exec body rg hrg L n rows hn hn0 rowBits hrowValue v S
    (hat .width) (hat .rows) (hat .field) (hat .records) (hat .mask) (fun i => hat (.scratch i))

theorem sharedInputInitialBank_off {T A : ℕ} (rg : SharedInputReg → Fin T)
    (outside : Fin T → List (Fin (A + 4))) (L n Lb B : ℕ) (rowBits : List Bool)
    (j : Fin T) (hj : ∀ r, rg r ≠ j) :
    sharedInputInitialBank rg outside L n Lb B rowBits j = outside j := by
  apply Function.extend_apply'
  rintro ⟨r, hr⟩
  exact hj r hr

end IntegerMultBounds.MathlibTM2.Routing
