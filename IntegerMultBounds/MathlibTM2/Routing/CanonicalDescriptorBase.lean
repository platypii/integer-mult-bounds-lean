module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCeilLog
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorMagnitude

/-! Generate the exact common descriptor base width by subtracting borrowed span
from dimension and executing `clog 2 (remaining+2)`. The subtraction word is erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalDescriptorLogSlot : Fin 6 → Fin 8 := ![2,4,3,5,6,7]
theorem canonicalDescriptorLogSlot_injective : Function.Injective canonicalDescriptorLogSlot := by decide +kernel

def canonicalDescriptorBaseProgram (rg : Fin 8 → Fin T) : Pr P T Q A U :=
  .seq (bsub (rg 0) (rg 1) (rg 2) (rg 4) (rg 5) (rg 6) (rg 7))
    (.seq (binaryCeilLogProgram (rg ∘ canonicalDescriptorLogSlot)) (bclear (rg 2)))

theorem canonicalDescriptorBase_exec (body : P → Pr P T Q A U)
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg) (L n w : ℕ)
    (hn : n < 2 ^ L) (hw : w ≤ n) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hborrowed : S.R (rg 1) = binSyms L w)
    (hblank : ∀ j : Fin 8, j ≠ 0 → j ≠ 1 → j ≠ 7 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 4 * L * L + 44 * L + 58 ∧
      Exec body (canonicalDescriptorBaseProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 3) (binSyms L (Nat.clog 2 (n - w + 2))) }) := by
  obtain ⟨v₁, hu₁, _, _, he₁⟩ := bsub_exec (body := body)
    (a := rg 0) (b := rg 1) (c := rg 2) (tx := rg 4) (ty := rg 5) (tz := rg 6) (cy := rg 7)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hn (hw.trans_lt hn)
    v S hdimension hborrowed (hblank 4 (by decide) (by decide) (by decide))
    (hblank 5 (by decide) (by decide) (by decide)) (hblank 6 (by decide) (by decide) (by decide))
  have hsub : (n + 2 ^ L - w) % 2 ^ L = n - w := by
    rw [show n + 2 ^ L - w = (n - w) + 2 ^ L by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt ((Nat.sub_le n w).trans_lt hn)]
  rw [hsub, hblank 2 (by decide) (by decide) (by decide), List.append_nil] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (n - w)) }
  have hlogBlank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → C.R ((rg ∘ canonicalDescriptorLogSlot) j) = [] := by
    intro j hj0 hj5
    fin_cases j
    · exact (hj0 rfl).elim
    · simpa [C, canonicalDescriptorLogSlot, hrg.eq_iff] using hblank 4 (by decide) (by decide) (by decide)
    · simpa [C, canonicalDescriptorLogSlot, hrg.eq_iff] using hblank 3 (by decide) (by decide) (by decide)
    · simpa [C, canonicalDescriptorLogSlot, hrg.eq_iff] using hblank 5 (by decide) (by decide) (by decide)
    · simpa [C, canonicalDescriptorLogSlot, hrg.eq_iff] using hblank 6 (by decide) (by decide) (by decide)
    · exact (hj5 rfl).elim
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryCeilLog_exec body (rg ∘ canonicalDescriptorLogSlot)
    (hrg.comp canonicalDescriptorLogSlot_injective) L (n - w) ((Nat.sub_le n w).trans_lt hn) v₁ C
    (by change C.R (rg 2) = _; simp [C]) hlogBlank
  let D : Stacks T A := { C with R := Function.update C.R (rg 3) (binSyms L (Nat.clog 2 (n - w + 2))) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (rg 2) v₂ D
  have hlen : (D.R (rg 2)).length = L := by simp [D, C, hrg.eq_iff, length_binSyms]
  have hfinal : ({ D with R := Function.update D.R (rg 2) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 3) (binSyms L (Nat.clog 2 (n - w + 2))) } := by
    congr 1
    funext x
    by_cases h2 : x = rg 2
    · subst x; simp [hrg.eq_iff, hblank 2 (by decide) (by decide) (by decide)]
    · by_cases h3 : x = rg 3 <;> simp [D, C, h2, h3, hrg.eq_iff]
  rw [hlen, hfinal] at he₃
  exact ⟨v₃, (8 * L + 8) + (m₂ + (2 * L + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

/-- The generated base word is exactly the existing canonical stride-bit width. -/
theorem canonicalDescriptorStrideWidth_exec (body : P → Pr P T Q A U)
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n))
    (v : HS T Q A U) (S : Stacks T A) (hdimension : S.R (rg 0) = binSyms L n)
    (hborrowed : S.R (rg 1) = binSyms L (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)))
    (hblank : ∀ j : Fin 8, j ≠ 0 → j ≠ 1 → j ≠ 7 → S.R (rg j) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 4 * L * L + 44 * L + 58 ∧
      Exec body (canonicalDescriptorBaseProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 3) (binSyms L (canonicalStageWidths p).strideBits) }) := by
  dsimp only
  have hw : routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) ≤ n := by
    have ht := routerGeometry_decomposition n (canonicalRouterStride n) (canonicalRouterGap n) hlarge
    omega
  have heq := (canonicalStageWidths_router n hlarge r).2.2.1
  simpa only [heq] using canonicalDescriptorBase_exec body rg hrg L n _ hn hw v S hdimension hborrowed hblank

end IntegerMultBounds.MathlibTM2.Routing
