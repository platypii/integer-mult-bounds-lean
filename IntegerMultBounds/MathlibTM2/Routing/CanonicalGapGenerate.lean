module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCeilLog
public import IntegerMultBounds.MathlibTM2.Routing.BinaryShiftBits
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterArithmetic
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Generate the canonical logarithmic routing gap from binary dimension.
Only gap output changes; logarithm, scaled logarithm and constant six are erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalGapLogSlot : Fin 6 → Fin 9 := ![0,2,1,5,6,8]
theorem canonicalGapLogSlot_injective : Function.Injective canonicalGapLogSlot := by decide +kernel

def canonicalGapGenerateProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (binaryCeilLogProgram (rg ∘ canonicalGapLogSlot))
    (.seq (bcopy (rg 1) (rg 2) (rg 5) (rg 6))
      (.seq (binaryShiftBitsProgram (rg 2) (rg 5) [false,false])
        (.seq (.seq (bzero (rg 0) (rg 3) (rg 5)) (binaryShiftBitsProgram (rg 3) (rg 5) [true,true,false]))
          (.seq (badd (rg 2) (rg 3) (rg 4) (rg 5) (rg 6) (rg 7) (rg 8)) (metadataClean [rg 1,rg 2,rg 3])))))

theorem canonicalGapGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hfit : canonicalRouterGap n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L n)
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 8 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 4 * L * L + 78 * L + 115 ∧
      Exec body (canonicalGapGenerateProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 4) (binSyms L (canonicalRouterGap n)) }) := by
  have hlogBlank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → S.R ((rg ∘ canonicalGapLogSlot) j) = [] := by
    intro j hj0 hj5
    fin_cases j <;> simp only [Function.comp_apply, canonicalGapLogSlot, Fin.isValue] <;>
      first | contradiction | (apply hblank <;> decide)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryCeilLog_exec body (rg ∘ canonicalGapLogSlot)
    (hrg.comp canonicalGapLogSlot_injective) L n hn v S hsrc hlogBlank
  let C : Stacks T A := { S with R := Function.update S.R (rg 1) (binSyms L (Nat.clog 2 (n + 2))) }
  obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec (body := body) (a := rg 1) (c := rg 2) (t₁ := rg 5) (t₂ := rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₁ C
    (by simp [C, hrg.eq_iff, hblank 5 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 6 (by decide) (by decide)])
  have hc1 : C.R (rg 1) = binSyms L (Nat.clog 2 (n + 2)) := by simp [C]
  have hc2 : C.R (rg 2) = [] := by simp [C, hrg.eq_iff, hblank 2 (by decide) (by decide)]
  rw [hc1, hc2, List.append_nil, length_binSyms] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 2) (binSyms L (Nat.clog 2 (n + 2))) }
  obtain ⟨v₃, hu₃, he₃⟩ := binaryShiftBits_exec body (rg 2) (rg 5) (hrg.ne (by decide)) [false,false]
    L (Nat.clog 2 (n + 2)) v₂ D (by simp [D])
    (by simp [D, C, hrg.eq_iff, hblank 5 (by decide) (by decide)])
  have hquad : binaryShiftBitsValue (Nat.clog 2 (n + 2)) [false,false] = 4 * Nat.clog 2 (n + 2) := by
    simp [binaryShiftBitsValue]
    omega
  rw [hquad] at he₃
  let E : Stacks T A := { D with R := Function.update D.R (rg 2) (binSyms L (4 * Nat.clog 2 (n + 2))) }
  obtain ⟨v₄, hu₄, he₄⟩ := binaryLiteral_exec body (rg 0) (rg 3) (rg 5)
    (by simp [List.nodup_cons, hrg.eq_iff]) [true,true,false] L v₃ E
    (by simp [E, D, C, hrg.eq_iff, hsrc, length_binSyms])
    (by simp [E, D, C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
    (by simp [E, D, C, hrg.eq_iff, hblank 5 (by decide) (by decide)])
  have hsix : binaryShiftBitsValue 0 [true,true,false] = 6 := rfl
  rw [hsix] at he₄
  let F : Stacks T A := { E with R := Function.update E.R (rg 3) (binSyms L 6) }
  obtain ⟨v₅, hu₅, _, _, he₅⟩ := badd_exec (body := body)
    (a := rg 2) (b := rg 3) (c := rg 4) (tx := rg 5) (ty := rg 6) (tz := rg 7) (cy := rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by unfold canonicalRouterGap at hfit; omega : 4 * Nat.clog 2 (n + 2) < 2 ^ L)
    (by unfold canonicalRouterGap at hfit; omega : 6 < 2 ^ L) v₄ F
    (by simp [F, E, hrg.eq_iff]) (by simp [F])
    (by simp [F, E, D, C, hrg.eq_iff, hblank 5 (by decide) (by decide)])
    (by simp [F, E, D, C, hrg.eq_iff, hblank 6 (by decide) (by decide)])
    (by simp [F, E, D, C, hrg.eq_iff, hblank 7 (by decide) (by decide)])
  have hsum : 4 * Nat.clog 2 (n + 2) + 6 = canonicalRouterGap n := by unfold canonicalRouterGap; omega
  have hf4 : F.R (rg 4) = [] := by simp [F, E, D, C, hrg.eq_iff, hblank 4 (by decide) (by decide)]
  rw [hsum, Nat.mod_eq_of_lt hfit, hf4, List.append_nil] at he₅
  let B : Stacks T A := { F with R := Function.update F.R (rg 4) (binSyms L (canonicalRouterGap n)) }
  obtain ⟨v₆, hu₆, he₆⟩ := metadataClean_exec body [rg 1,rg 2,rg 3] (by simp [hrg.eq_iff]) v₅ B
  have hcost : metadataCleanCost B.R [rg 1,rg 2,rg 3] = 6 * L + 7 := by
    simp [metadataCleanCost, B, F, E, D, C, hrg.eq_iff, length_binSyms]
    ring
  have hfinal : metadataCleared B.R [rg 1,rg 2,rg 3] = Function.update S.R (rg 4) (binSyms L (canonicalRouterGap n)) := by
    funext x
    by_cases hx : x ∈ [rg 1,rg 2,rg 3]
    · rw [metadataCleared_at _ _ _ hx]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · simpa [hrg.eq_iff] using (hblank 1 (by decide) (by decide)).symm
      · simpa [hrg.eq_iff] using (hblank 2 (by decide) (by decide)).symm
      · simpa [hrg.eq_iff] using (hblank 3 (by decide) (by decide)).symm
    · rw [metadataCleared_keep _ _ _ hx]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      by_cases h4 : x = rg 4 <;> simp [B, F, E, D, C, h4, hx.1, hx.2.1, hx.2.2]
  rw [hcost, hfinal] at he₆
  refine ⟨v₆, m₁ + ((6 * L + 6) + ((2 * (4 * L + 8) + 1) +
    (((4 * L + 4) + (3 * (4 * L + 8) + 1)) + ((8 * L + 8) + (6 * L + 7))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))⟩
  omega

end IntegerMultBounds.MathlibTM2.Routing
