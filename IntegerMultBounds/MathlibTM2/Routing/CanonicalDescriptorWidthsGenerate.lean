module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorBase
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScalarWidth
public import IntegerMultBounds.MathlibTM2.Routing.BinarySuccessor

/-! Generate the exact common descriptor-width operands from dimension and
borrowed span, restoring every temporary arithmetic word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalDescriptorBaseSlot : Fin 8 → Fin 11 := Fin.castLE (by decide)
def canonicalDescriptorCounterSlot : Fin 6 → Fin 11 := ![9,2,10,4,5,7]
theorem canonicalDescriptorBaseSlot_injective : Function.Injective canonicalDescriptorBaseSlot := by decide +kernel
theorem canonicalDescriptorCounterSlot_injective : Function.Injective canonicalDescriptorCounterSlot := by decide +kernel

def canonicalDescriptorWidthsProgram (rg : Fin 11 → Fin T) : Pr P T Q A U :=
  .seq (canonicalDescriptorBaseProgram (rg ∘ canonicalDescriptorBaseSlot))
    (.seq (binarySuccessorProgram (rg 3) (rg 8) (rg 4) (rg 5) (rg 7))
      (.seq (bcopy (rg 3) (rg 9) (rg 4) (rg 5))
        (.seq (bshift (rg 9) (rg 4) (fun _ => bitSymbol true))
          (binaryScalarWidthProgram (rg ∘ canonicalDescriptorCounterSlot)))))

def canonicalDescriptorWidthsBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (L n w : ℕ) : Fin T → List (Fin (A + 4)) :=
  let W := Nat.clog 2 (n - w + 2)
  Function.update (Function.update (Function.update (Function.update R (rg 3) (binSyms L W))
    (rg 8) (binSyms L (W + 1))) (rg 9) (binSyms L (2 * W + 1)))
    (rg 10) (binSyms L (canonicalScalarWidth (2 * W + 1)))

theorem canonicalDescriptorWidths_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (L n w : ℕ)
    (hn : n < 2 ^ L) (hw : w ≤ n) (hcoord : 2 * Nat.clog 2 (n - w + 2) + 1 < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hborrowed : S.R (rg 1) = binSyms L w)
    (hblank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 7 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 8 * L * L + 90 * L + 105 ∧
      Exec body (canonicalDescriptorWidthsProgram rg) (mk v S) m
        (mk v' { S with R := canonicalDescriptorWidthsBank S.R rg L n w }) := by
  let W := Nat.clog 2 (n - w + 2)
  have hbaseBlank : ∀ j : Fin 8, j ≠ 0 → j ≠ 1 → j ≠ 7 →
      S.R ((rg ∘ canonicalDescriptorBaseSlot) j) = [] := by
    intro j hj0 hj1 hj7
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 11 => a.val) he))
    · exact fun he => hj1 (Fin.ext (congrArg (fun a : Fin 11 => a.val) he))
    · exact fun he => hj7 (Fin.ext (congrArg (fun a : Fin 11 => a.val) he))
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := canonicalDescriptorBase_exec body (rg ∘ canonicalDescriptorBaseSlot)
    (hrg.comp canonicalDescriptorBaseSlot_injective) L n w hn hw v S hdimension hborrowed hbaseBlank
  let C : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms L W) }
  obtain ⟨v₂, hu₂, he₂⟩ := binarySuccessor_exec body (rg 3) (rg 8) (rg 4) (rg 5) (rg 7)
    (by simp [List.nodup_cons, hrg.eq_iff]) L W v₁ C (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 8 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
  let D : Stacks T A := { C with R := Function.update C.R (rg 8) (binSyms L (W + 1)) }
  obtain ⟨v₃, hu₃, he₃⟩ := bcopy_exec (body := body) (a := rg 3) (c := rg 9) (t₁ := rg 4) (t₂ := rg 5)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₂ D
    (by simp [D, C, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
  have hd3 : D.R (rg 3) = binSyms L W := by simp [D, C, hrg.eq_iff]
  have hd9 : D.R (rg 9) = [] := by simp [D, C, hrg.eq_iff, hblank 9 (by decide) (by decide) (by decide)]
  rw [hd3, hd9, List.append_nil, length_binSyms] at he₃
  let E : Stacks T A := { D with R := Function.update D.R (rg 9) (binSyms L W) }
  obtain ⟨v₄, hu₄, he₄⟩ := bshift_exec (body := body) (s := rg 9) (t := rg 4) (hrg.ne (by decide))
    (fun _ => bitSymbol true) v₃ E
    (by simp [E, D, C, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide)])
  have he9 : E.R (rg 9) = binSyms L W := by simp [E]
  rw [he9, length_binSyms, binSyms_shift] at he₄
  let F : Stacks T A := { E with R := Function.update E.R (rg 9) (binSyms L (2 * W + 1)) }
  have keep (j : Fin 11) (hj3 : j ≠ 3) (hj8 : j ≠ 8) (hj9 : j ≠ 9) : F.R (rg j) = S.R (rg j) := by
    simp [F, E, D, C, hrg.eq_iff, hj3, hj8, hj9]
  have hcounterBlank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 →
      F.R ((rg ∘ canonicalDescriptorCounterSlot) j) = [] := by
    intro j hj0 hj5
    fin_cases j
    · exact (hj0 rfl).elim
    · exact (keep 2 (by decide) (by decide) (by decide)).trans (hblank 2 (by decide) (by decide) (by decide))
    · exact (keep 10 (by decide) (by decide) (by decide)).trans (hblank 10 (by decide) (by decide) (by decide))
    · exact (keep 4 (by decide) (by decide) (by decide)).trans (hblank 4 (by decide) (by decide) (by decide))
    · exact (keep 5 (by decide) (by decide) (by decide)).trans (hblank 5 (by decide) (by decide) (by decide))
    · exact (hj5 rfl).elim
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := binaryScalarWidth_exec body (rg ∘ canonicalDescriptorCounterSlot)
    (hrg.comp canonicalDescriptorCounterSlot_injective) L (2 * W + 1) hcoord v₄ F
    (by change F.R (rg 9) = _; simp [F]) hcounterBlank
  refine ⟨v₅, m₁ + ((10 * L + 11) + ((6 * L + 6) + ((4 * L + 8) + m₅))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast rfl ?_⟩
  · nlinarith only [hm₁, hm₅]
  · simp [F, E, D, C, canonicalDescriptorWidthsBank, canonicalDescriptorCounterSlot, canonicalScalarWidth, W]

/-- Canonical routing supplies every fit condition needed by width generation. -/
theorem canonicalDescriptorWidths_canonical_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (v : HS T Q A U) (S : Stacks T A) (hdimension : S.R (rg 0) = binSyms L n)
    (hborrowed : S.R (rg 1) = binSyms L (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)))
    (hblank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 7 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 8 * L * L + 90 * L + 105 ∧
      Exec body (canonicalDescriptorWidthsProgram rg) (mk v S) m
        (mk v' { S with R := (canonicalDescriptorWidthsBank S.R rg L n
          (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))) }) := by
  have hw : routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n) ≤ n := by
    have ht := routerGeometry_decomposition n (canonicalRouterStride n) (canonicalRouterGap n) hlarge
    omega
  have hgap : canonicalRouterGap n ≤ n := by
    unfold canonicalRouterStride at hlarge
    omega
  have hcoord := (canonicalDescriptorCoordinateWidth_le_gap n).trans hgap |>.trans_lt hn
  exact canonicalDescriptorWidths_exec body rg hrg L n _ hn hw hcoord v S hdimension hborrowed hblank

/-- The four generated words are the exact width operands used by every residue. -/
theorem canonicalDescriptorWidthsBank_router
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T) (hrg : Function.Injective rg)
    (L n : ℕ) (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n)) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let B := canonicalDescriptorWidthsBank R rg L n
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    B (rg 3) = binSyms L (canonicalStageWidths p).strideBits ∧
      B (rg 3) = binSyms L (canonicalStageWidths p).groupBits ∧
      B (rg 8) = binSyms L (canonicalStageWidths p).indexBits ∧
      B (rg 9) = binSyms L (canonicalStageWidths p).selectorBits ∧
      B (rg 10) = binSyms L (canonicalStageWidths p).widthBits := by
  dsimp only
  obtain ⟨hi,hg,hs,hsel,hw⟩ := canonicalStageWidths_router n hlarge r
  simp [canonicalDescriptorWidthsBank, hrg.eq_iff, hi, hg, hs, hsel, hw]

end IntegerMultBounds.MathlibTM2.Routing
