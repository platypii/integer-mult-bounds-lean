module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalHeaderOperandReady
public import IntegerMultBounds.MathlibTM2.Routing.RepairZeroGenerate

/-! Generate the shared repair zero fields from original dimension/residue.
Slot 120 is reserved for the caller's payload-width word and remains untouched. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalRepairZeroCore : Fin 120 → Fin 124 := Fin.castLE (by decide)
theorem canonicalRepairZeroCore_injective : Function.Injective canonicalRepairZeroCore := by decide +kernel
def canonicalRepairZeroSlot : Fin 8 → Fin 124 := ![34,33,121,122,123,40,41,42]
theorem canonicalRepairZeroSlot_injective : Function.Injective canonicalRepairZeroSlot := by decide +kernel

def canonicalRepairZeroGenerateProgram (rg : Fin 124 → Fin T) : Pr P T Q A U :=
  .seq (canonicalHeaderScalarGenerateProgram (rg ∘ canonicalRepairZeroCore))
    (repairZeroGenerateProgram (rg ∘ canonicalRepairZeroSlot))

def canonicalRepairZeroGeneratedBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 124 → Fin T) (L n r : ℕ) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  repairZeroBank (canonicalHeaderScalarGeneratedBank R (rg ∘ canonicalRepairZeroCore) L n r)
    (rg ∘ canonicalRepairZeroSlot) p

theorem canonicalRepairZeroGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 124 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 124, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalClassifierGeneratePrice L W p + 10 * W + 13 +
        (4 * W * (p.wc+p.wy) + 22 * W + 8 * (p.wc+p.wy) + 24) ∧
      Exec body (canonicalRepairZeroGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalRepairZeroGeneratedBank S.R rg L n r.val }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalRepairZeroCore
  have hc : Function.Injective core := hrg.comp canonicalRepairZeroCore_injective
  have cb : ∀ i : Fin 120, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (core i) = [] := by
    intro i h0 h9 h18
    apply hblank
    · intro h; exact h0 (Fin.ext (congrArg (fun x : Fin 124 => x.val) h))
    · intro h; exact h9 (Fin.ext (congrArg (fun x : Fin 124 => x.val) h))
    · intro h; exact h18 (Fin.ext (congrArg (fun x : Fin 124 => x.val) h))
    · intro h
      have hv := congrArg (fun x : Fin 124 => x.val) h
      change i.val = 120 at hv
      have := i.isLt
      omega
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalHeaderScalarGenerate_exec body core hc L n hn hlarge
    hdivisor r v S hdimension hresidue cb
  let C : Stacks T A := { S with R := canonicalHeaderScalarGeneratedBank S.R core L n r.val }
  have scratch (i : Fin 118) (hi : i ∈ ([40,41,42] : List (Fin 118))) :
      C.R (core (canonicalHeaderScalarCore i)) = [] := by
    change canonicalHeaderScalarGeneratedBank S.R core L n r.val (core (canonicalHeaderScalarCore i)) = []
    rw [canonicalHeaderScalarGeneratedBank_low S.R core hc L n r.val _ i.isLt]
    apply canonicalHeaderBase_blank S.R core hc L n r.val cb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp
  have newBlank (i : Fin 124) (hi : 121 ≤ i.val) : C.R (rg i) = [] := by
    rw [show C.R (rg i) = S.R (rg i) from canonicalHeaderScalarGeneratedBank_outside S.R core L n r.val _ (by
      intro j he
      have hv := congrArg (fun x : Fin 124 => x.val) (hrg he)
      change j.val = i.val at hv
      have := j.isLt
      omega)]
    apply hblank <;> intro h <;> subst i <;> norm_num at hi
  have palette (j : Fin 11) := canonicalHeaderScalarGeneratedBank_palette S.R core hc L n r.val j
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := repairZeroGenerate_exec body (rg ∘ canonicalRepairZeroSlot)
    (hrg.comp canonicalRepairZeroSlot_injective) W p (repairDescriptorScalarPalette_fit p r.isLt 6)
    (repairDescriptorScalarPalette_fit p r.isLt 5) v₁ C (palette 6) (palette 5) (by
      intro i h0 h1
      fin_cases i
      · exact (h0 rfl).elim
      · exact (h1 rfl).elim
      · exact newBlank 121 (by decide)
      · exact newBlank 122 (by decide)
      · exact newBlank 123 (by decide)
      · exact scratch 40 (by simp)
      · exact scratch 41 (by simp)
      · exact scratch 42 (by simp))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
