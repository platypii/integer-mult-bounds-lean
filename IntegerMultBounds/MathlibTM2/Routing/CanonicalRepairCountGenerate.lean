module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairZeroGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairRecordCountGenerate

/-! Compose shared repair zeros and exact record-count generation from original
dimension/residue, retaining the caller's payload-width word at slot 120. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def canonicalRepairCountCore : Fin 124 → Fin 125 := Fin.castLE (by decide)
theorem canonicalRepairCountCore_injective : Function.Injective canonicalRepairCountCore := by decide +kernel
def canonicalRepairCountSlot : Fin 6 → Fin 125 := ![0,124,123,40,41,42]
theorem canonicalRepairCountSlot_injective : Function.Injective canonicalRepairCountSlot := by decide +kernel

def canonicalRepairCountGenerateProgram (rg : Fin 125 → Fin T) : Pr P T Q A U :=
  .seq (canonicalRepairZeroGenerateProgram (rg ∘ canonicalRepairCountCore))
    (repairRecordCountGenerateProgram (rg ∘ canonicalRepairCountSlot))

def canonicalRepairCountGeneratedBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 125 → Fin T) (L n r : ℕ) :=
  Function.update (canonicalRepairZeroGeneratedBank R (rg ∘ canonicalRepairCountCore) L n r)
    (rg 124) (binSyms (n+1) (2 ^ n))

theorem canonicalRepairCountGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 125 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 125, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalClassifierGeneratePrice L W p + 10 * W + 13 +
        (4 * W * (p.wc+p.wy) + 22 * W + 8 * (p.wc+p.wy) + 24) +
        (L * (4 * n + 11) + 8 * n + 13) ∧
      Exec body (canonicalRepairCountGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalRepairCountGeneratedBank S.R rg L n r.val }) := by
  dsimp only
  let core := rg ∘ canonicalRepairCountCore
  let header := core ∘ canonicalRepairZeroCore
  have hc : Function.Injective core := hrg.comp canonicalRepairCountCore_injective
  have hh : Function.Injective header := hc.comp canonicalRepairZeroCore_injective
  have cb : ∀ i : Fin 124, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → S.R (core i) = [] := by
    intro i h0 h9 h18 h120
    exact hblank _ (fun h => h0 (Fin.ext (congrArg (fun x : Fin 125 => x.val) h)))
      (fun h => h9 (Fin.ext (congrArg (fun x : Fin 125 => x.val) h)))
      (fun h => h18 (Fin.ext (congrArg (fun x : Fin 125 => x.val) h)))
      (fun h => h120 (Fin.ext (congrArg (fun x : Fin 125 => x.val) h)))
  have hb : ∀ i : Fin 120, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (header i) = [] := by
    intro i h0 h9 h18
    apply hblank
    · intro h; exact h0 (Fin.ext (congrArg (fun x : Fin 125 => x.val) h))
    · intro h; exact h9 (Fin.ext (congrArg (fun x : Fin 125 => x.val) h))
    · intro h; exact h18 (Fin.ext (congrArg (fun x : Fin 125 => x.val) h))
    · intro h; have hv := congrArg (fun x : Fin 125 => x.val) h
      change i.val = 120 at hv
      have := i.isLt
      omega
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalRepairZeroGenerate_exec body core hc L n hn hlarge hdivisor
    r v S hdimension hresidue cb
  let C : Stacks T A := { S with R := canonicalRepairZeroGeneratedBank S.R core L n r.val }
  have keep (i : Fin 125) (h121 : i ≠ 121) (h122 : i ≠ 122) : C.R (rg i) =
      canonicalHeaderScalarGeneratedBank S.R header L n r.val (rg i) := by
    simp [C,canonicalRepairZeroGeneratedBank,repairZeroBank,canonicalRepairZeroSlot,
      core,header,canonicalRepairCountCore,hrg.eq_iff,h121,h122]
  have source : C.R (rg 0) = binSyms L n :=
    (keep 0 (by decide) (by decide)).trans
      ((canonicalHeaderScalarGeneratedBank_dimension S.R header hh L n r.val).trans hdimension)
  have scratch (i : Fin 118) (hi : i ∈ ([40,41,42] : List (Fin 118))) :
      C.R (header (canonicalHeaderScalarCore i)) = [] := by
    have hlo : i.val < 118 := i.isLt
    have h121 : (⟨i.val,by have := i.isLt; omega⟩ : Fin 125) ≠ 121 := by
      intro h; have hv := congrArg Fin.val h; simp only at hv; omega
    have h122 : (⟨i.val,by have := i.isLt; omega⟩ : Fin 125) ≠ 122 := by
      intro h; have hv := congrArg Fin.val h; simp only at hv; omega
    rw [show C.R (header (canonicalHeaderScalarCore i)) =
        canonicalHeaderScalarGeneratedBank S.R header L n r.val (header (canonicalHeaderScalarCore i)) from
        keep ⟨i.val,by omega⟩ h121 h122]
    rw [canonicalHeaderScalarGeneratedBank_low S.R header hh L n r.val _ i.isLt]
    apply canonicalHeaderBase_blank S.R header hh L n r.val hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp
  have newBlank (i : Fin 125) (hi : 123 ≤ i.val) : C.R (rg i) = [] := by
    rw [keep i (by intro h; subst i; norm_num at hi) (by intro h; subst i; norm_num at hi)]
    rw [canonicalHeaderScalarGeneratedBank_outside S.R header L n r.val _ (by
      intro j he
      have hv := congrArg (fun x : Fin 125 => x.val) (hrg he)
      change j.val = i.val at hv
      have := j.isLt
      omega)]
    apply hblank <;> intro h <;> subst i <;> norm_num at hi
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := repairRecordCountGenerate_exec body (rg ∘ canonicalRepairCountSlot)
    (hrg.comp canonicalRepairCountSlot_injective) L n hn v₁ C source (by
      intro i hi
      fin_cases i
      · exact (hi rfl).elim
      · exact newBlank 124 (by decide)
      · exact newBlank 123 (by decide)
      · exact scratch 40 (by simp)
      · exact scratch 41 (by simp)
      · exact scratch 42 (by simp))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end
end IntegerMultBounds.MathlibTM2.Routing
