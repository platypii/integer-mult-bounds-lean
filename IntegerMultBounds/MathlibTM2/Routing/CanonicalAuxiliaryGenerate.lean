module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalScalarInputGenerate
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalAuxiliarySources
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalProfileFits
public import IntegerMultBounds.MathlibTM2.Routing.RouterAuxiliaryGenerate

/-! Complete the two auxiliary operand banks from original dimension/residue.
Shared setup supplies all count, width and target operands and their fit proofs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def canonicalAuxiliaryCore : Fin 46 → Fin 49 := Fin.castLE (by decide)
def canonicalAuxiliarySlot : Fin 12 → Fin 49 := ![11,25,44,46,47,48,3,4,5,6,7,8]
theorem canonicalAuxiliaryCore_injective : Function.Injective canonicalAuxiliaryCore := by decide +kernel
theorem canonicalAuxiliarySlot_injective : Function.Injective canonicalAuxiliarySlot := by decide +kernel

def canonicalAuxiliaryGenerateProgram (rg : Fin 49 → Fin T) : Pr P T Q A U :=
  .seq (canonicalScalarInputProgram (rg ∘ canonicalAuxiliaryCore))
    (routerAuxiliaryGenerateProgram (rg ∘ canonicalAuxiliarySlot))

def canonicalAuxiliaryBank (R : Fin T → List (Fin (A+4))) (rg : Fin 49 → Fin T) (L n r : ℕ) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  routerAuxiliaryBank (canonicalDescriptorScalarInputBank R (rg ∘ canonicalAuxiliaryCore) L n r)
    (rg ∘ canonicalAuxiliarySlot) (canonicalStageWidths p).indexBits p.n p.wy

theorem canonicalAuxiliaryGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 49 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2^L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 49, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let I := (canonicalStageWidths p).indexBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 96*L*L+592*L+560 + (2*L*(4*I+11)+22*L+26*I+55) ∧
      Exec body (canonicalAuxiliaryGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalAuxiliaryBank S.R rg L n r.val }) := by
  dsimp only
  let core := rg ∘ canonicalAuxiliaryCore
  have hc : Function.Injective core := hrg.comp canonicalAuxiliaryCore_injective
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalScalarInput_exec body core hc L n hn hlarge hdivisor r v S
    hdimension hresidue (by
      intro i h0 h9 h18
      exact hblank _ (fun h => h0 (Fin.ext (congrArg (fun x : Fin 49 => x.val) h)))
        (fun h => h9 (Fin.ext (congrArg (fun x : Fin 49 => x.val) h)))
        (fun h => h18 (Fin.ext (congrArg (fun x : Fin 49 => x.val) h))))
  let C : Stacks T A := { S with R := canonicalDescriptorScalarInputBank S.R core L n r.val }
  obtain ⟨count,index,target⟩ := canonicalAuxiliarySources S.R core hc L n hlarge r hresidue
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have fits := canonicalProfileFits L n hn hlarge r
  have hi : (canonicalStageWidths p).indexBits < 2^L := by
    have h := fits.2.2.2.2.1
    dsimp only [p]
    omega
  have hwy : p.wy < 2^L := by
    have h := canonicalDescriptorScalarRaw_fit L n hn hlarge r 3
    simpa [repairDescriptorScalarPalette,descriptorScalarInputIndex,p] using h
  have off : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → i ≠ 2 →
      canonicalAuxiliarySlot i ∉ ([0,9,18,1,2,11,14,16,17,19,21,25,26,27,44] : List (Fin 49)) := by
    decide +kernel
  have blank : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → i ≠ 2 → C.R ((rg ∘ canonicalAuxiliarySlot) i) = [] := by
    intro i h0 h1 h2
    have h := off i h0 h1 h2
    have keep : C.R (rg (canonicalAuxiliarySlot i)) = S.R (rg (canonicalAuxiliarySlot i)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      simp_all [C,canonicalDescriptorScalarInputBank,canonicalProfileSetupBank,canonicalDescriptorWidthsBank,
        canonicalResidueGeometryBank,canonicalGeometryBank,routerReservoirGeometryBank,routerGeometryBank,
        canonicalProfileWidthSlot,canonicalProfileGeometrySlot,canonicalResidueCommonSlot,
        routerReservoirCommonSlot,canonicalDescriptorGeometrySlot,core,canonicalAuxiliaryCore,
        Function.comp_def,hrg.eq_iff]
    change C.R (rg (canonicalAuxiliarySlot i)) = []
    rw [keep]
    apply hblank <;> intro he <;> exact h (by simp [he])
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := routerAuxiliaryGenerate_exec body (rg ∘ canonicalAuxiliarySlot)
    (hrg.comp canonicalAuxiliarySlot_injective) L L L (canonicalStageWidths p).indexBits p.n p.wy
    hi fits.2.2.2.1 hwy v₁ C count index target blank
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end IntegerMultBounds.MathlibTM2.Routing
