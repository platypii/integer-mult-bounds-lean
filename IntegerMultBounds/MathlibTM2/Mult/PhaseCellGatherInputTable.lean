module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedGatherReadiness
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableFormats

/-! A generated gather record survives initialization of a disjoint numerical
table in the caller prefix. Ports, program and mathematical parameters are fixed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
open ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K V s width radius L w n : ℕ} {bank : ComputedClassBank → Fin T}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
  {S : Stacks ((T+175)+tapeCount) (prime+K)}
namespace RestoringGatherData
noncomputable section

def loadInputTable (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S)
    (rg : TblR n → Fin ((T+175)+tapeCount)) (ports : List (Fin T))
    (hcover : ∀ r, ∃ output ∈ ports, classCallerRegister output = rg r)
    (input : Fin n → Fin ((T+175)+tapeCount)) (D : ℕ)
    (value : Fin ((T+175)+tapeCount) → ℕ)
    (hExpose : ∀ j output, output ∈ ports → g.exposeSrc j ≠ output)
    (hInput : ∀ output ∈ ports, g.input ≠ output)
    (hRoute : ∀ j output, output ∈ ports → g.routeSrc j ≠ output)
    (hOutput : ∀ output ∈ ports, bank (.control .source) ≠ output) :
    RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed
      (loadedInputTable rg input D value S) := by
  let F := loadedInputTable rg input D value S
  have hR (k) (hk : ∀ output ∈ ports, k ≠ classCallerRegister output) : F.R k = S.R k :=
    loadedInputTable_off _ input D value S k (by
      intro r
      obtain ⟨output,ho,heq⟩ := hcover r
      simpa only [heq] using hk output ho)
  have hc (k : Fin T) (hk : ∀ output ∈ ports, k ≠ output) : F.R (classCallerRegister k) = S.R (classCallerRegister k) :=
    hR _ (fun output ho => classCallerRegister_injective.ne (hk output ho))
  let seed := g.toRestoringGatherSeed.reframe F ports hR rfl
    (fun j _ => hExpose j) hInput (fun j _ => hRoute j) hOutput
  exact {
    toRestoringGatherSeed := seed
    hL := (hc _ (hExpose 3)).trans g.hL
    hRL := (hc _ (hRoute 3)).trans g.hRL}

theorem loadInputTable_program {P U : Type}
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S)
    (rg : TblR n → Fin ((T+175)+tapeCount)) (ports : List (Fin T))
    (hcover : ∀ r, ∃ output ∈ ports, classCallerRegister output = rg r)
    (input : Fin n → Fin ((T+175)+tapeCount)) (D : ℕ)
    (value : Fin ((T+175)+tapeCount) → ℕ)
    (hExpose : ∀ j output, output ∈ ports → g.exposeSrc j ≠ output)
    (hInput : ∀ output ∈ ports, g.input ≠ output)
    (hRoute : ∀ j output, output ∈ ports → g.routeSrc j ≠ output)
    (hOutput : ∀ output ∈ ports, bank (.control .source) ≠ output) :
    (g.loadInputTable rg ports hcover input D value hExpose hInput hRoute hOutput).program
      (P := P) (U := U) = g.program := rfl

end
end RestoringGatherData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
