import IntegerMultBounds.Machine.ArbitraryWidthHighCommonSelector
import IntegerMultBounds.Machine.ArbitraryWidthHighBranchComposition
import IntegerMultBounds.Machine.ArbitraryWidthHighCommonHighBody
import IntegerMultBounds.Machine.ArbitraryWidthHighFramedFallback

/-! One actual runtime selector chooses the proved high body or elementary
fallback, both on the same bank with identical exact transpose endpoints. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighCommonDispatch
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighPrepare (highDepth)
open ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

abbrev bank := @ArbitraryWidthHighFramedFallback.bank

def liftSlot (i : Fin ((t+16)+19)) := Fin.castAdd ArbitraryWidthElementary.tapeCount
  (ArbitraryWidthHighFramedFallback.frameSlot i)
def rho := liftSlot (ArbitraryWidthHighCommonSelector.rho (t := t))
def width := liftSlot (ArbitraryWidthHighCommonSelector.width (t := t))
def flag := liftSlot (ArbitraryWidthHighCommonSelector.flag (t := t))

theorem rho_ne_width : rho (t := t) ≠ width := by
  intro he
  apply ArbitraryWidthHighCommonSelector.rho_ne_width (t := t)
  have hv := congrArg Fin.val he
  exact Fin.ext hv
theorem rho_ne_flag : rho (t := t) ≠ flag := by
  intro he
  apply ArbitraryWidthHighCommonSelector.rho_ne_flag (t := t)
  have hv := congrArg Fin.val he
  exact Fin.ext hv
theorem width_ne_flag : width (t := t) ≠ flag := by
  intro he
  apply ArbitraryWidthHighCommonSelector.width_ne_flag (t := t)
  have hv := congrArg Fin.val he
  exact Fin.ext hv

def highProgram (focus : Fin t) :=
  extend (ArbitraryWidthHighCommonHighBody.program focus) ArbitraryWidthElementary.tapeCount

def program (focus : Fin t) := ArbitraryWidthHighBranchComposition.program
  rho width flag rho_ne_width rho_ne_flag width_ne_flag (highProgram focus)
  (ArbitraryWidthHighFramedFallback.program focus)

abbrev guard (d : Descriptor) : Prop := 1 ≤ highDepth prime d.width ∧ highDepth prime d.width < d.width

def cost (d : Descriptor) (hs : Fin 6 → List Bool) :=
  ArbitraryWidthHighBranch.cost (ArbitraryWidthHighPrepare.words prime d.width 2) (hs 3)+1+
    if guard d then ArbitraryWidthHighCommonHighBody.cost d hs else ArbitraryWidthHighCommonFallbackBody.cost d

theorem lifted_cells (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool)
    (i : Fin ((t+16)+19)) :
    (bank caller d hs).head (liftSlot i) = (ArbitraryWidthHighCommonPrepare.output caller d hs prime).head i ∧
    (bank caller d hs).tape (liftSlot i) = (ArbitraryWidthHighCommonPrepare.output caller d hs prime).tape i := by
  simp only [bank,ArbitraryWidthHighFramedFallback.bank,liftSlot,Tapes.append,Fin.addCases_left]
  exact ArbitraryWidthHighFramedFallback.frame_cells _ i

theorem guard_values (d : Descriptor) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers d hs) :
    (1 ≤ Counter.value (ArbitraryWidthHighPrepare.words prime d.width 2) ∧
      Counter.value (ArbitraryWidthHighPrepare.words prime d.width 2) < Counter.value (hs 3)) ↔ guard d := by
  have hr : Counter.value (ArbitraryWidthHighPrepare.words prime d.width 2) = highDepth prime d.width :=
    ArbitraryWidthHighPrepare.words_value prime d.width 2
  have he : Counter.value (hs 3) = d.width := hv.1 3
  rw [hr,he]

/-- The runtime flag is initially blank, generated and erased by the actual
selector. All branch and metadata contracts follow from original headers;
there are no supplied execution callbacks or precomputed branch outcomes. -/
theorem runs (caller : Tapes t prime) (focus : Fin t) (d : Descriptor) (hs : Fin 6 → List Bool)
    (hp : d.Positive) (hv : RecursiveDimensionBank.Headers d hs)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus) (fun w => w = bank caller d hs)
      (fun w => w = bank (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) d hs) (cost d hs) := by
  let out := bank (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0) d hs
  have hrc := lifted_cells caller d hs ArbitraryWidthHighCommonSelector.rho
  have hec := lifted_cells caller d hs ArbitraryWidthHighCommonSelector.width
  have hfc := lifted_cells caller d hs ArbitraryWidthHighCommonSelector.flag
  have hr := ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 2
  have he := ArbitraryWidthHighCommonPrepare.original_view caller d hs prime 3
  have hfl : (ArbitraryWidthHighCommonPrepare.output caller d hs prime).head
      ArbitraryWidthHighCommonSelector.flag = 0 ∧
      (ArbitraryWidthHighCommonPrepare.output caller d hs prime).tape
      ArbitraryWidthHighCommonSelector.flag = (fun _ => blank) := by
    simpa only [ArbitraryWidthHighCommonSelector.flag,ArbitraryWidthHighCommonPrepare.output,
      Tapes.append,Fin.addCases_right] using
      ArbitraryWidthHighPrepareShared.private_output_width (a := prime) prime d.width
  have h := ArbitraryWidthHighBranchComposition.runs rho width flag rho_ne_width rho_ne_flag width_ne_flag
    (highProgram focus) (ArbitraryWidthHighFramedFallback.program focus)
    (bank caller d hs) out out (ArbitraryWidthHighCommonHighBody.cost d hs)
    (ArbitraryWidthHighCommonFallbackBody.cost d)
    (ArbitraryWidthHighPrepare.words prime d.width 2) (hs 3)
    (ArbitraryWidthHighPrepare.words_canonical prime d.width 2)
    (hrc.2.trans (hr.2.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)) (hrc.1.trans hr.1)
    (hec.2.trans (he.2.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)) (hec.1.trans he.1)
    (hfc.2.trans hfl.2) (hfc.1.trans hfl.1)
    (fun hg => hoare_extend_eq
      (ArbitraryWidthHighCommonHighBody.runs caller focus d hs hp hv ((guard_values d hs hv).mp hg) x hf hh)
      (FixedHeaderBankCopy.empty ArbitraryWidthElementary.tapeCount))
    (fun _ => ArbitraryWidthHighFramedFallback.realizes_hoare caller focus d hs hp hv x hf hh)
  apply h.consequence (fun _ hh => hh) _ _
  · intro w hw
    simpa only [ite_self] using hw
  · simp only [cost,guard_values d hs hv,le_refl]

end
end IntegerMultBounds.Machine.ArbitraryWidthHighCommonDispatch
