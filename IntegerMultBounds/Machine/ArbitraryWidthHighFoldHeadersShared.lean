import IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeadersCleanup
import IntegerMultBounds.Machine.FixedHeaderSparseBankCopy

/-! Physically copy the caller's sole original six headers, compute the folded
root header bank, then erase all generated and copied private descriptors. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeadersShared
noncomputable section
variable {a t : ℕ}
open RecursiveInterchangeLayout (Descriptor)

def destination : Fin 6 → Fin 16 := Fin.castAdd 10
private theorem destination_injective : Function.Injective destination := Fin.castAdd_injective _ _
def copyProgram (focus : Fin 6 → Fin t) := FixedHeaderSparseBankCopy.program
  (a := a) (by omega : 0 < t+6) focus destination destination_injective (by decide)
def foldedProgram := Placement.placed (ArbitraryWidthHighFoldHeaders.program (a := a))
  (finAddFlip : Fin (16+t) ≃ Fin (t+16))
def program (focus : Fin 6 → Fin t) := seq (copyProgram (a := a) focus) foldedProgram

def eraseFolded := Placement.placed (ArbitraryWidthHighFoldHeadersCleanup.program (a := a))
  (finAddFlip : Fin (16+t) ≃ Fin (t+16))
def eraseCopies := FixedHeaderSparseBankCopy.cleanup (a := a)
  (by omega : 0 < t+6) destination destination_injective (by decide)
def cleanup := seq (eraseFolded (a := a) (t := t)) eraseCopies

theorem input_bank (hs : Fin 6 → List Bool) :
    ArbitraryWidthHighFoldHeaders.input (a := a) hs =
      FixedHeaderSparseBankCopy.headerBank destination hs := by
  apply FixedHeaderSparseBankCopy.headerBank_eq destination destination_injective
  · intro i; fin_cases i <;> exact ⟨rfl,rfl⟩
  · intro j hj
    have hhigh : 6 ≤ j.val := by
      by_contra h
      have hj' : j.val < 6 := by omega
      exact hj ⟨j.val,hj'⟩ (Fin.ext rfl)
    fin_cases j <;> first | exact ⟨rfl,rfl⟩ | norm_num at hhigh

private theorem right_hoare {states budget : ℕ} {M : Program 16 states a}
    {v w : Tapes 16 a} (h : HoareTime M (fun z => z = v) (fun z => z = w) budget)
    (caller : Tapes t a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (16+t) ≃ Fin (t+16)))
      (fun z => z = caller.append v) (fun z => z = caller.append w) budget := by
  have ha : Placement.active (finAddFlip : Fin (16+t) ≃ Fin (t+16)) (caller.append v) = v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hw : Placement.active (finAddFlip : Fin (16+t) ≃ Fin (t+16)) (caller.append w) = w := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hf : Placement.extra (finAddFlip : Fin (16+t) ≃ Fin (t+16)) (caller.append v) =
      Placement.extra (finAddFlip : Fin (16+t) ≃ Fin (t+16)) (caller.append w) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hp := Placement.hoare_at h _ (caller.append v) ha
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,hs,rfl⟩
  rw [hs,Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine
    (finAddFlip : Fin (16+t) ≃ Fin (t+16)) z
    (Placement.extra finAddFlip (caller.append w))) hw.symm).trans (Placement.view _ _)



theorem constructs (focus : Fin 6 → Fin t) (caller : Tapes t a)
    (d : Descriptor) (hs : Fin 6 → List Bool) (V : ℕ) (hV : 0 < V)
    (hp : d.Positive) (hh : RecursiveDimensionBank.Headers d hs)
    (hprefix : d.beforeRows*d.rows*d.beforeH ≤ V)
    (hv : ∀ i, RecursiveDimensionBank.values d i ≤ V)
    (ht : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i))
    (hhead : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program focus)
      (fun z => z = caller.append (FixedHeaderBankCopy.empty 16))
      (fun z => z = caller.append (ArbitraryWidthHighFoldHeaders.output d hs)) (285*V) := by
  have hcopy := FixedHeaderSparseBankCopy.constructs_linear (a := a)
    (by omega : 0 < t+6) focus destination destination_injective (by decide) caller hs ht hhead
    V hV hh.2 (by intro i; rw [hh.1]; exact hv i)
  rw [← input_bank] at hcopy
  have hd := right_hoare (ArbitraryWidthHighFoldHeaders.constructs_linear (a := a)
    d hs V hp hh hprefix hv) caller
  exact (hcopy.seq hd).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem cleans (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool)
    (V : ℕ) (hV : 0 < V) (hp : d.Positive) (hh : RecursiveDimensionBank.Headers d hs)
    (hprefix : d.beforeRows*d.rows*d.beforeH ≤ V)
    (hv : ∀ i, RecursiveDimensionBank.values d i ≤ V) :
    HoareTime (cleanup (a := a) (t := t))
      (fun z => z = caller.append (ArbitraryWidthHighFoldHeaders.output d hs))
      (fun z => z = caller.append (FixedHeaderBankCopy.empty 16)) (109*V) := by
  have hd := right_hoare (ArbitraryWidthHighFoldHeadersCleanup.cleans_linear (a := a)
    d hs V hp hh hprefix hv) caller
  have hcopy := FixedHeaderSparseBankCopy.cleans_linear (a := a)
    (by omega : 0 < t+6) destination destination_injective (by decide) caller hs
    V hV hh.2 (by intro i; rw [hh.1]; exact hv i)
  rw [← input_bank] at hcopy
  exact (hd.seq hcopy).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem headers (d : Descriptor) (hs : Fin 6 → List Bool)
    (hh : RecursiveDimensionBank.Headers d hs) :
    RecursiveDimensionBank.Headers (ArbitraryWidthHighFoldSemantics.folded d)
      (ArbitraryWidthHighFoldHeaders.words d hs) :=
  ArbitraryWidthHighFoldHeaders.headers d hs hh

theorem source_view (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (i : Fin 6) :
    (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)).head
      (Fin.natAdd t (Fin.castAdd 10 i)) = 1 ∧
    (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)).tape
      (Fin.natAdd t (Fin.castAdd 10 i)) = RadixZeroFill.encodedBinary (hs i) := by
  fin_cases i <;> simp [Tapes.append,ArbitraryWidthHighFoldHeaders.output,
    ArbitraryWidthHighFoldHeaders.state,ArbitraryWidthHighFoldHeaders.bank]

theorem target_view (caller : Tapes t a) (d : Descriptor) (hs : Fin 6 → List Bool) (i : Fin 6) :
    (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)).head
      (Fin.natAdd t (Fin.natAdd 6 (Fin.castAdd 4 i))) = 1 ∧
    (caller.append (ArbitraryWidthHighFoldHeaders.output d hs)).tape
      (Fin.natAdd t (Fin.natAdd 6 (Fin.castAdd 4 i))) =
        RadixZeroFill.encodedBinary (ArbitraryWidthHighFoldHeaders.words d hs i) := by
  simpa [Tapes.append] using ArbitraryWidthHighFoldHeaders.output_headers (a := a) d hs i

end
end IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeadersShared
