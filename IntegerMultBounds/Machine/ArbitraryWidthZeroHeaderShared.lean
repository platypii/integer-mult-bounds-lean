import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! A physically written canonical zero clock, with paid erasure. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthZeroHeaderShared
noncomputable section
variable {a t : ℕ}

def empty : Tapes 1 a := FiniteReturnStack.bank (fun _ => blank) 0
def header : Tapes 1 a := FiniteReturnStack.bank (BinaryDescriptorStack.descriptor []) 1

theorem bits_zero : RecursiveChildQuotientsConstant.bits 0 = [] := rfl

theorem zero_value : Counter.value ([] : List Bool) = 0 := rfl

theorem zero_canonical : GrowingCounterData.Canonical [] := Or.inl rfl

theorem header_cells : (header (a := a)).head 0 = 1 ∧
    (header (a := a)).tape 0 = BinaryDescriptorStack.descriptor [] := ⟨rfl,rfl⟩

theorem encoded_zero : BinaryDescriptorStack.descriptor (a := a) [] =
    RadixZeroFill.encodedBinary [] := BinaryDescriptorStackRoundtrip.descriptor_encoded []

def program := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 0)
  (finAddFlip : Fin (1+t) ≃ Fin (t+1))
def cleanup := Placement.placed (BinaryDescriptorCleanupList.oneProgram (a := a) (0 : Fin 1))
  (finAddFlip : Fin (1+t) ≃ Fin (t+1))

private theorem right_hoare {states budget : ℕ} {M : Program 1 states a}
    {v w : Tapes 1 a} (h : HoareTime M (fun z => z = v) (fun z => z = w) budget)
    (caller : Tapes t a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (1+t) ≃ Fin (t+1)))
      (fun z => z = caller.append v) (fun z => z = caller.append w) budget := by
  have ha : Placement.active (finAddFlip : Fin (1+t) ≃ Fin (t+1)) (caller.append v) = v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hw : Placement.active (finAddFlip : Fin (1+t) ≃ Fin (t+1)) (caller.append w) = w := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hf : Placement.extra (finAddFlip : Fin (1+t) ≃ Fin (t+1)) (caller.append v) =
      Placement.extra (finAddFlip : Fin (1+t) ≃ Fin (t+1)) (caller.append w) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp [Tapes.append]
  have hp := Placement.hoare_at h _ (caller.append v) ha
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,hs,rfl⟩
  rw [hs,Placement.replace,hf]
  exact (congrArg (fun z => Placement.combine
    (finAddFlip : Fin (1+t) ≃ Fin (t+1)) z
    (Placement.extra finAddFlip (caller.append w))) hw.symm).trans (Placement.view _ _)

theorem constructs (caller : Tapes t a) :
    HoareTime (program (a := a) (t := t))
      (fun w => w = caller.append empty) (fun w => w = caller.append header) 6 := by
  have h := RecursiveChildQuotientsConstant.initialize_hoare (a := a) 0
  exact right_hoare h caller

theorem cleans (caller : Tapes t a) :
    HoareTime (cleanup (a := a) (t := t))
      (fun w => w = caller.append header) (fun w => w = caller.append empty) 4 := by
  have h := BinaryDescriptorCleanupList.one_hoare (0 : Fin 1) (header (a := a)) [] rfl rfl
  have he : SharedPlacementAlphabet.setTape (header (a := a)) 0 (fun _ => blank) 0 = empty := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact right_hoare h caller

theorem constructs_linear (caller : Tapes t a) (V : ℕ) (hV : 0 < V) :
    HoareTime (program (a := a) (t := t))
      (fun w => w = caller.append empty) (fun w => w = caller.append header) (6*V) :=
  (constructs caller).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem cleans_linear (caller : Tapes t a) (V : ℕ) (hV : 0 < V) :
    HoareTime (cleanup (a := a) (t := t))
      (fun w => w = caller.append header) (fun w => w = caller.append empty) (4*V) :=
  (cleans caller).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ArbitraryWidthZeroHeaderShared
