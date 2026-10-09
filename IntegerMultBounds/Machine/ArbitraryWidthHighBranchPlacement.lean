import IntegerMultBounds.Machine.ArbitraryWidthHighBranch
import IntegerMultBounds.Machine.InjectivePlacement

/-! Place the physical manuscript guard at any three distinct shared tape
slots. Its concrete contract accepts only the original marked rho/e words
and one blank flag; every complete tape and every head is restored. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighBranchPlacement
noncomputable section
variable {t a : ℕ}

def slots (rho width flag : Fin t) : Fin 3 → Fin t := ![rho,width,flag]

theorem slots_injective (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag) :
    Function.Injective (slots rho width flag) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [slots]

def placement (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag) : Fin (3+(t-3)) ≃ Fin t :=
  InjectivePlacement.placement (slots rho width flag) (slots_injective rho width flag hrw hrf hwf)
    (by have h := Fintype.card_le_of_injective _ (slots_injective rho width flag hrw hrf hwf)
        simp only [Fintype.card_fin] at h
        omega)

@[simp] theorem placement_active (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag) (i : Fin 3) :
    placement rho width flag hrw hrf hwf (Fin.castAdd (t-3) i) = slots rho width flag i :=
  InjectivePlacement.active_slot _ _ _ _

def program (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag) :=
  Placement.placed (ArbitraryWidthHighBranch.program (a := a)) (placement rho width flag hrw hrf hwf)

theorem active_input (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag)
    (v : Tapes t a) (rs es : List Bool)
    (hrr : v.tape rho = BinaryDescriptorStack.descriptor rs) (hrh : v.head rho = 1)
    (her : v.tape width = BinaryDescriptorStack.descriptor es) (heh : v.head width = 1)
    (hfr : v.tape flag = fun _ => blank) (hfh : v.head flag = 0) :
    Placement.active (placement rho width flag hrw hrf hwf) v = ArbitraryWidthHighBranch.input rs es := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp only [placement_active]
  · exact hrh
  · exact heh
  · exact hfh
  · exact hrr
  · exact her
  · exact hfr

/-- Literal stateful execution of the runtime guard with no supplied flag,
comparison outcome, or decision callback. -/
theorem selects (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag)
    (v : Tapes t a) (rs es : List Bool) (cr : GrowingCounterData.Canonical rs)
    (hrr : v.tape rho = BinaryDescriptorStack.descriptor rs) (hrh : v.head rho = 1)
    (her : v.tape width = BinaryDescriptorStack.descriptor es) (heh : v.head width = 1)
    (hfr : v.tape flag = fun _ => blank) (hfh : v.head flag = 0) :
    ∃ n ≤ ArbitraryWidthHighBranch.cost rs es, ∃ c,
      run (program rho width flag hrw hrf hwf) n (v.start (program rho width flag hrw hrf hwf)) = some c ∧
      step (program rho width flag hrw hrf hwf) c = none ∧ c.tapes = v ∧
      c.state = FiniteFlow.embed ArbitraryWidthHighBranch.states 1
        (ArbitraryWidthHighBranch.selected (Counter.value rs) (Counter.value es)) :=
  ArbitraryWidthHighBranch.selects_at (placement rho width flag hrw hrf hwf) v rs es cr
    (active_input rho width flag hrw hrf hwf v rs es hrr hrh her heh hfr hfh)

/-- The selector is a reusable whole-bank operation: scratch cleanup is
included, not deferred to whichever branch the finite control subsequently enters. -/
theorem preserves (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag)
    (v : Tapes t a) (rs es : List Bool) (cr : GrowingCounterData.Canonical rs)
    (hrr : v.tape rho = BinaryDescriptorStack.descriptor rs) (hrh : v.head rho = 1)
    (her : v.tape width = BinaryDescriptorStack.descriptor es) (heh : v.head width = 1)
    (hfr : v.tape flag = fun _ => blank) (hfh : v.head flag = 0) :
    HoareTime (program rho width flag hrw hrf hwf) (fun w => w = v) (fun w => w = v)
      (ArbitraryWidthHighBranch.cost rs es) := by
  obtain ⟨n,hn,c,hr,hh,ht,_⟩ := selects rho width flag hrw hrf hwf v rs es cr hrr hrh her heh hfr hfh
  rintro w rfl
  exact ⟨n,c,hn,hr,hh,ht⟩

end
end IntegerMultBounds.Machine.ArbitraryWidthHighBranchPlacement
