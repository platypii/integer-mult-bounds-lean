import IntegerMultBounds.Machine.RecursiveChildCallSetup
import IntegerMultBounds.Machine.RecursiveShiftRoleBank

/-! Physical child header/PC setup on the permanent role bank. The two stacks
occupy a fixed suffix of the arbitrary auxiliary bank; every role, scratch tape
and other auxiliary tape is preserved, and private workspace returns blank. -/
namespace IntegerMultBounds.Machine.RecursiveChildSetupRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout RecursiveInterchangeVolume
open RecursiveShiftRoleBank (common headers)
variable {t u k : ℕ}

def ports : Fin 8 → Fin 40 := ![3,4,5,6,7,8,38,39]

theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]

def commonPorts : Fin 8 → Fin (t+(7+(u+2))) :=
  fun i => Fin.addCases (motive := fun _ => Fin (t+(7+(u+2))))
    (fun j : Fin 6 => Fin.natAdd t (Fin.castAdd (u+2) (Fin.natAdd 1 j)))
    (fun j : Fin 2 => Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd u j))) i

private theorem commonPorts_value (i : Fin 8) :
    (commonPorts (t := t) (u := u) i).val = if i.val < 6 then t+1+i.val else t+7+u+(i.val-6) := by
  fin_cases i <;> simp [commonPorts,Fin.addCases] <;> omega

theorem commonPorts_injective : Function.Injective (commonPorts (t := t) (u := u)) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [commonPorts_value,commonPorts_value] at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

private theorem local_payload (hs : Fin 6 → List Bool) (st : Tapes 2 prime) :
    SharedBank.payload (RecursiveChildCallSetup.bank hs st) ports = (headers hs).append st := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem local_clean (hs : Fin 6 → List Bool) (st : Tapes 2 prime) :
    SharedBank.strip (RecursiveChildCallSetup.bank hs st) ports = SharedBank.empty 40 prime := by
  have hb (i : Fin 40) (hi : ¬∃ j, ports j = i) :
      (RecursiveChildCallSetup.bank hs st).head i = 0 ∧
      (RecursiveChildCallSetup.bank hs st).tape i = fun _ => blank := by
    have hn : (i.val < 3 ∨ 9 ≤ i.val) ∧ i.val < 38 := by
      have h : ∀ i : Fin 40, (¬∃ j, ports j = i) → (i.val < 3 ∨ 9 ≤ i.val) ∧ i.val < 38 := by decide
      exact h i hi
    fin_cases i <;> norm_num at hn <;> exact ⟨rfl,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hb i hi).1
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hb i hi).2

theorem common_payload (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    SharedBank.payload (common roles hs (aux.append st)) commonPorts = (headers hs).append st := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    change Fin (6+2) at i
    induction i using Fin.addCases with
    | left i => simp only [common,commonPorts,Tapes.append,Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [common,commonPorts,Tapes.append,Fin.addCases_right]

theorem common_frame (roles : Tapes t prime) (hs ch : Fin 6 → List Bool)
    (aux : Tapes u prime) (st st' : Tapes 2 prime) :
    SharedBank.strip (common roles hs (aux.append st)) commonPorts =
      SharedBank.strip (common roles ch (aux.append st')) commonPorts := by
  have he (i : Fin (t+(7+(u+2)))) (hi : ¬∃ j, commonPorts (t := t) (u := u) j = i) :
      (common roles hs (aux.append st)).head i = (common roles ch (aux.append st')).head i ∧
      (common roles hs (aux.append st)).tape i = (common roles ch (aux.append st')).tape i := by
    induction i using Fin.addCases with
    | left i => simp only [common,Tapes.append,Fin.addCases_left]; trivial
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        change Fin (1+6) at i
        induction i using Fin.addCases with
        | left i => simp only [common,Tapes.append,Fin.addCases_left,Fin.addCases_right]; trivial
        | right i => exact (hi ⟨Fin.castAdd 2 i,by simp only [commonPorts,Fin.addCases_left]⟩).elim
      | right i =>
        induction i using Fin.addCases with
        | left i => simp only [common,Tapes.append,Fin.addCases_left,Fin.addCases_right]; trivial
        | right i => exact (hi ⟨Fin.natAdd 6 i,by simp only [commonPorts,Fin.addCases_right]⟩).elim
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, commonPorts (t := t) (u := u) j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte] using (he i hi).1
  · funext i
    by_cases hi : ∃ j, commonPorts (t := t) (u := u) j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte] using (he i hi).2

/-- Any exact clean header/stack operation on the constructor bank lifts to
these permanent ports without disturbing arbitrary role and auxiliary tapes. -/
theorem placed_hoare {s B : ℕ} (M : Program 40 s prime)
    (roles : Tapes t prime) (hs ch : Fin 6 → List Bool) (aux : Tapes u prime)
    (st st' : Tapes 2 prime)
    (h : HoareTime M (fun w => w = RecursiveChildCallSetup.bank hs st)
      (fun w => w = RecursiveChildCallSetup.bank ch st') B) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports commonPorts
        (commonPorts_injective (t := t) (u := u))))
      (fun w => w = CleanSubbank.bank (common roles hs (aux.append st)))
      (fun w => w = CleanSubbank.bank (common roles ch (aux.append st'))) B := by
  apply CleanSubbank.realizes _ ports commonPorts ports_injective commonPorts_injective _ _
    (RecursiveChildCallSetup.bank hs st) (RecursiveChildCallSetup.bank ch st') _
  · exact (local_payload hs st).trans (common_payload roles hs aux st).symm
  · exact (local_payload ch st').trans (common_payload roles ch aux st').symm
  · exact local_clean hs st
  · exact local_clean ch st'
  · exact common_frame roles hs ch aux st st'
  · exact h

def program (roles : ℕ) {m : ℕ} (i j : Fin m) (code : FiniteReturnStack.Code k) :=
  Placement.placed (RecursiveChildCallSetup.program Shared50ModularControl.prime_prime.two_le roles i j code)
    (CleanSubbank.placement ports (commonPorts (t := t) (u := u)) commonPorts_injective)

/-- Child dimensions and saved parent/PC frames are physically produced in
fixed permanent ports; the arbitrary role arrays never enter the constructor. -/
theorem prepares {roles m n depth : ℕ} {root parent : Descriptor}
    (path : Path prime roles m root n parent) (hr : 0 < roles) (hm : 2 ≤ m)
    (hwroot : root.width = m^depth) (hvroot : root.Positive)
    (b : ℕ) (i j : Fin m) (hw : parent.width = m*b) (hdiv : roles ∣ parent.rows)
    (hs : Fin 6 → List Bool) (hh : RecursiveDimensionBank.Headers parent hs)
    (roleBank : Tapes t prime) (aux : Tapes u prime) (st : Tapes 2 prime) (code : FiniteReturnStack.Code k) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (child prime roles b parent i j) ch ∧
      HoareTime (program (t := t) (u := u) roles i j code)
        (fun w => w = CleanSubbank.bank (common roleBank hs (aux.append st)))
        (fun w => w = CleanSubbank.bank
          (common roleBank ch (aux.append (RecursiveChildCallSetup.savedStacks hs st code))))
        ((RecursiveChildPrepare.constant m roles+24*(Nat.log2 roles+2)+50+k)*volume prime (child prime roles b parent i j)) := by
  obtain ⟨ch,hch,hp⟩ := RecursiveChildCallSetup.prepares path Shared50ModularControl.prime_prime.two_le
    hr hm hwroot hvroot b i j hw hdiv hs hh st code
  refine ⟨ch,hch,?_⟩
  exact placed_hoare _ roleBank hs ch aux st _ hp

end
end IntegerMultBounds.Machine.RecursiveChildSetupRoleBank
