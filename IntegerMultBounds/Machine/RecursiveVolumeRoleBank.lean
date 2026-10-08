import IntegerMultBounds.Machine.RecursiveVolumeClean
import IntegerMultBounds.Machine.RecursiveXorRoleBank

/-! Physical preparation of the mixed-operation permanent bank. Two initially
blank auxiliary tapes become the empty XOR clock and the complete stream-volume
descriptor, while every role, scratch tape, header and spectator is retained.
All private constructor/tracker tapes are returned blank. -/
namespace IntegerMultBounds.Machine.RecursiveVolumeRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveShiftRoleBank (common headers)
variable {t u : ℕ}

private theorem prime_ge : 2 ≤ prime := Shared50ModularControl.prime_prime.two_le

def controls : Option (List Bool) → Tapes 2 prime
  | none => SharedBank.empty 2 prime
  | some bs => RecursiveXorRoleBank.controls bs

def bank (roles : Tapes t prime) (hs : Fin 6 → List Bool) (bs : Option (List Bool)) (aux : Tapes u prime) :=
  common roles hs ((controls bs).append aux)

def ports : Fin 8 → Fin 34 := ![0,16,3,4,5,6,7,8]
def commonPorts : Fin 8 → Fin (t+(7+(2+u))) :=
  fun j => Fin.addCases (motive := fun _ => Fin (t+(7+(2+u))))
    (fun i : Fin 2 => Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd u i)))
    (fun i : Fin 6 => Fin.natAdd t (Fin.castAdd (2+u) (Fin.natAdd 1 i))) j

theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]

private theorem commonPorts_value (i : Fin 8) :
    (commonPorts (t := t) (u := u) i).val = if i.val < 2 then t+7+i.val else t+i.val-1 := by
  fin_cases i <;> simp [commonPorts,Fin.addCases]

theorem commonPorts_injective : Function.Injective (commonPorts (t := t) (u := u)) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [commonPorts_value,commonPorts_value] at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

def program := Placement.placed (RecursiveVolumeClean.program prime_ge)
  (CleanSubbank.placement ports (commonPorts (t := t) (u := u)) commonPorts_injective)

private theorem binary_eq (bs : List Bool) :
    RadixZeroFill.encodedBinary (q := prime) bs = CountedLoopReuseAlphabet.binary bs := by
  rw [← CountedLoopReuseAlphabet.encoding_binary]
  rfl

private theorem local_payload (hs : Fin 6 → List Bool) (bs : Option (List Bool)) :
    SharedBank.payload (RecursiveVolumeClean.bank (q := prime) hs bs) ports = (controls bs).append (headers hs) := by
  apply congrArg₂ Tapes.mk <;> funext i
  · fin_cases i <;> cases bs <;> rfl
  · fin_cases i <;> cases bs <;> try rfl
    exact binary_eq _

private theorem common_payload (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (bs : Option (List Bool)) (aux : Tapes u prime) :
    SharedBank.payload (bank roles hs bs aux) commonPorts = (controls bs).append (headers hs) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    change Fin (2+6) at i
    induction i using Fin.addCases with
    | left i => simp only [bank,commonPorts,common,Tapes.append,Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [bank,commonPorts,common,Tapes.append,Fin.addCases_left,Fin.addCases_right]

private theorem local_clean (hs : Fin 6 → List Bool) (bs : Option (List Bool)) :
    SharedBank.strip (RecursiveVolumeClean.bank (q := prime) hs bs) ports = SharedBank.empty 34 prime := by
  have hselect (i : Fin 17) (hi : RecursiveVolumeClean.keep i = true) :
      ∃ j, ports j = Fin.castAdd 17 i := by
    fin_cases i <;> simp_all [RecursiveVolumeClean.keep,RecursiveVolumeClean.right]
    all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ |
      exact ⟨4,rfl⟩ | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩ | exact ⟨7,rfl⟩
  have hblank (i : Fin 34) (hi : ¬∃ j, ports j = i) :
      (RecursiveVolumeClean.bank (q := prime) hs bs).head i = 0 ∧
      (RecursiveVolumeClean.bank (q := prime) hs bs).tape i = fun _ => blank := by
    change Fin (17+17) at i
    induction i using Fin.addCases with
    | left i =>
      exact RecursiveVolumeClean.private_blank hs bs i
        (Bool.eq_false_iff.mpr (fun hk => hi (hselect i hk)))
    | right i => exact RecursiveVolumeClean.trackers_blank hs bs i
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).1
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).2

private theorem common_frame (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (bs cs : Option (List Bool)) (aux : Tapes u prime) :
    SharedBank.strip (bank roles hs bs aux) commonPorts = SharedBank.strip (bank roles hs cs aux) commonPorts := by
  have selected (i : Fin 2) : ∃ j, commonPorts (t := t) (u := u) j =
      Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd u i)) := ⟨Fin.castAdd 6 i,by simp only [commonPorts,Fin.addCases_left]⟩
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases with
    | left i => simp only [bank,common,Tapes.append,Fin.addCases_left]
    | right i =>
      induction i using Fin.addCases with
      | left i => simp only [bank,common,Tapes.append,Fin.addCases_left,Fin.addCases_right]
      | right i =>
        induction i using Fin.addCases with
        | left i => simp only [selected i,↓reduceIte]
        | right i => simp only [bank,common,Tapes.append,Fin.addCases_right]

/-- The supplied six canonical headers suffice: no clock, length descriptor,
workspace markers, products, or head movements are assumed initialized. -/
theorem realizes (v : Descriptor) (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) :
    HoareTime (program (t := t) (u := u))
      (fun w => w = CleanSubbank.bank (bank roles hs none aux))
      (fun w => w = CleanSubbank.bank (bank roles hs (some (RecursiveVolumeConstruct.bits (q := prime) v)) aux))
      (RecursiveVolumeClean.bound (volume prime v)) := by
  apply CleanSubbank.realizes _ ports commonPorts ports_injective commonPorts_injective
    _ _ (RecursiveVolumeClean.bank hs none) (RecursiveVolumeClean.bank hs (some (RecursiveVolumeConstruct.bits (q := prime) v))) _
  · exact (local_payload hs none).trans (common_payload roles hs none aux).symm
  · exact (local_payload hs _).trans (common_payload roles hs _ aux).symm
  · exact local_clean hs none
  · exact local_clean hs _
  · exact common_frame roles hs none _ aux
  · exact RecursiveVolumeClean.realizes prime_ge v hs hv hp

end
end IntegerMultBounds.Machine.RecursiveVolumeRoleBank
