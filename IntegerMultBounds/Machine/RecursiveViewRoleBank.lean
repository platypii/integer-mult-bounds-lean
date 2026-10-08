import IntegerMultBounds.Machine.RecursiveCrossPrepare
import IntegerMultBounds.Machine.RecursiveRoleSerialization

/-! Paid coordinate-view changes on the exact permanent role/scratch/header bank.
A fixed selector handles cross-group fields or two ordered fields within H/D.
Only six occupied headers change; payloads, scratch and every auxiliary tape
(including initialized XOR controls) are retained, and all private work is blank. -/
namespace IntegerMultBounds.Machine.RecursiveViewRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveShiftRoleBank (common headers)
variable {t u m : ℕ}

inductive Selection (m : ℕ) where
  | cross (i j : Fin m)
  | within (group : RecursiveAffineDimensions.Group) (j i : Fin m) (earlier : j < i)

def layout (s : Selection m) (b : ℕ) (v : Descriptor) : Descriptor := match s with
  | .cross i j => RecursiveAffineViews.cross prime b v i j
  | .within g j i _ => RecursiveAffineDimensionsClean.view (q := prime) b v j i g

def constant : Selection m → ℕ
  | .cross _ _ => RecursiveCrossPrepare.constant m
  | .within _ _ _ _ => RecursiveAffinePrepare.constant m

private theorem prime_ge : 2 ≤ prime := Shared50ModularControl.prime_prime.two_le

structure Block where
  states : ℕ
  program : Program 38 states prime

def block : Selection m → Block
  | .cross i j => ⟨_,RecursiveCrossPrepare.program prime_ge i j⟩
  | .within g j i _ => ⟨_,RecursiveAffinePrepare.program prime_ge j i g⟩

theorem layout_volume (s : Selection m) (b : ℕ) (v : Descriptor) (hw : v.width=m*b) :
    volume prime (layout s b v) = volume prime v := by
  cases s with
  | cross i j => exact RecursiveAffineViews.cross_volume prime b v i j hw
  | within g j i hj =>
    cases g
    · exact RecursiveAffineViews.withinH_volume prime b v j i hj hw
    · exact RecursiveAffineViews.withinD_volume prime b v j i hj hw

private theorem prepares (s : Selection m) (b : ℕ) (v : Descriptor) (hw : v.width=m*b)
    (hp : v.Positive) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (layout s b v) ch ∧
      HoareTime (block s).program (fun w => w = RecursiveChildHeaderHandoff.canonical hs)
        (fun w => w = RecursiveChildHeaderHandoff.canonical ch) (constant s*volume prime v) := by
  cases s with
  | cross i j => exact RecursiveCrossPrepare.prepares prime_ge b v i j hw hp hs hv
  | within g j i hj => exact RecursiveAffinePrepare.prepares prime_ge b v j i g hj hw hp hs hv

def ports : Fin 6 → Fin 38 := ![3,4,5,6,7,8]
def commonPorts (j : Fin 6) : Fin (t+(7+u)) :=
  Fin.natAdd t (Fin.castAdd u (Fin.natAdd 1 j))

theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]

theorem commonPorts_injective : Function.Injective (commonPorts (t := t) (u := u)) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [commonPorts,Fin.val_natAdd,Fin.val_castAdd] at hv
  exact Fin.ext (by omega)

def program (s : Selection m) := Placement.placed (block s).program
  (CleanSubbank.placement ports (commonPorts (t := t) (u := u)) commonPorts_injective)

private theorem local_payload (hs : Fin 6 → List Bool) :
    SharedBank.payload (RecursiveChildHeaderHandoff.canonical (q := prime) hs) ports = headers hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem common_payload (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime) :
    SharedBank.payload (common roles hs aux) commonPorts = headers hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;>
    simp only [common,commonPorts,Tapes.append,Fin.addCases_left,Fin.addCases_right,headers]

private theorem local_clean (hs : Fin 6 → List Bool) :
    SharedBank.strip (RecursiveChildHeaderHandoff.canonical (q := prime) hs) ports = SharedBank.empty 38 prime := by
  have hblank (i : Fin 38) (hi : ¬∃ j, ports j = i) :
      (RecursiveChildHeaderHandoff.canonical (q := prime) hs).head i = 0 ∧
      (RecursiveChildHeaderHandoff.canonical (q := prime) hs).tape i = fun _ => blank := by
    fin_cases i <;> first | exact ⟨rfl,rfl⟩ |
      exact (hi ⟨0,rfl⟩).elim | exact (hi ⟨1,rfl⟩).elim | exact (hi ⟨2,rfl⟩).elim |
      exact (hi ⟨3,rfl⟩).elim | exact (hi ⟨4,rfl⟩).elim | exact (hi ⟨5,rfl⟩).elim
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).1
  · funext i
    by_cases hi : ∃ j, ports j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).2

private theorem common_frame (roles : Tapes t prime) (hs ch : Fin 6 → List Bool) (aux : Tapes u prime) :
    SharedBank.strip (common roles hs aux) commonPorts = SharedBank.strip (common roles ch aux) commonPorts := by
  have selected (i : Fin 6) : ∃ j, commonPorts (t := t) (u := u) j =
      Fin.natAdd t (Fin.castAdd u (Fin.natAdd 1 i)) := ⟨i,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases with
    | left i => simp only [common,Tapes.append,Fin.addCases_left]
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        change Fin (1+6) at i
        induction i using Fin.addCases with
        | left i => simp only [common,Tapes.append,Fin.addCases_left,Fin.addCases_right]
        | right i => simp only [selected i,↓reduceIte]
      | right i => simp only [common,Tapes.append,Fin.addCases_right]

/-- This same fixed machine installs the selected coordinate view at every
supported runtime width. Parent headers must be saved/restored by the caller. -/
theorem realizes (s : Selection m) (b : ℕ) (v : Descriptor) (hw : v.width=m*b)
    (hp : v.Positive) (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (hv : RecursiveDimensionBank.Headers v hs) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (layout s b v) ch ∧
      HoareTime (program (t := t) (u := u) s)
        (fun w => w = CleanSubbank.bank (common roles hs aux))
        (fun w => w = CleanSubbank.bank (common roles ch aux)) (constant s*volume prime v) := by
  obtain ⟨ch,hch,hh⟩ := prepares s b v hw hp hs hv
  refine ⟨ch,hch,?_⟩
  apply CleanSubbank.realizes _ ports commonPorts ports_injective commonPorts_injective
    _ _ (RecursiveChildHeaderHandoff.canonical hs) (RecursiveChildHeaderHandoff.canonical ch) _
  · exact (local_payload hs).trans (common_payload roles hs aux).symm
  · exact (local_payload ch).trans (common_payload roles ch aux).symm
  · exact local_clean hs
  · exact local_clean ch
  · exact common_frame roles hs ch aux
  · exact hh

/-- The new dependent payload type uses exactly the same physical role tapes. -/
theorem roles_view (s : Selection m) (b : ℕ) (v : Descriptor) (hw : v.width=m*b)
    (data : Fin t → Fin (volume prime v) → Fin 4) :
    RecursiveRoleSerialization.roles (fun wire => RecursiveAffineViews.array prime (layout_volume s b v hw) (data wire)) =
      RecursiveRoleSerialization.roles data := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext wire
    change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0
        (List.ofFn (RecursiveAffineViews.array prime (layout_volume s b v hw) (data wire)))) =
      FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0 (List.ofFn (data wire)))
    rw [RecursiveAffineViews.array_word]

end
end IntegerMultBounds.Machine.RecursiveViewRoleBank
