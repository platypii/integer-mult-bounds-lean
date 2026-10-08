import IntegerMultBounds.Machine.RecursiveRowsNodeHeaders
import IntegerMultBounds.Machine.RecursiveRowsSerialization

/-! Physical installation of the network's row descriptor on the permanent
role bank. All payloads and auxiliary stacks are framed; private tapes clear. -/
namespace IntegerMultBounds.Machine.RecursiveRowsNodeRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveShiftRoleBank (common headers)
variable {t u : ℕ}

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

def program (roles : ℕ) := Placement.placed (RecursiveRowsNodeHeaders.program (q := prime) roles)
  (CleanSubbank.placement ports (commonPorts (t := t) (u := u)) commonPorts_injective)

private theorem local_payload (hs : Fin 6 → List Bool) :
    SharedBank.payload (RecursiveChildQuotients.input (a := prime) hs) ports = headers hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded _

private theorem common_payload (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime) :
    SharedBank.payload (common roles hs aux) commonPorts = headers hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;>
    simp only [common,commonPorts,Tapes.append,Fin.addCases_left,Fin.addCases_right,headers]

private theorem local_clean (hs : Fin 6 → List Bool) :
    SharedBank.strip (RecursiveChildQuotients.input (a := prime) hs) ports = SharedBank.empty 38 prime := by
  have hblank (i : Fin 38) (hi : ¬∃ j, ports j = i) :
      (RecursiveChildQuotients.input (a := prime) hs).head i = 0 ∧
      (RecursiveChildQuotients.input (a := prime) hs).tape i = fun _ => blank := by
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

def constant (roles : ℕ) := RecursiveRowsQuotient.constant roles+30

theorem realizes (c : ℕ) (hc : 0 < c) (v : Descriptor) (hp : v.Positive)
    (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (hv : RecursiveDimensionBank.Headers v hs) :
    ∃ rs : List Bool, RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.role v c)
      (RecursiveRowsNodeHeaders.headers hs rs) ∧
      HoareTime (program (t := t) (u := u) c)
        (fun w => w = CleanSubbank.bank (common roles hs aux))
        (fun w => w = CleanSubbank.bank (common roles (RecursiveRowsNodeHeaders.headers hs rs) aux))
        (constant c*volume prime v) := by
  obtain ⟨rs,hrc,hrv,hrlen,hh⟩ := RecursiveRowsNodeHeaders.constructs_hoare (q := prime) c hc hs
  have hvrows : Counter.value (hs 1) = v.rows := hv.1 1
  have hrows : v.rows ≤ volume prime v := by
    have h := (RecursiveRowsDimensions.products_le Shared50ModularControl.prime_prime.two_le 1 v hp).2.2
    simp only [Nat.div_one] at h
    exact (Nat.le_mul_of_pos_left v.rows hp.1).trans h
  have hV : 0 < volume prime v := lt_of_lt_of_le hp.2.1 hrows
  have hh' := hh.consequence (fun _ h => h) (fun _ h => h)
    (RecursiveRowsNodeHeaders.cost_linear c hs rs _ hV (hv.2 1) (hvrows ▸ hrows) hrlen)
  refine ⟨rs,RecursiveRowsNodeHeaders.headers_correct v hs rs c hv hrc (hrv.trans (congrArg (fun n => n/c) hvrows)),?_⟩
  apply CleanSubbank.realizes _ ports commonPorts ports_injective commonPorts_injective
    _ _ (RecursiveChildQuotients.input hs)
      (RecursiveChildQuotients.input (RecursiveRowsNodeHeaders.headers hs rs)) _
  · exact (local_payload hs).trans (common_payload roles hs aux).symm
  · exact (local_payload _).trans (common_payload roles _ aux).symm
  · exact local_clean hs
  · exact local_clean _
  · exact common_frame roles hs _ aux
  · exact hh'

end
end IntegerMultBounds.Machine.RecursiveRowsNodeRoleBank
