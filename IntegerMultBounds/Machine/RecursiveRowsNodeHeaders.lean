import IntegerMultBounds.Machine.RecursiveRowsQuotient
import IntegerMultBounds.Machine.BinaryDescriptorReplaceList
import IntegerMultBounds.Machine.RecursiveRowsNodeLayout

/-! Paid installation of the reduced-row descriptor, including destruction of
both the original row header and its temporary quotient copy. -/
namespace IntegerMultBounds.Machine.RecursiveRowsNodeHeaders
open BinaryDescriptorInstallMarkedList
variable {q : ℕ}
noncomputable section

def headers (hs : Fin 6 → List Bool) (rs : List Bool) := Function.update hs 1 rs
def instruction : Instruction 38 := ⟨10,4,by decide⟩
def instructions := [instruction]
def words (xs : List Bool) : Fin 38 → List Bool := fun _ => xs

def installProgram := seq
  (BinaryDescriptorReplaceList.program (q := q) (by decide : 0 < 38) instructions)
  (BinaryDescriptorCleanupList.oneProgram (a := q) (10 : Fin 38))

def installCost (hs : Fin 6 → List Bool) (rs : List Bool) :=
  BinaryDescriptorReplaceList.cost instructions (words (hs 1)) (words rs)+1+2*rs.length+4

theorem install_hoare (hs : Fin 6 → List Bool) (rs : List Bool) :
    HoareTime (installProgram (q := q))
      (fun v => v = RecursiveChildQuotients.bank hs none (some rs) none)
      (fun v => v = RecursiveChildQuotients.input (headers hs rs)) (installCost hs rs) := by
  let v := RecursiveChildQuotients.bank (a := q) hs none (some rs) none
  let w := BinaryDescriptorReplaceList.output instructions (words rs) v
  have hi := BinaryDescriptorReplaceList.replaces_hoare (q := q) (by decide : 0 < 38)
    instructions (by intro a ha b hb; simp [instructions] at ha hb; subst a; subst b; decide)
    (by unfold BinaryDescriptorInstallMarkedList.Unique instructions; decide) (words (hs 1)) (words rs) v
    (by intro op hop; simp [instructions] at hop; subst op; exact ⟨rfl, BinaryDescriptorStackRoundtrip.descriptor_encoded rs⟩)
    (by intro op hop; simp [instructions] at hop; subst op; exact ⟨rfl, BinaryDescriptorStackRoundtrip.descriptor_encoded (hs 1)⟩)
  have hf := BinaryDescriptorReplaceList.output_frame instructions (words rs) v 10 (by decide)
  have he := BinaryDescriptorCleanupList.one_hoare (a := q) (10 : Fin 38) w rs
    (hf.2.trans rfl) (hf.1.trans rfl)
  have h := hi.seq he
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded rs).symm

def program (roles : ℕ) := seq (RecursiveRowsQuotient.program (a := q) roles) installProgram
def cost (roles : ℕ) (hs : Fin 6 → List Bool) (rs : List Bool) :=
  RecursiveRowsQuotient.cost roles hs+1+installCost hs rs

theorem constructs_hoare (roles : ℕ) (hr : 0 < roles) (hs : Fin 6 → List Bool) :
    ∃ rs : List Bool, GrowingCounterData.Canonical rs ∧
      Counter.value rs = Counter.value (hs 1)/roles ∧ rs.length ≤ (hs 1).length ∧
      HoareTime (program (q := q) roles) (fun v => v = RecursiveChildQuotients.input hs)
        (fun v => v = RecursiveChildQuotients.input (headers hs rs)) (cost roles hs rs) := by
  obtain ⟨rs,hc,hv,hl,hh⟩ := RecursiveRowsQuotient.quotient_hoare (a := q) roles hr hs
  exact ⟨rs,hc,hv,hl,hh.seq (install_hoare hs rs)⟩

theorem headers_correct (v : RecursiveInterchangeLayout.Descriptor)
    (hs : Fin 6 → List Bool) (rs : List Bool) (roles : ℕ)
    (hh : RecursiveDimensionBank.Headers v hs) (hc : GrowingCounterData.Canonical rs)
    (hr : Counter.value rs = v.rows/roles) :
    RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.role v roles) (headers hs rs) := by
  constructor
  · intro i
    fin_cases i <;> simp [headers,RecursiveDimensionBank.values,RecursiveInterchangeLayout.role] at *
    all_goals first | exact hh.1 _ | exact hr
  · intro i
    by_cases hi : i = 1
    · subst i; simpa [headers] using hc
    · simpa [headers,hi] using hh.2 i

theorem cost_linear (roles : ℕ) (hs : Fin 6 → List Bool) (rs : List Bool)
    (V : ℕ) (hV : 0 < V) (hc : GrowingCounterData.Canonical (hs 1))
    (hv : Counter.value (hs 1) ≤ V) (hl : rs.length ≤ (hs 1).length) :
    cost roles hs rs ≤ (RecursiveRowsQuotient.constant roles+30)*V := by
  have hq := RecursiveRowsQuotient.cost_linear roles hs V hV hc hv
  have hw := GrowingCounterData.canonical_width (hs 1) hc
  have hlog := Nat.log2_le_self (Counter.value (hs 1))
  have hi := BinaryDescriptorReplaceList.cost_le instructions (words (hs 1)) (words rs) (V+1)
    (by intro op hop; exact le_trans hw (by omega))
    (by intro op hop; exact le_trans hl (le_trans hw (by omega)))
  simp only [instructions,List.length_singleton] at hi
  unfold cost installCost instructions at *
  nlinarith

end
end IntegerMultBounds.Machine.RecursiveRowsNodeHeaders
