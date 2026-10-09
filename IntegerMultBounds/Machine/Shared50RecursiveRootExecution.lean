import IntegerMultBounds.Machine.Shared50RecursiveInduction
import IntegerMultBounds.Machine.Shared50RecursiveBudgetBound

/-! Full execution of the actual fixed root interchange program on power-width
binary arrays. Root descriptor/return-frame construction, recursive execution,
physical restoration, and genuine halt are all included. The complete bank is
restored except for the exact full H/D transpose of the sole I/O array. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveRootExecution
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50RecursiveControl
open Shared50RecursiveImplementation (implementation width pcStack returnWidth returnCapacity)
open Shared50RecursiveBaseExecution (entryConfig)
open Shared50RecursiveBank (bank)
open Shared50RecursiveCallReady (Ready)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeRows (transpose)
open Shared50RecursiveNodeLayout (wires)
open RecursiveRoleSerialization (roles)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
variable {k depth : ℕ}
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50FixedControl.control
  Shared50RecursiveCallLayout.parked Shared50RecursiveBudget.base Shared50RecursiveBudget.node

/-- Canonical blank work tapes satisfy every allocation invariant automatically. -/
theorem blank_ready : Ready (fun _ => blank) 0 (SharedBank.empty 1 prime)
    (SharedBank.empty 1 prime) (SharedBank.empty 2 prime) :=
  ⟨fun _ _ => rfl,fun _ _ => rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩

/-- The actual graph started with its physically saved root sentinel reaches
its halt node with exact transposed data and all original caller tapes. -/
theorem graph_hoare (capacity : Fintype.card PC ≤ 2^k)
    (v : Descriptor) (shape : Shared50RecursiveDepth.Shape depth v)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    HoareTime (Shared50RecursiveControl.program capacity width pcStack (implementation k))
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
        (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks hs st (rootCode capacity)))
        (tapeCount capacity width pcStack (implementation k)))
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (transpose (one_dvd v.rows) x)))) hs f p node scalar (SharedBank.empty 0 prime) st)
        (tapeCount capacity width pcStack (implementation k)))
      (Shared50RecursiveBudget.budget k depth (volume prime v)) := by
  intro ww hww
  subst ww
  obtain ⟨n,hn,htrace⟩ := Shared50RecursiveInduction.run capacity depth .halt v shape hs hs hv
    (RecursiveRowsNode.header_length v shape.positive hs hv) f p node scalar st ready x
  exact ⟨n,_,hn,htrace,Shared50RecursiveBaseExecution.halt_entry capacity _,rfl⟩

/-- All real root setup steps are charged before the same fixed recursive graph.
No assumed machine block, recursive trace or abstract interchange oracle remains. -/
theorem root_hoare (v : Descriptor) (shape : Shared50RecursiveDepth.Shape depth v)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    HoareTime Shared50RecursiveImplementation.program
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
        (SharedBank.empty 0 prime) st) Shared50RecursiveRoot.tapeCount)
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (transpose (one_dvd v.rows) x)))) hs f p node scalar (SharedBank.empty 0 prime) st)
        Shared50RecursiveRoot.tapeCount)
      (BinaryDescriptorFrames.cost Shared50RecursiveImplementation.rootFields (Shared50RecursiveRoot.words hs)+
        1+returnWidth+1+Shared50RecursiveBudget.budget returnWidth depth (volume prime v)) :=
  Shared50RecursiveRoot.root_hoare (roles (RecursiveRowsSerialization.sourceData wires (encoded x)))
    hs f p node scalar st _ _ (graph_hoare returnCapacity v shape hs hv f p node scalar st ready x)

/-- Root setup and its joining transition add a fixed linear-volume charge. -/
def rootOverhead : ℕ := 74+returnWidth

def rootBudget (depth V : ℕ) : ℕ :=
  rootOverhead*V+Shared50RecursiveBudget.budget returnWidth depth V

theorem root_budget_hoare (v : Descriptor) (shape : Shared50RecursiveDepth.Shape depth v)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    HoareTime Shared50RecursiveImplementation.program
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
        (SharedBank.empty 0 prime) st) Shared50RecursiveRoot.tapeCount)
      (fun ww => ww = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (transpose (one_dvd v.rows) x)))) hs f p node scalar (SharedBank.empty 0 prime) st)
        Shared50RecursiveRoot.tapeCount)
      (rootBudget depth (volume prime v)) := by
  have hsetup := Shared50RecursiveRoot.setup_cost_linear v shape.positive hs hv
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v shape.positive
  apply (root_hoare v shape hs hv f p node scalar st ready x).consequence (fun _ h => h) (fun _ h => h)
  unfold rootBudget rootOverhead
  nlinarith

/-- A single constant for the single fixed compiled root program. -/
def constant : ℝ := rootOverhead+Shared50RecursiveBudgetBound.constant returnWidth

theorem constant_positive : 0 < constant := by
  have h := Shared50RecursiveBudgetBound.constant_positive returnWidth
  have hn : (0 : ℝ) ≤ rootOverhead := Nat.cast_nonneg _
  unfold constant
  linarith

theorem rootBudget_bound (depth V : ℕ) :
    (rootBudget depth V : ℝ) ≤ constant*(V : ℝ)*((125000^depth : ℕ) : ℝ)^Parameters.tau := by
  have hbound := Shared50RecursiveBudgetBound.power_width_bound returnWidth depth V
  have hw : (1 : ℝ) ≤ ((125000^depth : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ (125000 : ℕ)^depth from Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hpow := Real.one_le_rpow hw Shared50RecursiveBudgetBound.exponent_range.1.le
  have hlin : (rootOverhead : ℝ)*V ≤ (rootOverhead : ℝ)*V*((125000^depth : ℕ) : ℝ)^Parameters.tau := by
    nlinarith [show (0 : ℝ) ≤ (rootOverhead : ℝ)*V by positivity]
  simp only [rootBudget,Nat.cast_add,Nat.cast_mul,constant]
  nlinarith

/-- Actual execution of the one fixed root machine halts in the certified
sublinear-width exponent bound and restores every cell/head outside its output.
The shape premises are exactly the current power-width/divisible-row interface. -/
theorem halts_power_bound (v : Descriptor) (shape : Shared50RecursiveDepth.Shape depth v)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    ∃ n : ℕ, ∃ c, (n : ℝ) ≤ constant*(volume prime v : ℝ)*(v.width : ℝ)^Parameters.tau ∧
      Machine.run Shared50RecursiveImplementation.program n
        ((raw (bank (roles (RecursiveRowsSerialization.sourceData wires (encoded x))) hs f p node scalar
          (SharedBank.empty 0 prime) st) Shared50RecursiveRoot.tapeCount).start Shared50RecursiveImplementation.program) =
        some c ∧
      step Shared50RecursiveImplementation.program c = none ∧
      c.tapes = raw (bank (roles (RecursiveRowsSerialization.sourceData wires
        (encoded (transpose (one_dvd v.rows) x)))) hs f p node scalar (SharedBank.empty 0 prime) st)
        Shared50RecursiveRoot.tapeCount := by
  obtain ⟨n,c,hn,htrace,hhalt,hout⟩ := root_budget_hoare v shape hs hv f p node scalar st ready x _ rfl
  have hbound := rootBudget_bound depth (volume prime v)
  rw [← shape.width] at hbound
  exact ⟨n,c,(by exact_mod_cast hn : (n : ℝ) ≤ rootBudget depth (volume prime v)).trans hbound,htrace,hhalt,hout⟩

end
end IntegerMultBounds.Machine.Shared50RecursiveRootExecution
