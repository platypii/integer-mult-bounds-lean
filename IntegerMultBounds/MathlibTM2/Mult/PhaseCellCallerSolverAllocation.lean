module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryCropPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineInputPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedFullLineRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section

/-- The ordinary full-line input bank and S3 worker have disjoint lifetimes
within a solve, so each receives its own fixed bank. -/
inductive SolverRole where
  | input (i : Fin 303)
  | worker (i : Fin 325)
  | scratch (i : Fin 5)
  | control (i : Fin 7)
  deriving DecidableEq, Fintype

def solverRegisterCount : ℕ := Fintype.card SolverRole

def solverRoleEquiv : SolverRole ≃ ((Fin 303 ⊕ Fin 325) ⊕ (Fin 5 ⊕ Fin 7)) where
  toFun
    | .input i => .inl (.inl i)
    | .worker i => .inl (.inr i)
    | .scratch i => .inr (.inl i)
    | .control i => .inr (.inr i)
  invFun
    | .inl (.inl i) => .input i
    | .inl (.inr i) => .worker i
    | .inr (.inl i) => .scratch i
    | .inr (.inr i) => .control i
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with (i|i)|(i|i) <;> rfl

theorem solverRegisterCount_eq : solverRegisterCount = 640 := by
  exact (Fintype.card_congr solverRoleEquiv).trans (by simp)

def solverSource {T : ℕ} (i : Fin T) : Fin (T+solverRegisterCount) := Fin.castAdd solverRegisterCount i

def solverRegister (T : ℕ) (r : SolverRole) : Fin (MachineTapes (T+solverRegisterCount)) :=
  unarySource _ (Fin.natAdd T (Fintype.equivFin SolverRole r))

theorem solverRegister_injective (T : ℕ) : Function.Injective (solverRegister T) :=
  (unarySource_injective _).comp ((Fin.natAdd_injective _ _).comp (Fintype.equivFin SolverRole).injective)

private theorem reserved_ne_retained {m n : ℕ} (i : Fin n) (j : Fin m) :
    Fin.natAdd m i ≠ Fin.castAdd n j := by
  intro he
  have hv := congrArg Fin.val he
  change m+i.val = j.val at hv
  have ht : m ≤ j.val := hv ▸ Nat.le_add_right m _
  exact Nat.not_le_of_lt j.isLt ht

theorem solverRegister_ne_source (T : ℕ) (r : SolverRole) (i : Fin T) :
    solverRegister T r ≠ unarySource _ (solverSource i) := by
  intro he
  exact reserved_ne_retained _ i ((unarySource_injective _) he)

theorem solverRegister_ne_header (T : ℕ) (r : SolverRole) (h : Role) :
    solverRegister T r ≠ fullHeader (T+solverRegisterCount) h := by
  intro he
  exact header_ne_bank id h (Fin.natAdd T (Fintype.equivFin SolverRole r))
    (classCallerRegister_injective he.symm)

theorem solverRegister_ne_routing (T : ℕ) (r : SolverRole) (i : Fin tapeCount) :
    solverRegister T r ≠ Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i :=
  prefix_ne_routing _ _

def solverParameterSource : Fin 8 → Option (Fin 11) :=
  ![some 0,some 1,some 2,some 3,some 4,some 5,none,some 4]

def solverParameter (T : ℕ) (src : Fin 11 → Fin T) (i : Fin 8) :
    Fin (MachineTapes (T+solverRegisterCount)) :=
  match solverParameterSource i with
  | none => fullHeader _ .zero
  | some j => unarySource _ (solverSource (src j))

theorem solverParameter_ne_register (T : ℕ) (src : Fin 11 → Fin T) (i : Fin 8) (r : SolverRole) :
    solverParameter T src i ≠ solverRegister T r := by
  unfold solverParameter
  cases solverParameterSource i with
  | none => exact (solverRegister_ne_header T r .zero).symm
  | some j => exact (solverRegister_ne_source T r (src j)).symm

def callerFullLineInput (T : ℕ) (src : Fin 11 → Fin T) : FullLineInputPlan (MachineTapes (T+solverRegisterCount)) where
  work i := solverRegister T (.input i)
  injective := (solverRegister_injective T).comp (by intro i j h; cases h; rfl)
  parameters := solverParameter T src
  word := solverRegister T (.scratch 0)
  saved := solverRegister T (.scratch 1)
  tmp := solverRegister T (.scratch 2)
  queue := solverRegister T (.scratch 3)
  carry := solverRegister T (.scratch 4)
  ambient := fullHeader _ .input
  replicas := unarySource _ (solverSource (src 8))
  parameterRegs i := by
    have hp := solverParameter_ne_register T src i
    simp only [List.nodup_cons,List.not_mem_nil,List.mem_cons,not_or,not_false_eq_true,and_true]
    simp [hp,(solverRegister_injective T).eq_iff]
  copyRegs := by
    have hh := fun r => (solverRegister_ne_header T r .input).symm
    simp [hh,(solverRegister_injective T).eq_iff]
  countRegs := by
    have hs := fun r => (solverRegister_ne_source T r (src 8)).symm
    simp [hs,(solverRegister_injective T).eq_iff]
  ambientOff i := (solverRegister_ne_header T (.input i) .input).symm
  replicasOff i := (solverRegister_ne_source T (.input i) (src 8)).symm
  scratchOff k hk i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> exact (solverRegister_injective T).ne (by simp)

def callerFullLineResult (T : ℕ) : Fin (MachineTapes (T+solverRegisterCount)) :=
  Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) (publicationReg 94)

def callerFullLineProducer (T Q : ℕ) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) :
    PackedProducerPlan (MachineTapes (T+solverRegisterCount)) Q where
  hR := hR
  hQ := hQ
  work i := solverRegister T (.worker i)
  hwork := (solverRegister_injective T).comp (by intro i j h; cases h; rfl)
  src := solverRegister T (.control 0)
  saved := solverRegister T (.control 1)
  count := solverRegister T (.control 2)
  tmp := solverRegister T (.control 3)
  spare := solverRegister T (.control 4)
  result := callerFullLineResult T
  clock := solverRegister T (.control 5)
  savedClock := solverRegister T (.control 6)
  hreg := by
    have hr := fun r => solverRegister_ne_routing T r (publicationReg 94)
    have hr' := fun r => (hr r).symm
    simp [callerFullLineResult,hr,hr',(solverRegister_injective T).eq_iff]
  hsep i := by
    have hr := solverRegister_ne_routing T (.worker i) (publicationReg 94)
    simp [callerFullLineResult,hr,(solverRegister_injective T).eq_iff]

theorem callerFullLine_compatible (T Q : ℕ) (src : Fin 11 → Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) :
    (callerFullLineInput T src).Compatible (callerFullLineProducer T Q hR hQ) := by
  intro i k hk
  simp only [PackedProducerPlan.support,List.mem_append,List.mem_ofFn,
    List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with (⟨j,rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
  all_goals first
    | exact (solverRegister_injective T).ne (by simp)
    | exact solverRegister_ne_routing T (.input i) (publicationReg 94)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
