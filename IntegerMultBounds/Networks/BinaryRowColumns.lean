import IntegerMultBounds.Networks.BinaryRowProgram

/-! Literal Boolean row additions on any number of columns implement the
same fixed binary basis word in each column. The XOR action is connected to
the F2 coordinate semantics; no field-operation oracle is used here. -/
namespace IntegerMultBounds.Networks.BinaryRowColumns
open Module BinaryRowProgram
variable {ι κ : Type*} [DecidableEq ι]

def scalar (b : Bool) : ZMod 2 := if b then 1 else 0

def bit (z : ZMod 2) : Bool := decide (z=1)

@[simp] theorem scalar_xor (b c : Bool) : scalar (xor b c)=scalar b+scalar c := by
  cases b <;> cases c <;> decide

@[simp] theorem bit_scalar (b : Bool) : bit (scalar b)=b := by cases b <;> decide

@[simp] theorem scalar_bit (z : ZMod 2) : scalar (bit z)=z := by
  have h : z=0 ∨ z=1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases h with rfl | rfl <;> decide

theorem scalar_injective : Function.Injective scalar := by
  intro b c h
  simpa only [bit_scalar] using congrArg bit h

def execute (op : Op ι) (x : κ → ι → Bool) : κ → ι → Bool :=
  fun column => Function.update (x column) op.target (xor (x column op.target) (x column op.source))

def run (word : List (Op ι)) (x : κ → ι → Bool) : κ → ι → Bool :=
  word.foldl (fun x op => execute op x) x

def coordinates (x : κ → ι → Bool) (column : κ) : ι → ZMod 2 :=
  fun i => scalar (x column i)

theorem execute_coordinates (op : Op ι) (x : κ → ι → Bool) (column : κ) :
    coordinates (execute op x) column=op.execute (coordinates x column) := by
  funext i
  by_cases h : i=op.target
  · subst i
    simp [coordinates,execute,Op.execute]
  · simp [coordinates,execute,Op.execute,Function.update_of_ne h]

theorem run_coordinates (word : List (Op ι)) (x : κ → ι → Bool) (column : κ) :
    coordinates (run word x) column=BinaryRowProgram.run word (coordinates x column) := by
  induction word generalizing x with
  | nil => rfl
  | cons op word ih =>
    change coordinates (run word (execute op x)) column=_
    rw [ih,execute_coordinates]
    rfl

theorem execute_involutive (op : Op ι) : Function.Involutive (execute (κ := κ) op) := by
  intro x
  funext column i
  apply scalar_injective
  have h := congrFun (BinaryRowProgram.execute_involutive op (coordinates x column)) i
  simpa only [← execute_coordinates,coordinates] using h

theorem run_append (u v : List (Op ι)) (x : κ → ι → Bool) :
    run (u++v) x=run v (run u x) := List.foldl_append

theorem reverse_restores (word : List (Op ι)) (x : κ → ι → Bool) :
    run word.reverse (run word x)=x := by
  funext column i
  apply scalar_injective
  have h := congrFun (BinaryRowProgram.reverse_restores word (coordinates x column)) i
  simpa only [← run_coordinates,coordinates] using h

section Basis
variable [Fintype ι] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- Store each vector's coordinates as literal Boolean address bits. -/
noncomputable def encode (b : Basis ι (ZMod 2) E) (x : κ → E) : κ → ι → Bool :=
  fun column i => bit (b.equivFun (x column) i)

omit [DecidableEq ι] in
@[simp] theorem encode_coordinates (b : Basis ι (ZMod 2) E) (x : κ → E) (column : κ) :
    coordinates (encode b x) column=b.equivFun (x column) := by
  funext i
  exact scalar_bit _

/-- One literal fixed XOR word converts every column from the old basis to
the new basis, regardless of the number of runtime columns. -/
theorem basis_run (old new : Basis ι (ZMod 2) E) (x : κ → E) :
    run (basisWord old new) (encode old x)=encode new x := by
  funext column i
  apply scalar_injective
  have h := run_coordinates (basisWord old new) (encode old x) column
  rw [encode_coordinates,basisWord_run] at h
  simpa only [coordinates,encode,scalar_bit] using congrFun h i

end Basis
end IntegerMultBounds.Networks.BinaryRowColumns
