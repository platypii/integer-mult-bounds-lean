module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierWidthGenerate
public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeBatchScope
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalOuterInput

/-! Install the six nonempty classifier operands using four generated widths.
Both key operands and both residue operands share their exact width source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def classifierScalarJobs : List (Fin 6) := [0,1,2,3,4,5]
def classifierScalarRole : Fin 6 → Fin 16 := ![0,1,10,13,14,15]
def classifierScalarValue (p : Par) : Fin 6 → ℕ := ![p.K,p.G,p.n,p.ρ+1,p.ρ,p.m]
def classifierScalarWidthIndex : Fin 6 → Fin 4 := ![0,0,1,2,2,3]
def classifierScalarSource : Fin 6 → Fin 118 := ![28,29,11,31,30,19]
def classifierScalarDestination (i : Fin 6) : Fin 118 := ⟨112+i.val,by have := i.isLt; omega⟩
def classifierScalarWidth (p : Par) (i : Fin 6) : ℕ :=
  canonicalScalarWidth (classifierWidthValue p (classifierScalarWidthIndex i))
def classifierScalarInputWidth (L W : ℕ) (i : Fin 6) : ℕ :=
  classifierWidthRawWidth L W (classifierScalarWidthIndex i)
def classifierScalarSlot (i : Fin 6) : Fin 9 → Fin 118 :=
  ![classifierWidthDestination (classifierScalarWidthIndex i),classifierScalarSource i,45,
    classifierScalarDestination i,39,40,41,42,43]

theorem classifierScalarSlot_injective (i : Fin 6) : Function.Injective (classifierScalarSlot i) := by
  fin_cases i <;> decide +kernel

theorem classifierScalarRole_injective : Function.Injective classifierScalarRole := by decide +kernel

theorem classifierScalar_operands {A : ℕ} (p : Par) (i : Fin 6) :
    (binSyms (classifierScalarWidth p i) (classifierScalarValue p i) : List (Fin (A + 4))) =
      canonicalClassifierOperands p (canonicalScalarWidth p.K) (canonicalScalarWidth p.n)
        (canonicalScalarWidth (p.ρ+1)) (canonicalScalarWidth p.m) (classifierScalarRole i) := by
  fin_cases i <;> rfl

def classifierScalarInstallProgram (rg : Fin 118 → Fin T) : Pr P T Q A U :=
  binaryResizeBatchProgram (fun i => rg ∘ classifierScalarSlot i) classifierScalarJobs

def classifierScalarInstalledBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (p : Par) :=
  binaryResizeBatchBank R (fun i => rg ∘ classifierScalarSlot i)
    (classifierScalarWidth p) (classifierScalarValue p) classifierScalarJobs

theorem classifierScalarInstalledBank_at (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (p : Par) (i : Fin 6) :
    classifierScalarInstalledBank R rg p (rg (classifierScalarDestination i)) =
      canonicalClassifierOperands p (canonicalScalarWidth p.K) (canonicalScalarWidth p.n)
        (canonicalScalarWidth (p.ρ+1)) (canonicalScalarWidth p.m) (classifierScalarRole i) := by
  have hd : (classifierScalarJobs.map (fun i => (rg ∘ classifierScalarSlot i) 3)).Nodup := by
    simp [classifierScalarJobs,classifierScalarSlot,classifierScalarDestination,hrg.eq_iff]
  rw [classifierScalarInstalledBank,
    show rg (classifierScalarDestination i) = (rg ∘ classifierScalarSlot i) 3 from rfl,
    binaryResizeBatchBank_at _ _ _ _ _ hd i (by fin_cases i <;> simp [classifierScalarJobs])]
  exact classifierScalar_operands p i

theorem classifierScalarInstall_exec (body : P → Pr P T Q A U)
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L W : ℕ) (p : Par)
    (hwidthFit : ∀ i, classifierScalarWidth p i < 2 ^ classifierScalarInputWidth L W i)
    (hvalueFit : ∀ i, classifierScalarValue p i < 2 ^ classifierScalarInputWidth L W i)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : ∀ i, S.R (rg (classifierWidthDestination (classifierScalarWidthIndex i))) =
      binSyms (classifierScalarInputWidth L W i) (classifierScalarWidth p i))
    (hvalue : ∀ i, S.R (rg (classifierScalarSource i)) =
      binSyms (classifierScalarInputWidth L W i) (classifierScalarValue p i))
    (hblank : ∀ i : Fin 118,
      i ∈ ([39,40,41,42,43,45,112,113,114,115,116,117] : List (Fin 118)) → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ binaryResizeBatchCost (classifierScalarInputWidth L W) (classifierScalarInputWidth L W)
        (classifierScalarWidth p) classifierScalarJobs ∧
      Exec body (classifierScalarInstallProgram rg) (mk v S) m
        (mk v' { S with R := classifierScalarInstalledBank S.R rg p }) := by
  have hd : (classifierScalarJobs.map (fun i => (rg ∘ classifierScalarSlot i) 3)).Nodup := by
    simp [classifierScalarJobs,classifierScalarSlot,classifierScalarDestination,hrg.eq_iff]
  have sep : ∀ i j, j ≠ 3 → ∀ k, classifierScalarSlot i j ≠ classifierScalarSlot k 3 := by
    decide +kernel
  apply binaryResizeBatch_exec body (fun i => rg ∘ classifierScalarSlot i)
    (fun i => hrg.comp (classifierScalarSlot_injective i))
    (classifierScalarInputWidth L W) (classifierScalarInputWidth L W)
    (classifierScalarWidth p) (classifierScalarValue p) hwidthFit hvalueFit classifierScalarJobs hd
    (fun i j hj k => hrg.ne (sep i j hj k)) v S hwidth hvalue
  · intro i _
    apply hblank
    fin_cases i <;> decide
  · intro i j h0 h1 h3
    apply hblank
    fin_cases j <;> simp_all [classifierScalarSlot]

end
end IntegerMultBounds.MathlibTM2.Routing
