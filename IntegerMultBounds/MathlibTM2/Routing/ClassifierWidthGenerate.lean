module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryScalarWidthBatch
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStageWidths

/-! Generate the four exact classifier widths from the existing canonical
palette and residue geometry, preserving those source words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def classifierWidthJobs : List (Fin 4) := [0,1,2,3]
def classifierWidthRawWidth (L W : ℕ) : Fin 4 → ℕ := ![W,L,W,L]
def classifierWidthValue (p : Par) : Fin 4 → ℕ := ![p.K,p.n,p.ρ+1,p.m]
def classifierWidthSource : Fin 4 → Fin 118 := ![28,11,31,19]
def classifierWidthDestination (i : Fin 4) : Fin 118 := ⟨108+i.val,by have := i.isLt; omega⟩
def classifierWidthSlot (i : Fin 4) : Fin 6 → Fin 118 :=
  ![classifierWidthSource i,39,classifierWidthDestination i,40,41,9]

theorem classifierWidthSlot_injective (i : Fin 4) : Function.Injective (classifierWidthSlot i) := by
  fin_cases i <;> decide +kernel

def classifierWidthGenerateProgram (rg : Fin 118 → Fin T) : Pr P T Q A U :=
  binaryScalarWidthBatchProgram (fun i => rg ∘ classifierWidthSlot i) classifierWidthJobs

def classifierWidthBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (L W : ℕ) (p : Par) :=
  binaryScalarWidthBatchBank R (fun i => rg ∘ classifierWidthSlot i)
    (classifierWidthRawWidth L W) (classifierWidthValue p) classifierWidthJobs

theorem classifierWidthBank_at (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L W : ℕ) (p : Par) (i : Fin 4) :
    classifierWidthBank R rg L W p (rg (classifierWidthDestination i)) =
      binSyms (classifierWidthRawWidth L W i) (canonicalScalarWidth (classifierWidthValue p i)) := by
  have hd : (classifierWidthJobs.map (fun i => (rg ∘ classifierWidthSlot i) 2)).Nodup := by
    simp [classifierWidthJobs,classifierWidthSlot,classifierWidthDestination,hrg.eq_iff]
  exact binaryScalarWidthBatchBank_at R _ _ _ classifierWidthJobs hd i
    (by fin_cases i <;> simp [classifierWidthJobs])

theorem classifierWidthGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L W : ℕ) (p : Par)
    (hfit : ∀ i, classifierWidthValue p i < 2 ^ classifierWidthRawWidth L W i)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : ∀ i, S.R (rg (classifierWidthSource i)) =
      binSyms (classifierWidthRawWidth L W i) (classifierWidthValue p i))
    (hblank : ∀ i : Fin 118, i ∈ ([39,40,41,108,109,110,111] : List (Fin 118)) → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 8 * (L*L + W*W) + 52 * (L+W) + 89 ∧
      Exec body (classifierWidthGenerateProgram rg) (mk v S) m
        (mk v' { S with R := classifierWidthBank S.R rg L W p }) := by
  have hd : (classifierWidthJobs.map (fun i => (rg ∘ classifierWidthSlot i) 2)).Nodup := by
    simp [classifierWidthJobs,classifierWidthSlot,classifierWidthDestination,hrg.eq_iff]
  have sep : ∀ i j, j ≠ 2 → ∀ k, classifierWidthSlot i j ≠ classifierWidthSlot k 2 := by
    decide +kernel
  obtain ⟨v',m,hu,hm,he⟩ := binaryScalarWidthBatch_exec body
    (fun i => rg ∘ classifierWidthSlot i) (fun i => hrg.comp (classifierWidthSlot_injective i))
    (classifierWidthRawWidth L W) (classifierWidthValue p) hfit classifierWidthJobs hd
    (fun i j hj k => hrg.ne (sep i j hj k)) v S hsrc (by
      intro i j h0 h5
      apply hblank
      fin_cases i <;> fin_cases j <;> simp_all [classifierWidthSlot,classifierWidthDestination])
  refine ⟨v',m,hu,?_,he⟩
  simp [classifierWidthJobs,binaryScalarWidthBatchCost,classifierWidthRawWidth] at hm
  nlinarith only [hm]

end IntegerMultBounds.MathlibTM2.Routing
