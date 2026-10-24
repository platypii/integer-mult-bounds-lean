module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierScalarInstall

/-! Generate all classifier operands from six preserved geometry/palette words.
The four exact scalar widths are computed internally and reused. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def classifierWidthScalarIndex : Fin 4 → Fin 6 := ![0,2,3,5]

def classifierGenerateProgram (rg : Fin 118 → Fin T) : Pr P T Q A U :=
  .seq (classifierWidthGenerateProgram rg) (classifierScalarInstallProgram rg)

def classifierGeneratedBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (L W : ℕ) (p : Par) :=
  classifierScalarInstalledBank (classifierWidthBank R rg L W p) rg p

theorem classifierScalarInputWidth_le (L W : ℕ) (i : Fin 6) :
    classifierScalarInputWidth L W i ≤ L+W := by
  fin_cases i <;> simp [classifierScalarInputWidth,classifierWidthRawWidth,classifierScalarWidthIndex]

theorem classifierScalarWidth_le_input (L W : ℕ) (p : Par)
    (hfit : ∀ i, classifierScalarValue p i < 2 ^ classifierScalarInputWidth L W i) (i : Fin 6) :
    classifierScalarWidth p i ≤ classifierScalarInputWidth L W i := by
  have hx : classifierWidthValue p (classifierScalarWidthIndex i) <
      2 ^ classifierScalarInputWidth L W i := by
    have h := hfit (classifierWidthScalarIndex (classifierScalarWidthIndex i))
    fin_cases i <;> exact h
  exact Nat.clog_le_of_le_pow (Nat.succ_le_of_lt hx)

theorem classifierGeneratedBank_low (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L W : ℕ) (p : Par)
    (i : Fin 118) (hi : i.val < 108) :
    classifierGeneratedBank R rg L W p (rg i) = R (rg i) := by
  unfold classifierGeneratedBank classifierScalarInstalledBank classifierWidthBank
  rw [binaryResizeBatchBank_keep,binaryScalarWidthBatchBank_keep]
  · intro hm
    obtain ⟨j,_,he⟩ := List.mem_map.mp hm
    have hv := congrArg (fun x : Fin 118 => x.val) (hrg he)
    change 108 + j.val = i.val at hv
    omega
  · intro hm
    obtain ⟨j,_,he⟩ := List.mem_map.mp hm
    have hv := congrArg (fun x : Fin 118 => x.val) (hrg he)
    change 112 + j.val = i.val at hv
    omega

theorem classifierGeneratedBank_outside (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (L W : ℕ) (p : Par) (k : Fin T) (hoff : ∀ i, rg i ≠ k) :
    classifierGeneratedBank R rg L W p k = R k := by
  unfold classifierGeneratedBank classifierScalarInstalledBank classifierWidthBank
  rw [binaryResizeBatchBank_keep,binaryScalarWidthBatchBank_keep]
  all_goals intro hm; obtain ⟨i,_,he⟩ := List.mem_map.mp hm; exact hoff _ he

theorem classifierGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L W : ℕ) (p : Par)
    (hfit : ∀ i, classifierScalarValue p i < 2 ^ classifierScalarInputWidth L W i)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : ∀ i, S.R (rg (classifierScalarSource i)) =
      binSyms (classifierScalarInputWidth L W i) (classifierScalarValue p i))
    (hblank : ∀ i : Fin 118,
      i ∈ ([39,40,41,42,43,45,108,109,110,111,112,113,114,115,116,117] : List (Fin 118)) →
      S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (8 * (L*L + W*W) + 52 * (L+W) + 89) +
        binaryResizeBatchCost (classifierScalarInputWidth L W) (classifierScalarInputWidth L W)
          (classifierScalarWidth p) classifierScalarJobs ∧
      Exec body (classifierGenerateProgram rg) (mk v S) m
        (mk v' { S with R := classifierGeneratedBank S.R rg L W p }) := by
  have rawfit (i : Fin 4) : classifierWidthValue p i < 2 ^ classifierWidthRawWidth L W i := by
    have h := hfit (classifierWidthScalarIndex i)
    fin_cases i <;> exact h
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := classifierWidthGenerate_exec body rg hrg L W p rawfit v S
    (by intro i; have h := hsrc (classifierWidthScalarIndex i); fin_cases i <;> exact h)
    (by
      intro i hi
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let C : Stacks T A := { S with R := classifierWidthBank S.R rg L W p }
  have keep (i : Fin 118)
      (hi : i ∉ ([108,109,110,111] : List (Fin 118))) : C.R (rg i) = S.R (rg i) := by
    apply binaryScalarWidthBatchBank_keep
    simpa [classifierWidthJobs,classifierWidthSlot,classifierWidthDestination,hrg.eq_iff] using hi
  have widthFit (i : Fin 6) : classifierScalarWidth p i < 2 ^ classifierScalarInputWidth L W i := by
    exact (classifierScalarWidth_le_input L W p hfit i).trans_lt Nat.lt_two_pow_self
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := classifierScalarInstall_exec body rg hrg L W p widthFit hfit v₁ C
    (by intro i; exact classifierWidthBank_at S.R rg hrg L W p (classifierScalarWidthIndex i))
    (by intro i; exact (keep _ (by fin_cases i <;> decide)).trans (hsrc i))
    (by
      intro i hi
      rw [keep _ (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing
