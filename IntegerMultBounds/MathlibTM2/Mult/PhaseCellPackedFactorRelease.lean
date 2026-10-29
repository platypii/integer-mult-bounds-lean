module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime

/-! Clear only the owned factor bank. Borrowed source/result suffixes and the
routed table are outside this bank. Stock determines the complete disposal cost. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedFactorOwnedIndices : List (Fin 224) :=
  (List.finRange 224).filter (fun i => 154 ≤ i.val ∧ i ≠ 206)

def packedFactorOwnedReg (i : Fin 224) : Fin 248 :=
  Fin.castLE (by decide) (packedBoundaryFactorReg (preparedBoundaryCoreReg i))

theorem packedFactorOwnedReg_injective : Function.Injective packedFactorOwnedReg := by
  intro i j hij
  apply preparedBoundaryCoreReg_injective
  apply packedBoundaryFactorReg_injective
  apply Fin.ext
  exact congrArg (fun k : Fin 248 => k.val) hij

theorem packedFactorOwnedReg_bounds (i : Fin 224) (hi : i ∈ packedFactorOwnedIndices) :
    168 ≤ (packedFactorOwnedReg i).val ∧ (packedFactorOwnedReg i).val < 238 ∧
      packedFactorOwnedReg i ≠ 220 := by
  have hn : 154 ≤ i.val ∧ i ≠ 206 := by simpa [packedFactorOwnedIndices] using hi
  have h140 : i ≠ 140 := by intro he; subst i; omega
  have h143 : i ≠ 143 := by intro he; subst i; omega
  have hi224 := i.isLt
  have hval206 : i.val ≠ 206 := fun he => hn.2 (Fin.ext he)
  simp only [packedFactorOwnedReg,preparedBoundaryCoreReg,packedBoundaryFactorReg,
    Fin.val_castLE] at *
  simp [Fin.ext_iff,show i.val ≠ 140 by omega,show i.val ≠ 143 by omega,hval206,
    show ¬ i.val < 154 by omega]
  omega

def packedFactorOwnedRegs : List (Fin 248) := packedFactorOwnedIndices.map packedFactorOwnedReg

theorem packedFactorOwnedRegs_nodup : packedFactorOwnedRegs.Nodup := by
  exact ((List.nodup_finRange 224).filter _).map packedFactorOwnedReg_injective

def packedFactorReleased {A : ℕ} (S : Stacks 248 A) : Stacks 248 A :=
  {S with R := fun i => if i ∈ packedFactorOwnedRegs then [] else S.R i}

def packedFactorReleaseCost (D : ℕ) : ℕ :=
  2*(packedFactorOwnedIndices.length*D)+2*packedFactorOwnedRegs.length+1

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedFactorRelease : Pr P 248 Q A U := clearWords packedFactorOwnedRegs

theorem packedFactorRelease_exec (D : ℕ) (v : HS 248 Q A U) (S : Stacks 248 A)
    (hstock : ∀ i ∈ packedFactorOwnedIndices, (S.R (packedFactorOwnedReg i)).length ≤ D) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedFactorReleaseCost D ∧
      Exec body packedFactorRelease (mk v S) n (mk v' (packedFactorReleased S)) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) packedFactorOwnedRegs packedFactorOwnedRegs_nodup v S
  have hsum : (packedFactorOwnedRegs.map fun i => (S.R i).length).sum ≤ packedFactorOwnedIndices.length*D := by
    change ((packedFactorOwnedIndices.map packedFactorOwnedReg).map fun i => (S.R i).length).sum ≤ _
    rw [List.map_map]
    have hbound (is : List (Fin 224)) (his : ∀ i ∈ is, i ∈ packedFactorOwnedIndices) :
        (is.map fun i => (S.R (packedFactorOwnedReg i)).length).sum ≤ is.length*D := by
      induction is with
      | nil => simp
      | cons i is ih =>
        have hi := hstock i (his i (by simp))
        have ht := ih (fun j hj => his j (by simp [hj]))
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
    exact hbound _ (fun _ hi => hi)
  exact ⟨v',_,hu,by dsimp [packedFactorReleaseCost]; omega,he⟩

theorem packedFactorReleased_off {A : ℕ} (S : Stacks 248 A) (i : Fin 248)
    (hi : i ∉ packedFactorOwnedRegs) : (packedFactorReleased S).R i = S.R i := by
  simp [packedFactorReleased,hi]

theorem packedFactorOwnedRegs_bounds (i : Fin 248) (hi : i ∈ packedFactorOwnedRegs) :
    168 ≤ i.val ∧ i.val < 238 ∧ i ≠ 220 := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  exact packedFactorOwnedReg_bounds j hj

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
