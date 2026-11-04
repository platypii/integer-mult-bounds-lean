module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonClassMasterSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableRetirement
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock

/-! Load the common seed once from eleven retained global words. Its two
owned slots are padded from an empty zero source, not supplied class words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def globalValues (p u l target s t B W N radius width : ℕ) : Fin 11 → ℕ :=
  ![p,u,l,target,s,t,B,W,N,radius,width]

def seedSources (globals : Fin 11 → Fin T) (zero : Fin T) : Fin 13 → Fin T :=
  ![globals 0,globals 1,globals 2,globals 3,globals 4,globals 5,globals 6,
    globals 7,globals 8,globals 9,zero,zero,globals 10]

def sourceBits (D : ℕ) (zero k : Fin T) : ℕ := if k = zero then 0 else D

def sourceValue (value : Fin T → ℕ) (zero k : Fin T) : ℕ := if k = zero then 0 else value k

def loadedSeed (rg : TblR 13 → Fin T) (globals : Fin 11 → Fin T) (zero : Fin T)
    (D : ℕ) (value : Fin T → ℕ) (S : Stacks T A) :=
  loadedInputTable rg (seedSources globals zero) D (sourceValue value zero) S

def seedLoadCost (D : ℕ) := 104*D+113

theorem seedSourceValues (globals : Fin 11 → Fin T) (zero : Fin T) (value : Fin T → ℕ)
    (hoff : ∀ j, globals j ≠ zero) (p u l target s t B W N radius width : ℕ)
    (hvalues : ∀ j, value (globals j) = globalValues p u l target s t B W N radius width j) :
    (fun i => sourceValue value zero (seedSources globals zero i)) = seedValues p u l target s t B W N radius width := by
  funext i
  fin_cases i <;> simp [seedSources,sourceValue,hoff,hvalues,globalValues,seedValues]

theorem seedLoadCost_eq (rg : TblR 13 → Fin T) (globals : Fin 11 → Fin T) (zero : Fin T)
    (hoff : ∀ j, globals j ≠ zero) (D : ℕ) :
    chirpBankLoadCost rg (seedSources globals zero) D 0 (sourceBits D zero) = seedLoadCost D := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,
    List.ofFn_succ,seedSources,sourceBits,hoff,seedLoadCost] <;> omega

theorem loadSeed_exec_within (body : P → Pr P T Q A U) (rg : TblR 13 → Fin T) (hinj : Function.Injective rg)
    (globals : Fin 11 → Fin T) (zero widthMaster : Fin T)
    (hwidthOff : ∀ r, rg r ≠ widthMaster) (hzeroOff : ∀ r, rg r ≠ zero)
    (hglobalOff : ∀ j r, rg r ≠ globals j) (hoff : ∀ j, globals j ≠ zero)
    (D p u l target s t B W N radius width : ℕ) (value : Fin T → ℕ)
    (hvalues : ∀ j, value (globals j) = globalValues p u l target s t B W N radius width j)
    (hfit : ∀ j, value (globals j) < 2^D)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R widthMaster).length = D) (hzero : S.R zero = [])
    (hwords : ∀ j, S.R (globals j) = binSyms D (value (globals j)))
    (hblank : ∀ r, S.R (rg r) = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*seedLoadCost D) depth
        (chirpBankLoad rg (seedSources globals zero) widthMaster zero) (mk v S) (seedLoadCost D)
        (mk v' (loadedSeed rg globals zero D value S)) ∧
      tblHolds rg (loadedSeed rg globals zero D value S)
        (tblRho D (List.replicate D tick) [] ⟨seedValues p u l target s t B W N radius width,[]⟩) ∧
      (∀ j, seedValues p u l target s t B W N radius width j < 2^D) := by
  have hinput (i r) : rg r ≠ seedSources globals zero i := by
    fin_cases i <;> simp [seedSources,hglobalOff,hzeroOff]
  have hfits (i) : sourceValue value zero (seedSources globals zero i) <
      2^sourceBits D zero (seedSources globals zero i) := by
    fin_cases i <;> simp [seedSources,sourceValue,sourceBits,hoff,hfit]
  have hbits (i) : sourceBits D zero (seedSources globals zero i) ≤ D := by
    fin_cases i <;> simp [seedSources,sourceBits,hoff]
  have hsource (i) : S.R (seedSources globals zero i) =
      binSyms (sourceBits D zero (seedSources globals zero i)) (sourceValue value zero (seedSources globals zero i)) := by
    fin_cases i <;> simp [seedSources,sourceBits,sourceValue,hoff,hwords,hzero,binSyms]
  obtain ⟨v',hu,hx⟩ := chirpBankLoad_exec (body := body) rg hinj (seedSources globals zero)
    widthMaster zero hwidthOff hzeroOff hinput D 0 (sourceBits D zero) (sourceValue value zero)
    hfits hbits v S hwidth (by rw [hzero]; rfl) hsource hblank
  rw [seedLoadCost_eq rg globals zero hoff D] at hx
  have hseed := seedSourceValues globals zero value hoff p u l target s t B W N radius width hvalues
  refine ⟨v',hu,mn_native_exec_within hx 3 (chirpBankLoad_native _ _ _ _) depth _ (by omega),?_,?_⟩
  · simpa only [loadedSeed,loadedInputTable,List.replicate_zero,hseed] using
      chirpBankLoad_holds rg hinj (seedSources globals zero) D 0 (sourceValue value zero) S hblank
  · intro j
    rw [←hseed]
    exact (hfits j).trans_le (Nat.pow_le_pow_right (by decide) (hbits j))

/-- Release the shared bank after all classes, retaining the final ambient output. -/
theorem retireSeed_exec_within (body : P → Pr P T Q A U) (rg : TblR 13 → Fin T) (hinj : Function.Injective rg)
    (globals : Fin 11 → Fin T) (zero : Fin T) (D : ℕ) (value : Fin T → ℕ)
    (output : Fin T) (hoff : ∀ r, rg r ≠ output) (ys : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hblank : ∀ r, S.R (rg r) = []) (depth : ℕ) :
    let M := loadedSeed rg globals zero D value S
    let F := {M with R := Function.update M.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords (inputTableWords rg)) (mk v F) (28*D+29)
        (mk v' {S with R := Function.update S.R output ys}) := by
  simpa only [loadedSeed,Nat.add_assoc] using retireInputTable_exec_within body rg hinj
    (seedSources globals zero) D (sourceValue value zero) output hoff ys v S hblank depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
