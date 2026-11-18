module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearSem
public import IntegerMultBounds.Machine.Branch

/-! The two tape programs for the sign left by fallback elimination. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.M8
open AtomSegment AtomBank ActualAffineScaling
variable {n f b W : ℕ}
local instance : NeZero (modulus b) := ⟨(modulus_pos b).ne'⟩

def negateAnchor (n : ℕ) : SOp (n+1) :=
  ⟨.scale 0 (-1), Stage2Machine.ShearSem.neg_one_occurs⟩

def anchorOps (n : ℕ) (negative : Bool) : List (SOp (n+1)) :=
  if negative then [negateAnchor n] else []

def anchorSlots (n : ℕ) := 2 + len (negateAnchor n).1

theorem anchorFits (negative : Bool) (s : SOp (n+1)) (h : s ∈ anchorOps n negative) :
    len s.1 ≤ anchorSlots n := by
  cases negative <;> simp [anchorOps] at h
  subst s
  simp [anchorSlots]

def anchorProgram (n : ℕ) (negative : Bool) :=
  chain (anchorSlots n) (by simp [anchorSlots]) (anchorOps n negative) (anchorFits negative)

/-- Both branches share the same tape layout. The transition table is independent of the
number of atoms per field, the prime-power exponent and the trailing record width. -/
theorem anchorProgram_runs (negative : Bool) (hf : 0 < f) (hb : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array ((n+1)*f) b W) :
    ∃ a' : FlatCoordinateStages.Array ((n+1)*f) b W,
      HoareTime (anchorProgram n negative).2
        (fun v => v = outer (anchorSlots n) (neutral b W) (arrTape a) f)
        (fun v => v = outer (anchorSlots n) (neutral b W) (arrTape a') f)
        (chainConst (anchorOps n negative) * f * ((modulus b)^((n+1)*f)*W)) ∧
      ∀ (x : Fin (n+1) → Fin f → ZMod (modulus b)) (j : Fin W),
        a' (FlatCoordinateLayout.index (AtomOps.refine
          (Fin.cons (fun k => if negative then -x 0 k else x 0 k) (fun i => x i.succ))) j) =
          a (FlatCoordinateLayout.index (AtomOps.refine x) j) := by
  obtain ⟨a',run,transport⟩ := chain_hoare (P := anchorSlots n) (by simp [anchorSlots]) hf hb hW
    (anchorOps n negative) (anchorFits negative) a
  refine ⟨a',run,?_⟩
  intro x j
  have act := transport (AtomOps.refine x) j
  rw [AtomOps.refined_atomRun] at act
  · convert act using 4
    funext i k
    induction i using Fin.cases <;> cases negative <;>
      simp [anchorOps,negateAnchor,AtomOps.atomRun,AtomOps.atomExecute,mapOp,ratMod_neg_one]
  · cases negative <;> simp [anchorOps,negateAnchor,mapOp,AtomOps.Distinct]

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Read the sign at the current head of a caller tape. Both branches preserve the caller frame. -/
def anchorDispatch {T : ℕ} (n : ℕ) (sign : Fin T) :=
  branch (fun sy => sy (Fin.natAdd (22 + anchorSlots n) sign) == bitSymbol true)
    (extend (anchorProgram n true).2 T) (extend (anchorProgram n false).2 T)

theorem anchorDispatch_runs {T : ℕ} (caller : Tapes T prime) (sign : Fin T) (negative : Bool)
    (hs : caller.reads sign = bitSymbol negative) (hf : 0 < f) (hb : 0 < b) (hW : 0 < W)
    (a : FlatCoordinateStages.Array ((n+1)*f) b W) :
    ∃ a' : FlatCoordinateStages.Array ((n+1)*f) b W,
      HoareTime (anchorDispatch n sign)
        (fun v => v = (outer (anchorSlots n) (neutral b W) (arrTape a) f).append caller)
        (fun v => v = (outer (anchorSlots n) (neutral b W) (arrTape a') f).append caller)
        (chainConst (anchorOps n negative) * f * ((modulus b)^((n+1)*f)*W) + 1) ∧
      ∀ (x : Fin (n+1) → Fin f → ZMod (modulus b)) (j : Fin W),
        a' (FlatCoordinateLayout.index (AtomOps.refine
          (Fin.cons (fun k => if negative then -x 0 k else x 0 k) (fun i => x i.succ))) j) =
          a (FlatCoordinateLayout.index (AtomOps.refine x) j) := by
  obtain ⟨a',run,action⟩ := anchorProgram_runs negative hf hb hW a
  refine ⟨a',?_,action⟩
  have read (v : Tapes (22 + anchorSlots n) prime) :
      ((v.append caller).reads (Fin.natAdd _ sign) == bitSymbol true) = negative := by
    simp only [Tapes.reads,Tapes.append,Fin.addCases_right]
    change (caller.reads sign == bitSymbol true) = negative
    rw [hs]
    cases negative <;> rfl
  let cost := chainConst (anchorOps n negative) * f * ((modulus b)^((n+1)*f)*W)
  change HoareTime _ _ _ (cost + 1)
  rw [← Nat.max_self cost]
  apply branch_hoare
  all_goals
    rintro v ⟨rfl,test⟩
    rw [read] at test
    subst negative
    obtain ⟨k,c,hk,hr,hh,small,e,fr⟩ := (run.extend caller) _ ⟨_,rfl,rfl⟩
    exact ⟨k,c,hk,hr,hh,e ▸ fr⟩

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
