import IntegerMultBounds.Machine.RadixLinearCombinationShared

/-! First-use preparation from genuinely blank scratch. Every persistent leaf
sentinel is physically installed before shared-source refresh and computation. -/
namespace IntegerMultBounds.Machine.RadixLinearCombinationBootstrap

open RadixLinearCombinationRefresh (Expr Size controls leaves)
open MarkedWordCleanup (one word)
variable {c q : ℕ}

def empty (t : ℕ) : Tapes t q := ⟨fun _ => 0,fun _ _ => blank⟩

private theorem empty_append (s t : ℕ) : (empty s).append (empty t) = (empty (s+t) : Tapes (s+t) q) := by
  unfold empty Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

private theorem flip_active {s t : ℕ} (v : Tapes s q) (w : Tapes t q) :
    Placement.active (finAddFlip : Fin (t+s) ≃ Fin (s+t)) (v.append w) = w := by
  cases w
  simp [Placement.active,Tapes.append,finAddFlip_apply_castAdd]

private theorem flip_extra {s t : ℕ} (v : Tapes s q) (w : Tapes t q) :
    Placement.extra (finAddFlip : Fin (t+s) ≃ Fin (s+t)) (v.append w) = v := by
  cases v
  simp [Placement.extra,Tapes.append,finAddFlip_apply_natAdd]

def InitStates : Expr c → ℕ
  | .term _ _ => 2
  | .add l r => InitStates l+InitStates r

/-- Create one actual marker on each leaf source, leaving every result blank. -/
def initProgram : (e : Expr c) → Program (Size e) (InitStates e) q
  | .term _ _ => Placement.placed (u := 1) MarkedWordCleanup.markProgram (Equiv.swap 0 1)
  | .add l r => Placement.placed (u := 1)
      (FamilyPlacementAlphabet.sequence (initProgram l) (initProgram r))
      (finAddFlip : Fin ((Size l+Size r)+1) ≃ Fin (1+(Size l+Size r)))

def initCost : Expr c → ℕ
  | .term _ _ => 1
  | .add l r => initCost l+initCost r+1

theorem init_hoare (e : Expr c) :
    HoareTime (initProgram (q := q) e) (fun v => v = empty (Size e))
      (fun v => v = RadixLinearCombination.bank e.erase (fun _ => []) []) (initCost e) := by
  induction e with
  | term i r =>
    let wire : Fin (1+1) ≃ Fin 2 := Equiv.swap 0 1
    have hb : Placement.active wire (empty 2) = one (word ([] : List (Fin (q+4)))) 0 := by
      unfold Placement.active empty one word putWord
      rfl
    have ha : Placement.active wire (RadixLinearCombination.bank (.term i.val r) (fun _ => []) []) =
        one (MarkedWordCleanup.marked ([] : List (Fin (q+4)))) 1 := by
      unfold Placement.active wire RadixLinearCombination.bank one Tapes.append
      congr 1 <;> funext j <;> fin_cases j <;> rfl
    have hf : Placement.extra wire (empty (q := q) 2) =
        Placement.extra wire (RadixLinearCombination.bank (.term i.val r) (fun _ => []) []) := by
      unfold Placement.extra wire empty RadixLinearCombination.bank one Tapes.append
      congr 1 <;> funext j <;> fin_cases j <;> rfl
    apply (Placement.hoare_at (MarkedWordCleanup.mark_hoare ([] : List (Fin (q+4)))) wire (empty 2) hb).consequence
      (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    rw [Placement.replace,hf,← ha]
    exact Placement.view _ _
  | add l r hl hr =>
    have h := FamilyPlacementAlphabet.sequence_hoare hl hr
    rw [empty_append] at h
    let wire : Fin ((Size l+Size r)+1) ≃ Fin (1+(Size l+Size r)) := finAddFlip
    have hb : Placement.active wire (empty (q := q) (Size (.add l r))) = empty (Size l+Size r) := rfl
    have ha : Placement.active wire (RadixLinearCombination.bank (q := q) (.add l.erase r.erase) (fun _ => []) []) =
        (RadixLinearCombination.bank l.erase (fun _ => []) []).append
          (RadixLinearCombination.bank r.erase (fun _ => []) []) := by
      exact flip_active (one (word []) 0) _
    have hf : Placement.extra wire (empty (q := q) (Size (.add l r))) =
        Placement.extra wire (RadixLinearCombination.bank (.add l.erase r.erase) (fun _ => []) []) := by
      have hf' := flip_extra (one (word ([] : List (Fin (q+4)))) 0)
        ((RadixLinearCombination.bank l.erase (fun _ => []) []).append (RadixLinearCombination.bank r.erase (fun _ => []) []))
      exact hf'.symm
    apply (Placement.hoare_at h wire (empty (Size (.add l r))) hb).consequence (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    exact (congrArg₂ (Placement.combine wire) ha.symm hf).trans
      (Placement.view wire (RadixLinearCombination.bank (.add l.erase r.erase) (fun _ => []) []))

theorem initCost_eq (e : Expr c) : initCost e+1 = 2*leaves e := by
  induction e with
  | term => rfl
  | add l r hl hr => simp only [initCost,leaves]; omega

abbrev TapeCount (e : Expr c) := RadixLinearCombinationShared.TapeCount e

/-- Only the physical control bank is supplied; every other tape is blank. -/
def input (e : Expr c) (xs : ℕ → List (Fin q)) : Tapes (TapeCount e) q :=
  (controls xs).append (empty (RadixLinearCombinationBinary.TapeCount e.erase))

private def initializeProgram (e : Expr c) : Program (TapeCount e) (InitStates e) q :=
  Placement.placed (Placement.placed (initProgram e) (RadixLinearCombinationBinary.arithmeticPlacement e.erase))
    (finAddFlip : Fin (RadixLinearCombinationBinary.TapeCount e.erase+c) ≃ Fin (TapeCount e))

private theorem initialize_hoare (e : Expr c) (xs : ℕ → List (Fin q)) :
    HoareTime (initializeProgram e) (fun v => v = input e xs)
      (fun v => v = RadixLinearCombinationShared.input e xs (fun _ => [])) (initCost e) := by
  let inner := RadixLinearCombinationBinary.arithmeticPlacement e.erase
  let target := RadixLinearCombinationBinary.input e.erase (fun _ => ([] : List (Fin q)))
  have hb : Placement.active inner (empty (q := q) (RadixLinearCombinationBinary.TapeCount e.erase)) = empty (Size e) := rfl
  have ha : Placement.active inner target = RadixLinearCombination.bank e.erase (fun _ => []) [] := by
    rw [RadixLinearCombination.bank_split]
    unfold Placement.active inner target RadixLinearCombinationBinary.arithmeticPlacement
      RadixLinearCombinationBinary.input RadixLinearCombinationBinary.bank
    congr 1 <;> funext i <;> induction i using Fin.addCases with
    | left i => fin_cases i; simp [Tapes.append,one]
    | right i => simp [Tapes.append]
  have hf : Placement.extra inner (empty (RadixLinearCombinationBinary.TapeCount e.erase)) = Placement.extra inner target := by
    unfold Placement.extra inner target empty RadixLinearCombinationBinary.arithmeticPlacement
      RadixLinearCombinationBinary.input RadixLinearCombinationBinary.bank
    congr 1 <;> funext i <;> fin_cases i <;> simp [Tapes.append]
  have h : HoareTime (Placement.placed (initProgram e) inner)
      (fun v => v = empty (RadixLinearCombinationBinary.TapeCount e.erase)) (fun v => v = target) (initCost e) := by
    apply (Placement.hoare_at (init_hoare e) inner _ hb).consequence (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    rw [Placement.replace,hf,← ha]
    exact Placement.view _ _
  let wire : Fin (RadixLinearCombinationBinary.TapeCount e.erase+c) ≃ Fin (TapeCount e) := finAddFlip
  have hb' : Placement.active wire (input e xs) = empty (RadixLinearCombinationBinary.TapeCount e.erase) := by
    unfold Placement.active wire input
    congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl
  have ha' : Placement.active wire (RadixLinearCombinationShared.input e xs (fun _ => [])) = target := by
    unfold Placement.active wire RadixLinearCombinationShared.input
    congr 1 <;> funext i <;> simp [Tapes.append] <;> rfl
  have hf' : Placement.extra wire (input e xs) = Placement.extra wire (RadixLinearCombinationShared.input e xs (fun _ => [])) := by
    unfold Placement.extra wire input RadixLinearCombinationShared.input
    congr 1 <;> funext i <;> simp [Tapes.append]
  apply (Placement.hoare_at h wire _ hb').consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,hf',← ha']
  exact Placement.view _ _

variable [Fact q.Prime]

abbrev States (e : Expr c) := InitStates e+RadixLinearCombinationShared.States e

def program (e : Expr c) : Program (TapeCount e) (States e) q :=
  seq (initializeProgram e) (RadixLinearCombinationShared.program e)

/-- First-use, actual control-to-binary preparation, including every marker write. -/
theorem compute_hoare (e : Expr c) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i, (xs i).length = b) :
    HoareTime (program e) (fun v => v = input e xs)
      (fun v => v = RadixLinearCombinationShared.output e xs)
      ((15*leaves e+RadixLinearCombination.linearConstant e.erase+40)*q^b) := by
  have hh := (initialize_hoare e xs).seq (RadixLinearCombinationShared.compute_hoare_linear e xs (fun _ => []) b hw
    (fun _ => Nat.zero_le _))
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  have hp : 1 ≤ q^b := Nat.one_le_pow _ _ (by have := (Fact.out : q.Prime).two_le; omega)
  have hc := initCost_eq e
  nlinarith

theorem compute_finite_hoare (e : Expr c) (seed : Fin c) (xs : Fin c → List (Fin q)) (b : ℕ)
    (hw : ∀ i, (xs i).length = b) :
    HoareTime (program e) (fun v => v = input e (RadixLinearCombinationShared.read seed xs))
      (fun v => v = RadixLinearCombinationShared.output e (RadixLinearCombinationShared.read seed xs))
      ((15*leaves e+RadixLinearCombination.linearConstant e.erase+40)*q^b) :=
  compute_hoare e _ b (RadixLinearCombinationShared.read_width seed xs b hw)

end IntegerMultBounds.Machine.RadixLinearCombinationBootstrap
