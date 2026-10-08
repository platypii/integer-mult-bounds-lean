import IntegerMultBounds.Machine.OneHot
import IntegerMultBounds.Machine.CountedLoopReuse
import IntegerMultBounds.Machine.GrowingCounterData

/-! A literal unary-time initializer of fixed-modulus one-hot control from an
immutable binary count. One transition writes residue zero; a reusable counted
loop advances exactly the supplied count. All unrelated cells and all heads
are preserved, and both descriptor controls are restored. -/

namespace IntegerMultBounds.Machine.OneHotCount

variable {c : ℕ}
open CountedCopyReuse (empty binary)

/-- Write residue zero on the current cells, moving no head. -/
def initialProgram (hc : 0 < c) : Program c 2 0 where
  tapes_pos := hc
  start := 0
  transition := fun state _ => if state = 0 then
    some (1,fun i => (OneHot.symbol (OneHot.residue hc 0) i,Move.stay)) else none

theorem initialProgram_exact (hc : 0 < c) (v : Tapes c 0) :
    Placement.ExactRun (initialProgram hc) 1 v (OneHot.bank v (OneHot.residue hc 0)) := by
  refine ⟨OneHot.cfg (OneHot.bank v (OneHot.residue hc 0)) 1,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,initialProgram,Tapes.start,ite_true,Move.offset,add_zero,OneHot.cfg,OneHot.bank]
    congr 1
    congr 1
    funext i j
    by_cases hj : j = v.head i <;> simp [hj]
  · simp [step,initialProgram,OneHot.cfg]

theorem initialProgram_hoare (hc : 0 < c) (v : Tapes c 0) :
    HoareTime (initialProgram hc) (fun w => w = v)
      (fun w => w = OneHot.bank v (OneHot.residue hc 0)) 1 := by
  intro w hw
  subst w
  obtain ⟨last,hr,hh,hf⟩ := initialProgram_exact hc v
  exact ⟨1,last,le_rfl,hr,hh,hf⟩

private theorem framed_initialProgram (hc : 0 < c) (v : Tapes c 0) (bs : List Bool) :
    HoareTime (extend (initialProgram hc) 2)
      (fun w => w = CountedLoopReuse.bank v empty (binary bs) 1 1)
      (fun w => w = CountedLoopReuse.bank (OneHot.bank v (OneHot.residue hc 0)) empty (binary bs) 1 1) 1 := by
  have h := (initialProgram_hoare hc v).extend (CountedLoopReuse.controls empty (binary bs) 1 1)
  apply h.consequence _ _ le_rfl
  · intro w hw
    exact ⟨v,rfl,hw⟩
  · rintro w ⟨small,rfl,hw⟩
    exact hw

/-- Fixed finite program: initialization followed by reusable counted increments. -/
def program (hc : 0 < c) : Program (c+2) 20 0 :=
  seq (extend (initialProgram hc) 2) (CountedLoopReuse.program (OneHot.program hc))

/-- From any control-cell contents, construct N modulo the fixed c. Binary
control preparation, all joins, countdown and clock cleanup are charged. -/
theorem count_hoare (hc : 0 < c) (v : Tapes c 0) (bs : List Bool) (N : ℕ)
    (hcount : Counter.value bs = N) :
    HoareTime (program hc)
      (fun w => w = CountedLoopReuse.bank v empty (binary bs) 1 1)
      (fun w => w = CountedLoopReuse.bank (OneHot.bank v (OneHot.residue hc N)) empty (binary bs) 1 1)
      (7*N+7*bs.length+18) := by
  have hloop := CountedLoopReuse.loop_hoare (OneHot.program hc) bs N
    (fun n => OneHot.bank v (OneHot.residue hc n)) (fun _ => 1) hcount
    (by intro i _; simpa only [OneHot.next_residue] using OneHot.advance_hoare hc v (OneHot.residue hc i))
  have h := (framed_initialProgram hc v bs).seq hloop
  apply h.consequence (fun _ hw => hw) (fun _ hw => hw) _
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  omega

/-- Canonical count data gives a linear bound with no positivity requirement
on N. In particular an empty descriptor correctly constructs residue zero. -/
theorem count_hoare_linear (hc : 0 < c) (v : Tapes c 0) (bs : List Bool) (N : ℕ)
    (hcount : Counter.value bs = N) (hcanonical : GrowingCounterData.Canonical bs) :
    HoareTime (program hc)
      (fun w => w = CountedLoopReuse.bank v empty (binary bs) 1 1)
      (fun w => w = CountedLoopReuse.bank (OneHot.bank v (OneHot.residue hc N)) empty (binary bs) 1 1)
      (14*N+25) := by
  apply (count_hoare hc v bs N hcount).consequence (fun _ hw => hw) (fun _ hw => hw)
  have hw := GrowingCounterData.canonical_width bs hcanonical
  have hl := Nat.log2_le_self (Counter.value bs)
  rw [hcount] at hw hl
  omega

end IntegerMultBounds.Machine.OneHotCount
