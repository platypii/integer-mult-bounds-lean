import IntegerMultBounds.Machine.OneHotCount

/-! Initialize both finite residue banks used by scaling from the supplied
binary modulus. Control cells need no prepared symbols. The modulus-sized loop
has a charged linear cost, while descriptor and clock return unchanged. -/
namespace IntegerMultBounds.Machine.ScalingControlInit

variable {c : ℕ}
open CountedCopyReuse (empty binary)

def initialProgram (hc : 0 < c) : Program (c+c) 2 0 where
  tapes_pos := by omega
  start := 0
  transition := fun state _ => if state = 0 then
    some (1,Fin.addCases
      (fun i => (OneHot.symbol (OneHot.residue hc 0) i,Move.stay))
      (fun i => (OneHot.symbol (OneHot.residue hc 0) i,Move.stay))) else none

def pair (hc : 0 < c) (modulus current : Tapes c 0) (n : ℕ) : Tapes (c+c) 0 :=
  (OneHot.bank modulus (OneHot.residue hc n)).append
    (OneHot.bank current (OneHot.residue hc 0))

theorem initial_exact (hc : 0 < c) (modulus current : Tapes c 0) :
    Placement.ExactRun (initialProgram hc) 1 (modulus.append current) (pair hc modulus current 0) := by
  refine ⟨⟨1,(pair hc modulus current 0).head,(pair hc modulus current 0).tape⟩,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,initialProgram,Tapes.start,ite_true,pair,Tapes.append,OneHot.bank]
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases with
      | left i => simp only [Fin.addCases_left,Move.offset,add_zero]
      | right i => simp only [Fin.addCases_right,Move.offset,add_zero]
    · funext i z
      induction i using Fin.addCases with
      | left i => simp only [Fin.addCases_left,Function.update_apply]
      | right i => simp only [Fin.addCases_right,Function.update_apply]
  · simp [step,initialProgram]

private theorem initial_hoare (hc : 0 < c) (modulus current : Tapes c 0) :
    HoareTime (initialProgram hc) (fun w => w = modulus.append current)
      (fun w => w = pair hc modulus current 0) 1 := by
  rintro w rfl
  obtain ⟨last,hr,hh,hf⟩ := initial_exact hc modulus current
  exact ⟨1,last,le_rfl,hr,hh,hf⟩

def program (hc : 0 < c) : Program (c+c+2) 20 0 :=
  seq (extend (initialProgram hc) 2)
    (CountedLoopReuse.program (extend (OneHot.program hc) c))

theorem init_hoare (hc : 0 < c) (modulus current : Tapes c 0) (bs : List Bool)
    (N : ℕ) (hcount : Counter.value bs = N) :
    HoareTime (program hc)
      (fun w => w = CountedLoopReuse.bank (modulus.append current) empty (binary bs) 1 1)
      (fun w => w = CountedLoopReuse.bank (pair hc modulus current N) empty (binary bs) 1 1)
      (7*N+7*bs.length+18) := by
  have hi := (initial_hoare hc modulus current).extend (CountedLoopReuse.controls empty (binary bs) 1 1)
  have hi' : HoareTime (extend (initialProgram hc) 2)
      (fun w => w = CountedLoopReuse.bank (modulus.append current) empty (binary bs) 1 1)
      (fun w => w = CountedLoopReuse.bank (pair hc modulus current 0) empty (binary bs) 1 1) 1 := by
    apply hi.consequence _ _ le_rfl
    · intro w hw; exact ⟨_,rfl,hw⟩
    · rintro w ⟨small,rfl,hw⟩; exact hw
  have hb : ∀ i < N, HoareTime (extend (OneHot.program hc) c)
      (fun w => w = pair hc modulus current i)
      (fun w => w = pair hc modulus current (i+1)) 1 := by
    intro i _
    have h := (OneHot.advance_hoare hc modulus (OneHot.residue hc i)).extend
      (OneHot.bank current (OneHot.residue hc 0))
    apply h.consequence _ _ le_rfl
    · intro w hw; exact ⟨_,rfl,hw⟩
    · rintro w ⟨small,rfl,hw⟩
      simpa only [OneHot.next_residue,pair] using hw
  have hl := CountedLoopReuse.loop_hoare (extend (OneHot.program hc) c) bs N
    (pair hc modulus current) (fun _ => 1) hcount hb
  apply (hi'.seq hl).consequence (fun _ h => h) (fun _ h => h)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  omega

theorem init_hoare_linear (hc : 0 < c) (modulus current : Tapes c 0) (bs : List Bool)
    (N : ℕ) (hcount : Counter.value bs = N) (hcanonical : GrowingCounterData.Canonical bs) :
    HoareTime (program hc)
      (fun w => w = CountedLoopReuse.bank (modulus.append current) empty (binary bs) 1 1)
      (fun w => w = CountedLoopReuse.bank (pair hc modulus current N) empty (binary bs) 1 1)
      (14*N+25) := by
  have hw := GrowingCounterData.canonical_width bs hcanonical
  have hl := Nat.log2_le_self (Counter.value bs)
  exact (init_hoare hc modulus current bs N hcount).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.ScalingControlInit
