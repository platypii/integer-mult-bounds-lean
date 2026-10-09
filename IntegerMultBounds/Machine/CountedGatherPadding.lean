import IntegerMultBounds.Machine.Gather
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.GrowingCounterData

/-! Fixed finite-control gather padding and source seeking. The runtime count
is read from one retained binary descriptor; a separate marked-empty clock is
copied, decremented and restored. Counts never parameterize a program. -/
namespace IntegerMultBounds.Machine.CountedGatherPadding
variable {a : ℕ}

/-- Source, control, target, reusable marked-empty clock, retained count. -/
def bank (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (bs : List Bool) : Tapes 5 a :=
  CountedLoopReuseAlphabet.bank (Gather.bank f g h px pz pt)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1

def seekRightProgram (a : ℕ) : Program 5 18 a :=
  CountedLoopReuseAlphabet.program (Gather.skipX a)
def leftStep (a : ℕ) : Program 3 2 a := extend (StepLeft.program (a := a)) 2
def seekLeftProgram (a : ℕ) : Program 5 18 a :=
  CountedLoopReuseAlphabet.program (leftStep a)
def zerosProgram (a : ℕ) : Program 5 18 a :=
  CountedLoopReuseAlphabet.program (Gather.zeroT a)

def cost (n : ℕ) (bs : List Bool) := 7*n+7*bs.length+16

private theorem left_step (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) :
    HoareTime (leftStep a) (fun v => v = Gather.bank f g h px pz pt)
      (fun v => v = Gather.bank f g h (px-1) pz pt) 1 := by
  have hv := hoare_extend_eq (StepLeft.step_hoare (a := a) f px)
    (⟨fun i => if i = 0 then pz else pt,fun i => if i = 0 then g else h⟩ : Tapes 2 a)
  change HoareTime (leftStep a)
    (fun v => v = (StepRight.cfg f px 0).tapes.append
      (⟨fun i => if i = 0 then pz else pt,fun i => if i = 0 then g else h⟩ : Tapes 2 a))
    (fun v => v = (StepRight.cfg f (px-1) 0).tapes.append
      (⟨fun i => if i = 0 then pz else pt,fun i => if i = 0 then g else h⟩ : Tapes 2 a)) 1 at hv
  rwa [Gather.x_bank,Gather.x_bank] at hv

/-- Seeking right preserves every cell, both spectator heads and both controls. -/
theorem seekRight_hoare (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) :
    HoareTime (seekRightProgram a) (fun v => v = bank f g h px pz pt bs)
      (fun v => v = bank f g h (px+n) pz pt bs) (cost n bs) := by
  have hv := CountedLoopReuseAlphabet.loop_hoare (Gather.skipX a) bs n
    (fun i => Gather.bank f g h (px+i) pz pt) (fun _ => 1) hn (by
      intro i _
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using Gather.skipX_hoare f g h (px+i) pz pt)
  simpa [seekRightProgram,bank,cost,Finset.sum_const,Finset.card_range,Nat.mul_one,
    show n+6*n=7*n by omega] using hv

/-- Seeking left also accepts zero, and makes no assumptions about the cells
crossed or about the initial source-head coordinate. -/
theorem seekLeft_hoare (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) :
    HoareTime (seekLeftProgram a) (fun v => v = bank f g h px pz pt bs)
      (fun v => v = bank f g h (px-n) pz pt bs) (cost n bs) := by
  have hv := CountedLoopReuseAlphabet.loop_hoare (leftStep a) bs n
    (fun i => Gather.bank f g h (px-i) pz pt) (fun _ => 1) hn (by
      intro i _
      have hh := left_step f g h (px-i) pz pt
      simpa only [Nat.cast_add,Nat.cast_one,sub_sub] using hh)
  simpa [seekLeftProgram,bank,cost,Finset.sum_const,Finset.card_range,Nat.mul_one,
    show n+6*n=7*n by omega] using hv

private theorem zeros_succ (h : ℤ → Fin (a+4)) (pt : ℤ) (i : ℕ) :
    Function.update (putWord h pt ((List.replicate i false).map bitSymbol)) (pt+i) (bitSymbol false) =
      putWord h pt ((List.replicate (i+1) false).map bitSymbol) := by
  have hh := Gather.putWord_snoc h pt ((List.replicate i false).map bitSymbol) (bitSymbol false)
  simpa [List.map_replicate,List.length_replicate,List.replicate_succ'] using hh

/-- Write precisely n false symbols from the target head, retaining the
arbitrary target exterior and both source/control tapes. -/
theorem zeros_hoare (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) :
    HoareTime (zerosProgram a) (fun v => v = bank f g h px pz pt bs)
      (fun v => v = bank f g (putWord h pt ((List.replicate n false).map bitSymbol)) px pz (pt+n) bs)
      (cost n bs) := by
  have hv := CountedLoopReuseAlphabet.loop_hoare (Gather.zeroT a) bs n
    (fun i => Gather.bank f g (putWord h pt ((List.replicate i false).map bitSymbol)) px pz (pt+i))
    (fun _ => 1) hn (by
      intro i _
      have hh := Gather.zeroT_hoare f g (putWord h pt ((List.replicate i false).map bitSymbol)) px pz (pt+i)
      rw [zeros_succ] at hh
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using hh)
  simpa [zerosProgram,bank,cost,Finset.sum_const,Finset.card_range,Nat.mul_one,
    show n+6*n=7*n by omega,putWord] using hv

theorem cost_affine (n : ℕ) (bs : List Bool) (hn : Counter.value bs = n)
    (hc : GrowingCounterData.Canonical bs) : cost n bs ≤ 14*n+23 := by
  have hl := (GrowingCounterData.canonical_width bs hc).trans
    (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  rw [hn] at hl
  unfold cost
  omega

/-- Canonical counts give a uniform linear bound, including n = 0. -/
theorem cost_linear (n : ℕ) (bs : List Bool) (hn : Counter.value bs = n)
    (hc : GrowingCounterData.Canonical bs) : cost n bs ≤ 37*max 1 n := by
  have hl := (GrowingCounterData.canonical_width bs hc).trans
    (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  rw [hn] at hl
  have h1 := le_max_left 1 n
  have h2 := le_max_right 1 n
  unfold cost
  omega

theorem seekRight_linear (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hc : GrowingCounterData.Canonical bs) :
    HoareTime (seekRightProgram a) (fun v => v = bank f g h px pz pt bs)
      (fun v => v = bank f g h (px+n) pz pt bs) (37*max 1 n) :=
  (seekRight_hoare f g h px pz pt bs n hn).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear n bs hn hc)

theorem seekLeft_linear (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hc : GrowingCounterData.Canonical bs) :
    HoareTime (seekLeftProgram a) (fun v => v = bank f g h px pz pt bs)
      (fun v => v = bank f g h (px-n) pz pt bs) (37*max 1 n) :=
  (seekLeft_hoare f g h px pz pt bs n hn).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear n bs hn hc)

theorem zeros_linear (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ)
    (bs : List Bool) (n : ℕ) (hn : Counter.value bs = n) (hc : GrowingCounterData.Canonical bs) :
    HoareTime (zerosProgram a) (fun v => v = bank f g h px pz pt bs)
      (fun v => v = bank f g (putWord h pt ((List.replicate n false).map bitSymbol)) px pz (pt+n) bs)
      (37*max 1 n) :=
  (zeros_hoare f g h px pz pt bs n hn).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear n bs hn hc)

end IntegerMultBounds.Machine.CountedGatherPadding
