module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleRunSpace
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleCost
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePadSpace
public import IntegerMultBounds.Machine.RunInvariantComposition

/-! Workspace of a complete atom operation, including installed position counters
and their erasure. All parked banks have heads in [0,1]. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleRun
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewFrameRoleBank (count)
open FlatCoordinateSchedule (bits)
open AtomRoleLoop (levelBank datas)
open AtomRolePlan (kind Fits)
open AtomRoleInstall (fAux rest target)
open AtomStep (words)
noncomputable section
variable {t m f : ℕ}

/-- Canonical parked heads depend on neither data nor binary word contents. -/
theorem levelBank_heads (T : ℕ) {v : Descriptor} (hs : Fin 6 → List Bool)
    (data : RecursiveViewedAction.Data t v) (ws : Fin 5 → List Bool) (f : ℕ) :
    ∀ i, 0 ≤ (levelBank T hs (fAux f) data ws).head i ∧
      (levelBank T hs (fAux f) data ws).head i ≤ 1 := by
  have ha {s u : ℕ} (x : Tapes s prime) (y : Tapes u prime)
      (hx : ∀ i, 0 ≤ x.head i ∧ x.head i ≤ 1)
      (hy : ∀ i, 0 ≤ y.head i ∧ y.head i ≤ 1) :
      ∀ i, 0 ≤ (x.append y).head i ∧ (x.append y).head i ≤ 1 := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa only [Tapes.append,Fin.addCases_left] using hx i
    | right i => simpa only [Tapes.append,Fin.addCases_right] using hy i
  have he : ∀ i, 0 ≤ (SharedBank.empty 1 prime).head i ∧
      (SharedBank.empty 1 prime).head i ≤ 1 := by intro i; simp [SharedBank.empty]
  have hc := ha (RecursiveRoleSerialization.roles data)
    (((SharedBank.empty 1 prime).append (RecursiveShiftRoleBank.headers hs)).append
      ((SharedBank.empty 1 prime).append ((AtomView.counters ws).append (fAux f))))
    (by intro i; simp [RecursiveRoleSerialization.roles])
    (ha _ _ (ha _ _ he (by intro i; simp [RecursiveShiftRoleBank.headers]))
      (ha _ _ he (ha _ _ (by intro i; simp [AtomView.counters])
        (by intro i; simp only [fAux]; split_ifs <;> omega))))
  intro i
  dsimp only [levelBank,SharedBankStageInput.raw]
  split
  · exact hc _
  · simp

/-- The reusable loop controls are parked at one as well. -/
theorem loopBank_heads (T : ℕ) {v : Descriptor} (hs : Fin 6 → List Bool) (f : ℕ)
    (d : RecursiveViewedAction.Data t v) (ws : Fin 5 → List Bool) :
    ∀ i, 0 ≤ (LevelLoop.bank (levelBank T hs (fAux f) d ws) f).head i ∧
      (LevelLoop.bank (levelBank T hs (fAux f) d ws) f).head i ≤ 1 := by
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [LevelLoop.bank,CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_left] using levelBank_heads T hs d ws f i
  | right i => simp [LevelLoop.bank,CountedLoopReuseAlphabet.bank,Tapes.append,CountedLoopReuseAlphabet.controls]

/-- One operation's workspace budget contains one refined stage, setup and erasure. -/
def operationSpace (f : ℕ) (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ)
    (hop : Fits m op) (wire : Fin t) (V : ℕ) : ℕ :=
  AtomRoleInstall.setupCost f (plan op) +
    (AtomStepCost.constant (AtomRolePlan.act wire op hop) * V + 1 + AtomRoleSteps.stepCost (m*f) +
      3*(bits (f-1)).length+8) +
    AtomRoleInstall.eraseCost (vals ((kind hf op hop).sel (f-1)))

/-- The complete workspace allowance is linear in active volume, without a level factor. -/
theorem operationSpace_le {b : ℕ} (hb0 : 0 < b) (hf : 0 < f)
    (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (wire : Fin t)
    (v : Descriptor) (hw : v.width = (m*f)*b) (hp : v.Positive) :
    operationSpace f hf op hop wire (volume prime v) ≤
      AtomRoleCost.opConst m (AtomRolePlan.act wire op hop) * volume prime v := by
  have hV := AtomRoleCost.atoms_lt_volume hb0 v hw hp
  have hm : 0 < m := by
    cases op with
    | scale i c => have := i.isLt; omega
    | shift i j c => have := i.isLt; omega
    | revShift i j c => have := i.isLt; omega
  have hfV : f ≤ volume prime v := (Nat.le_mul_of_pos_left f hm).trans hV.le
  have hb := CounterSteps.bits_length (f-1)
  have hs := AtomRoleCost.setupCost_le hf op
  have he := AtomRoleCost.eraseCost_le ((kind hf op hop).sel (f-1))
  have hS := Nat.mul_le_mul_left (32*(m+1)^2+600*(m+1)) hfV
  unfold operationSpace AtomRoleCost.opConst AtomRoleSteps.stepCost
  rw [show (AtomStepCost.constant (AtomRolePlan.act wire op hop) + 32*(m+1)^2 + 600*(m+1) + 550) * volume prime v =
    AtomStepCost.constant (AtomRolePlan.act wire op hop) * volume prime v +
      (32*(m+1)^2+600*(m+1))*volume prime v + 550*volume prime v by ring]
  omega

theorem operation_heads {b : ℕ} (hb0 : 0 < b) (T : ℕ) (hf : 0 < f)
    (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (wire : Fin t)
    (hle : ftapes (opForm op hop) (AtomRolePlan.act wire op hop) ≤ T)
    (v : Descriptor) (hw : v.width = (m*f)*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (data : RecursiveViewedAction.Data t v)
    {c} (hc : RunInvariant (opRun T op hop wire hle) (· = common T hs f b data) c) :
    ∀ i, -(operationSpace f hf op hop wire (volume prime v) : ℤ) ≤ c.head i ∧
      c.head i ≤ ((bits (f-1)).length : ℤ)+1+operationSpace f hf op hop wire (volume prime v) := by
  let act := AtomRolePlan.act wire op hop
  let K := kind hf op hop
  let B := AtomStepCost.constant act * volume prime v + 1 + AtomRoleSteps.stepCost (m*f) +
    3*(bits (f-1)).length+8
  let budget := operationSpace f hf op hop wire (volume prime v)
  let H : TapePred (T+2) prime := fun z => ∀ i,
    -(budget : ℤ) ≤ z.head i ∧ z.head i ≤ ((bits (f-1)).length : ℤ)+1+budget
  have hT := run_tapes T op hop wire hle
  change ftapes (opForm op hop) act ≤ T at hle
  have hk := ftapes_ge (opForm op hop) act
  have h1 := hoare_extend_eq
    (AtomRoleInstall.setup_hoare T hT hs data f b (plan op) (plan_dec hf op hop))
    (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary (bits (f-1))) 1 1)
  have hL := kloop_hoare hb0 K act v hw hp hs hv (fAux f) hf data
  rw [kind_form hf op hop] at hL
  have h2 := AtomRolePad.pad_hoare (k := count t (5+2)) hle (by omega) _ _ _ f hL
  rw [plan_words b hf op hop, words_target] at h2
  have h3 := hoare_extend_eq
    (AtomRoleInstall.eraseAll_hoare T hT hs (datas K.sel act v hw data f)
      f b (vals (K.sel (f-1))))
    (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary (bits (f-1))) 1 1)
  have hpark := loopBank_heads (t := t) (v := v) T hs f
  have hsetup : ∀ z, RunInvariant (extend (AtomRoleInstall.setup T hT (plan op)) 2)
      (· = common T hs f b data) z → H z.tapes := by
    intro z hz i
    have h := RunInvariant.heads_eq h1 hz i
    have hb := hpark data (rest b) i
    simp only [LevelLoop.bank,CountedLoopReuseAlphabet.bank] at hb
    change -(budget : ℤ) ≤ z.head i ∧ z.head i ≤ _
    dsimp only [budget,operationSpace] at *
    omega
  have hclean : ∀ z, RunInvariant (extend (AtomRoleInstall.eraseAll T hT) 2)
      (· = LevelLoop.bank (levelBank T hs (fAux f) (datas K.sel act v hw data f)
        (target b (vals (K.sel (f-1))))) f) z → H z.tapes := by
    intro z hz i
    have h := RunInvariant.heads_eq h3 hz i
    have hb := hpark (datas K.sel act v hw data f) (target b (vals (K.sel (f-1)))) i
    simp only [LevelLoop.bank,CountedLoopReuseAlphabet.bank] at hb
    change -(budget : ℤ) ≤ z.head i ∧ z.head i ≤ _
    dsimp only [budget,operationSpace,K] at *
    omega
  have hloop : ∀ z, RunInvariant
      (Placement.placed (fprogram (opForm op hop) act).2 (AtomRolePad.placement _ T hle))
      (· = LevelLoop.bank (levelBank T hs (fAux f) data
        (target b (fun j => AtomSegment.planValue f (plan op j)))) f) z → H z.tapes := by
    intro z hz
    obtain ⟨u,hu,n,hr⟩ := hz
    subst u
    have hsmall (x : Config (ftapes (kform K) act+2) (fprogram (kform K) act).1 prime)
        (hx : RunInvariant (fprogram (kform K) act).2
          (· = LevelLoop.bank (levelBank (ftapes (kform K) act) hs (fAux f) data (words b (K.sel 0))) f) x) :=
      kloop_heads hb0 K act v hw hp hs hv (fAux f) hf data 0 1
        (levelBank_heads _ hs data (words b (K.sel 0)) f) hx
    dsimp only [K] at hsmall
    rw [kind_form hf op hop,plan_words b hf op hop] at hsmall
    have hh := AtomRolePad.pad_heads (k := count t (5+2)) hle (by omega) _ _ f
      (-(B : ℤ)) (((bits (f-1)).length : ℤ)+1+B) ?_ ?_ hr
    · intro i
      have h := hh i
      change -(budget : ℤ) ≤ z.head i ∧ z.head i ≤ _
      dsimp only [budget,operationSpace,B,act] at *
      omega
    · intro x hx i
      have h := hsmall x hx i
      simpa only [min_self,max_eq_right (show (1 : ℤ) ≤ ((bits (f-1)).length : ℤ)+1 by omega),zero_sub] using h
    · intro i
      have h := hpark data (target b (fun j => AtomSegment.planValue f (plan op j))) i
      simp only [levelBank] at h
      dsimp only [B]
      omega
  change H c.tapes
  apply RunInvariant.seq_tapes (h1.seq h2) H ?_ hclean hc
  intro z hz
  exact RunInvariant.seq_tapes h1 H hsetup hloop hz

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleRun
