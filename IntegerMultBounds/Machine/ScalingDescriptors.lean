import IntegerMultBounds.Machine.ScalingDescriptorData
import IntegerMultBounds.Machine.GrowingCounter
import IntegerMultBounds.Machine.ScalingControlInit

/-! Literal synthesis of binary scaling-piece lengths. A fixed residue selector
chooses one growing descriptor, a reusable B-counted loop increments it, and a
Q-counted outer loop visits every output block. Carries are amortized globally. -/

namespace IntegerMultBounds.Machine.ScalingDescriptors

open CountedCopyReuse (empty binary)
open ScalingDescriptorData (descriptors)

/-- One spare tape permits fixed swap placement of any descriptor counter. -/
def counters {c : ℕ} (ds : Fin c → List Bool) : Tapes (1+c) 0 :=
  (⟨fun _ => 1,fun _ _ => blank⟩ : Tapes 1 0).append
    ⟨fun _ => 1,fun j => binary (ds j)⟩

def incrementPlacement {c : ℕ} (j : Fin c) : Fin (1+c) ≃ Fin (1+c) :=
  Equiv.swap (Fin.castAdd c (0 : Fin 1)) (Fin.natAdd 1 j)

def incrementProgram {c : ℕ} (j : Fin c) : Program (1+c) 3 0 :=
  Placement.placed GrowingCounter.program (incrementPlacement j)

@[simp] private theorem slots_ne {c : ℕ} (i : Fin 1) (j : Fin c) :
    Fin.castAdd c i ≠ Fin.natAdd 1 j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
  omega

@[simp] private theorem slots_ne' {c : ℕ} (i : Fin 1) (j : Fin c) :
    Fin.natAdd 1 j ≠ Fin.castAdd c i := Ne.symm (slots_ne i j)

private theorem active_counters {c : ℕ} (ds : Fin c → List Bool) (j : Fin c) :
    Placement.active (incrementPlacement j) (counters ds) = GrowingCounter.tapes empty (ds j) := by
  unfold Placement.active counters incrementPlacement GrowingCounter.tapes
  congr 1 <;> funext i <;> fin_cases i <;> simp [Tapes.append,binary]

private theorem replace_counters {c : ℕ} (ds : Fin c → List Bool) (j : Fin c) (bs : List Bool) :
    Placement.replace (incrementPlacement j) (counters ds) (GrowingCounter.tapes empty bs) =
      counters (Function.update ds j bs) := by
  unfold Placement.replace Placement.combine Placement.extra counters incrementPlacement
    Tapes.reindex Tapes.append GrowingCounter.tapes
  congr 1
  · funext i
    induction i using Fin.addCases with
    | left i => fin_cases i; simp [Equiv.swap_apply_def]
    | right i => by_cases hi : i = j <;> simp [Equiv.swap_apply_def,hi]
  · funext i
    induction i using Fin.addCases with
    | left i => fin_cases i; simp [Equiv.swap_apply_def]
    | right i => by_cases hi : i = j <;> simp [Equiv.swap_apply_def,hi,binary]

theorem increment_hoare {c : ℕ} (ds : Fin c → List Bool) (j : Fin c) :
    HoareTime (incrementProgram j) (fun v => v = counters ds)
      (fun v => v = counters (Function.update ds j (GrowingCounterData.increment (ds j))))
      (2*GrowingCounterData.carrySteps (ds j)) := by
  have h := Placement.hoare_at
    (GrowingCounter.increment_hoare empty (ds j) (by simp [empty])
      (by simp [empty,show (1 : ℤ)+(ds j).length ≠ 0 by omega]))
    (incrementPlacement j) (counters ds) (active_counters ds j)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_counters _ _ _

def innerBank {c : ℕ} (ds : Fin c → List Bool) (bs : List Bool) : Tapes (1+c+2) 0 :=
  CountedLoopReuse.bank (counters ds) empty (binary bs) 1 1

def innerProgram {c : ℕ} (j : Fin c) : Program (1+c+2) 19 0 :=
  CountedLoopReuse.program (incrementProgram j)

private theorem advance_sum (n : ℕ) (bs : List Bool) :
    (∑ i ∈ Finset.range n, 2*GrowingCounterData.carrySteps (GrowingCounterData.advance i bs)) =
      GrowingCounterData.totalCost n bs := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [GrowingCounterData.advance]
    rw [ih]
    simp only [GrowingCounterData.totalCost,Nat.add_comm]

/-- A block-width batch increments one descriptor and restores its private clock. -/
theorem inner_hoare {c : ℕ} (ds : Fin c → List Bool) (j : Fin c)
    (bs : List Bool) (B : ℕ) (hcount : Counter.value bs = B) :
    HoareTime (innerProgram j) (fun v => v = innerBank ds bs)
      (fun v => v = innerBank (Function.update ds j (GrowingCounterData.advance B (ds j))) bs)
      (GrowingCounterData.totalCost B (ds j)+6*B+7*bs.length+16) := by
  have hb (i : ℕ) (_hi : i < B) : HoareTime (incrementProgram j)
      (fun v => v = counters (Function.update ds j (GrowingCounterData.advance i (ds j))))
      (fun v => v = counters (Function.update ds j (GrowingCounterData.advance (i+1) (ds j))))
      (2*GrowingCounterData.carrySteps (GrowingCounterData.advance i (ds j))) := by
    have h := increment_hoare (Function.update ds j (GrowingCounterData.advance i (ds j))) j
    simpa only [Function.update_self,Function.update_idem,ScalingDescriptorData.advance_succ_right] using h
  have h := CountedLoopReuse.loop_hoare (incrementProgram j) bs B
    (fun i => counters (Function.update ds j (GrowingCounterData.advance i (ds j))))
    (fun i => 2*GrowingCounterData.carrySteps (GrowingCounterData.advance i (ds j))) hcount hb
  simpa only [GrowingCounterData.advance,Function.update_eq_self,advance_sum,innerBank,innerProgram] using h

/-- Binary counters and B descriptor, followed by modulus/current one-hot banks. -/
def bank {c : ℕ} (ds : Fin c → List Bool) (bs : List Bool)
    (modulus current : Tapes c 0) (m z : Fin c) : Tapes (1+c+2+c+c) 0 :=
  ((innerBank ds bs).append (OneHot.bank modulus m)).append (OneHot.bank current z)

def family {c : ℕ} (j : Fin c) : Program (1+c+2+c+c) 19 0 :=
  extend (extend (innerProgram j) c) c

def selector {c : ℕ} (hc : 0 < c) (symbols : Fin (1+c+2+c+c) → Fin 4) : Fin c :=
  ScalingControl.table hc
    (OneHot.decode hc (fun i => symbols (Fin.castAdd c (Fin.natAdd (1+c+2) i))))
    (OneHot.decode hc (fun i => symbols (Fin.natAdd (1+c+2+c) i)))

private theorem selector_bank {c : ℕ} (hc : 0 < c) (ds : Fin c → List Bool)
    (bs : List Bool) (modulus current : Tapes c 0) (m z : Fin c) :
    selector hc (bank ds bs modulus current m z).reads = ScalingControl.table hc m z := by
  simp [selector,bank,Tapes.reads,Tapes.append,OneHot.decode_symbol]

def advanceProgram {c : ℕ} (hc : 0 < c) : Program (1+c+2+c+c) 2 0 :=
  Placement.placed (OneHot.program hc) (finAddFlip : Fin (c+(1+c+2+c)) ≃ Fin (1+c+2+c+c))

private theorem advance_hoare {c : ℕ} (hc : 0 < c) (v : Tapes (1+c+2+c) 0)
    (current : Tapes c 0) (z : Fin c) :
    HoareTime (advanceProgram hc)
      (fun w => w = v.append (OneHot.bank current z))
      (fun w => w = v.append (OneHot.bank current (OneHot.next hc z))) 1 := by
  let e : Fin (c+(1+c+2+c)) ≃ Fin (1+c+2+c+c) := finAddFlip
  have ha : Placement.active e (v.append (OneHot.bank current z)) = OneHot.bank current z := by
    unfold Placement.active e
    simp [Tapes.append,finAddFlip_apply_castAdd,OneHot.bank]
  have h := Placement.hoare_at (OneHot.advance_hoare hc current z) e _ ha
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  have hextra : Placement.extra e (v.append (OneHot.bank current z)) = v := by
    cases v
    simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
  rw [Placement.replace,hextra]
  have ha' : Placement.active e (v.append (OneHot.bank current (OneHot.next hc z))) =
      OneHot.bank current (OneHot.next hc z) := by
    simp [Placement.active,e,Tapes.append,finAddFlip_apply_castAdd,OneHot.bank]
  have he' : Placement.extra e (v.append (OneHot.bank current (OneHot.next hc z))) = v := by
    cases v
    simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
  simpa only [ha',he'] using Placement.view e (v.append (OneHot.bank current (OneHot.next hc z)))

private theorem family_hoare {c : ℕ} (ds : Fin c → List Bool) (j : Fin c)
    (bs : List Bool) (B : ℕ) (hcount : Counter.value bs = B)
    (modulus current : Tapes c 0) (m z : Fin c) :
    HoareTime (family j)
      (fun v => v = bank ds bs modulus current m z)
      (fun v => v = bank (Function.update ds j (GrowingCounterData.advance B (ds j))) bs modulus current m z)
      (GrowingCounterData.totalCost B (ds j)+6*B+7*bs.length+16) := by
  have h := ((inner_hoare ds j bs B hcount).extend (OneHot.bank modulus m)).extend (OneHot.bank current z)
  apply h.consequence _ _ le_rfl
  · intro v hv
    exact ⟨_,⟨_,rfl,rfl⟩,hv⟩
  · rintro v ⟨w,⟨small,rfl,rfl⟩,hv⟩
    exact hv

/-- One fixed dispatch, one B-counted increment batch, then one residue advance. -/
def body {c : ℕ} (hc : 0 < c) : Program (1+c+2+c+c) (c*19+1+2) 0 :=
  seq (Dispatch.program hc family (selector hc)) (advanceProgram hc)

theorem body_hoare {c : ℕ} (hc : 0 < c) (Q B z : ℕ) (bs : List Bool)
    (hcount : Counter.value bs = B) (modulus current : Tapes c 0) :
    HoareTime (body hc)
      (fun v => v = bank (descriptors hc Q B z) bs modulus current (OneHot.residue hc Q) (OneHot.residue hc z))
      (fun v => v = bank (descriptors hc Q B (z+1)) bs modulus current
        (OneHot.residue hc Q) (OneHot.residue hc (z+1)))
      (ScalingDescriptorData.blockCost hc Q B z+6*B+7*bs.length+19) := by
  let ds := descriptors hc Q B z
  let j := ScalingControl.select hc Q z
  have hfamily := family_hoare ds j bs B hcount modulus current (OneHot.residue hc Q) (OneHot.residue hc z)
  have hdispatch := Dispatch.hoare_at hc family (selector hc)
    (bank ds bs modulus current (OneHot.residue hc Q) (OneHot.residue hc z)) j hfamily rfl
    (selector_bank hc ds bs modulus current (OneHot.residue hc Q) (OneHot.residue hc z))
  have h := hdispatch.seq (advance_hoare hc
    ((innerBank (Function.update ds j (GrowingCounterData.advance B (ds j))) bs).append
      (OneHot.bank modulus (OneHot.residue hc Q))) current (OneHot.residue hc z))
  simp only [ds,j,ScalingDescriptorData.descriptors_step,OneHot.next_residue] at h
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) (by dsimp [ScalingDescriptorData.blockCost]; omega)

/-- Whole counted synthesis sweep, leaving its clocks and input counts reusable. -/
def sweepProgram {c : ℕ} (hc : 0 < c) : Program (1+c+2+c+c+2) (7+(c*19+1+2+5)+4) 0 :=
  CountedLoopReuse.program (body hc)

theorem sweep_hoare {c : ℕ} (hc : 0 < c) (Q B : ℕ) (bs qs : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (modulus current : Tapes c 0) :
    HoareTime (sweepProgram hc)
      (fun v => v = CountedLoopReuse.bank
        (bank (fun _ => []) bs modulus current (OneHot.residue hc Q) (OneHot.residue hc 0)) empty (binary qs) 1 1)
      (fun v => v = CountedLoopReuse.bank
        (bank (descriptors hc Q B Q) bs modulus current (OneHot.residue hc Q) (OneHot.residue hc Q)) empty (binary qs) 1 1)
      (10*(Q*B)+7*Q*bs.length+25*Q+7*qs.length+16) := by
  have h := CountedLoopReuse.loop_hoare (body hc) qs Q
    (fun z => bank (descriptors hc Q B z) bs modulus current (OneHot.residue hc Q) (OneHot.residue hc z))
    (fun z => ScalingDescriptorData.blockCost hc Q B z+6*B+7*bs.length+19) hq
    (by intro z _; exact body_hoare hc Q B z bs hb modulus current)
  simp only [ScalingDescriptorData.descriptors_zero] at h
  apply h.consequence (fun _ hv => hv) (fun _ hv => hv) _
  have ham := ScalingDescriptorData.amortized_cost hc Q B Q
  simp only [ScalingDescriptorData.totalCost] at ham
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
  nlinarith

private def controls {c : ℕ} (b : Tapes (1+c+2) 0) (modulus current : Tapes c 0)
    (outer : Tapes 2 0) : Tapes (1+c+2+c+c+2) 0 :=
  ((b.append modulus).append current).append outer

private def initTo {c : ℕ} : Fin (c+c+2) → Fin (1+c+2+c+c+2) :=
  Fin.addCases (Fin.addCases
    (fun i => Fin.castAdd 2 (Fin.castAdd c (Fin.natAdd (1+c+2) i)))
    (fun i => Fin.castAdd 2 (Fin.natAdd (1+c+2+c) i)))
    (fun i => Fin.natAdd (1+c+2+c+c) i)

private def initInverse {c : ℕ} : Fin (1+c+2+c+c+2) → Fin (c+c+2+(1+c+2)) :=
  Fin.addCases (Fin.addCases (Fin.addCases
    (fun i => Fin.natAdd (c+c+2) i)
    (fun i => Fin.castAdd (1+c+2) (Fin.castAdd 2 (Fin.castAdd c i))))
    (fun i => Fin.castAdd (1+c+2) (Fin.castAdd 2 (Fin.natAdd c i))))
    (fun i => Fin.castAdd (1+c+2) (Fin.natAdd (c+c) i))

def initPlacement (c : ℕ) : Fin (c+c+2+(1+c+2)) ≃ Fin (1+c+2+c+c+2) where
  toFun := Fin.addCases initTo (fun i => Fin.castAdd 2 (Fin.castAdd c (Fin.castAdd c i)))
  invFun := initInverse
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => induction i using Fin.addCases <;>
          simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [initInverse,Fin.addCases_left,Fin.addCases_right]
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => induction i using Fin.addCases <;>
          simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]
      | right i => simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]
    | right i => simp only [initTo,initInverse,Fin.addCases_left,Fin.addCases_right]

private theorem active_controls {c : ℕ} (b : Tapes (1+c+2) 0) (modulus current : Tapes c 0)
    (outer : Tapes 2 0) : Placement.active (initPlacement c) (controls b modulus current outer) =
      (modulus.append current).append outer := by
  unfold Placement.active initPlacement controls
  congr 1 <;> funext i <;> induction i using Fin.addCases with
  | left i => induction i using Fin.addCases <;>
      simp only [Equiv.coe_fn_mk,initTo,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  | right i => simp only [Equiv.coe_fn_mk,initTo,Tapes.append,Fin.addCases_left,Fin.addCases_right]

private theorem extra_controls {c : ℕ} (b : Tapes (1+c+2) 0) (modulus current : Tapes c 0)
    (outer : Tapes 2 0) : Placement.extra (initPlacement c) (controls b modulus current outer) = b := by
  unfold Placement.extra initPlacement controls
  cases b
  simp [Tapes.append]

private theorem replace_controls {c : ℕ} (b : Tapes (1+c+2) 0)
    (modulus modulus' current current' : Tapes c 0) (outer outer' : Tapes 2 0) :
    Placement.replace (initPlacement c) (controls b modulus current outer)
      ((modulus'.append current').append outer') = controls b modulus' current' outer' := by
  rw [Placement.replace,extra_controls]
  simpa only [active_controls,extra_controls] using
    Placement.view (initPlacement c) (controls b modulus' current' outer')

/-- Count input Q onto the one-hot banks, preserving all growing descriptors. -/
def initProgram {c : ℕ} (hc : 0 < c) : Program (1+c+2+c+c+2) 20 0 :=
  Placement.placed (ScalingControlInit.program hc) (initPlacement c)

private theorem init_hoare {c : ℕ} (hc : 0 < c) (Q : ℕ) (bs qs : List Bool)
    (hq : Counter.value qs = Q) (modulus current : Tapes c 0) :
    HoareTime (initProgram hc)
      (fun v => v = controls (innerBank (fun _ => []) bs) modulus current
        (CountedLoopReuse.controls empty (binary qs) 1 1))
      (fun v => v = CountedLoopReuse.bank
        (bank (fun _ => []) bs modulus current (OneHot.residue hc Q) (OneHot.residue hc 0)) empty (binary qs) 1 1)
      (7*Q+7*qs.length+18) := by
  have h := Placement.hoare_at (ScalingControlInit.init_hoare hc modulus current qs Q hq)
    (initPlacement c) (controls (innerBank (fun _ => []) bs) modulus current
      (CountedLoopReuse.controls empty (binary qs) 1 1)) (active_controls _ _ _ _)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  exact replace_controls _ _ _ _ _ _ _

/-- A single fixed transition installs all growing-counter and work-clock
sentinels on initially blank cells; binary Q/B descriptors remain untouched. -/
def markerMask (c : ℕ) : Fin (1+c+2+c+c+2) → Bool :=
  Fin.addCases (Fin.addCases (Fin.addCases
    (Fin.addCases (Fin.addCases (fun _ => false) (fun _ => true)) (fun i => i = 0))
    (fun _ => false)) (fun _ => false)) (fun i => i = 0)

private def marked {t : ℕ} (mask : Fin t → Bool) (v : Tapes t 0) : Tapes t 0 :=
  ⟨fun i => v.head i+if mask i then 1 else 0,
    fun i => if mask i then Function.update (v.tape i) (v.head i) separator else v.tape i⟩

def markerProgram (c : ℕ) : Program (1+c+2+c+c+2) 2 0 where
  tapes_pos := by omega
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => if markerMask c i then (separator,Move.right) else (symbols i,Move.stay)) else none

private theorem marker_hoare {c : ℕ} (v : Tapes (1+c+2+c+c+2) 0) :
    HoareTime (markerProgram c) (fun w => w = v)
      (fun w => w = marked (markerMask c) v) 1 := by
  intro w hw
  subst w
  refine ⟨1,⟨1,(marked (markerMask c) v).head,(marked (markerMask c) v).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,markerProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      cases h : markerMask c i <;> simp [h,marked,Move.offset]
    · funext i z
      cases h : markerMask c i <;> by_cases hz : z = v.head i <;> simp [h,marked,hz]
  · simp [step,markerProgram]

/-- Completely blank descriptor tapes and clocks, with their heads on the
cells where sentinels will be written. The supplied Q/B tapes are immutable. -/
def initial {c : ℕ} (bs qs : List Bool) (modulus current : Tapes c 0) : Tapes (1+c+2+c+c+2) 0 :=
  controls
    (CountedLoopReuse.bank
      ((⟨fun _ => 1,fun _ _ => blank⟩ : Tapes 1 0).append
        (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes c 0))
      (fun _ => blank) (binary bs) 0 1)
    modulus current (CountedLoopReuse.controls (fun _ => blank) (binary qs) 0 1)

private theorem marker_initial {c : ℕ} (bs qs : List Bool) (modulus current : Tapes c 0) :
    marked (markerMask c) (initial bs qs modulus current) =
      controls (innerBank (fun _ => []) bs) modulus current
        (CountedLoopReuse.controls empty (binary qs) 1 1) := by
  unfold marked markerMask initial controls innerBank counters CountedLoopReuse.bank
    CountedLoopReuse.controls Tapes.append
  congr 1
  · funext i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          induction i using Fin.addCases with
          | left i => induction i using Fin.addCases <;> simp
          | right i => fin_cases i <;> simp
        | right i => simp
      | right i => simp
    | right i => fin_cases i <;> simp
  · funext i z
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          induction i using Fin.addCases with
          | left i => induction i using Fin.addCases <;> simp [binary,empty,putBits,Function.update_apply]
          | right i => fin_cases i <;> simp [empty,Function.update_apply]
        | right i => simp
      | right i => simp
    | right i => fin_cases i <;> simp [empty,Function.update_apply]

/-- Input-size-independent descriptor synthesis, including physical sentinel
and residue initialization and all loop preparation and cleanup. -/
def program {c : ℕ} (hc : 0 < c) : Program (1+c+2+c+c+2) (2+20+(7+(c*19+1+2+5)+4)) 0 :=
  seq (seq (markerProgram c) (initProgram hc)) (sweepProgram hc)

theorem synthesize_hoare {c : ℕ} (hc : 0 < c) (Q B : ℕ) (bs qs : List Bool)
    (hb : Counter.value bs = B) (hq : Counter.value qs = Q) (modulus current : Tapes c 0) :
    HoareTime (program hc)
      (fun v => v = initial bs qs modulus current)
      (fun v => v = CountedLoopReuse.bank
        (bank (descriptors hc Q B Q) bs modulus current (OneHot.residue hc Q) (OneHot.residue hc Q)) empty (binary qs) 1 1)
      (10*(Q*B)+7*Q*bs.length+32*Q+14*qs.length+37) := by
  have hm := marker_hoare (initial bs qs modulus current)
  rw [marker_initial] at hm
  have h := (hm.seq (init_hoare hc Q bs qs hq modulus current)).seq
    (sweep_hoare hc Q B bs qs hb hq modulus current)
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) (by omega)

/-- Canonical supplied Q/B descriptors yield a concrete volume-linear bound
for positive dimensions; no piece-length descriptor is supplied as an oracle. -/
theorem synthesize_hoare_linear {c : ℕ} (hc : 0 < c) (Q B : ℕ) (hB : 0 < B)
    (bs qs : List Bool) (hb : Counter.value bs = B) (hq : Counter.value qs = Q)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (modulus current : Tapes c 0) :
    HoareTime (program hc)
      (fun v => v = initial bs qs modulus current)
      (fun v => v = CountedLoopReuse.bank
        (bank (descriptors hc Q B Q) bs modulus current (OneHot.residue hc Q) (OneHot.residue hc Q)) empty (binary qs) 1 1)
      (70*(Q*B)+51) := by
  apply (synthesize_hoare hc Q B bs qs hb hq modulus current).consequence
    (fun _ hv => hv) (fun _ hv => hv)
  have wb := GrowingCounterData.canonical_width bs cb
  have wq := GrowingCounterData.canonical_width qs cq
  have lb := Nat.log2_le_self (Counter.value bs)
  have lq := Nat.log2_le_self (Counter.value qs)
  rw [hb] at wb lb
  rw [hq] at wq lq
  have hwb : bs.length ≤ B+1 := by omega
  have hwq : qs.length ≤ Q+1 := by omega
  have hmul := Nat.mul_le_mul_left Q hwb
  have hQB : Q ≤ Q*B := by nlinarith
  nlinarith

end IntegerMultBounds.Machine.ScalingDescriptors
