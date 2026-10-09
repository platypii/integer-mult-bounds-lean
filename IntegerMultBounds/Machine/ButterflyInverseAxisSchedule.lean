import IntegerMultBounds.Machine.ButterflyInverseAxisArray

/-! A fixed runtime-counted schedule executes successive selected axes. Every
iteration constructs its own powers and geometry from original D,t,R,p, runs the
physical native inverse butterfly and erases all derived state before the next axis.
The cost is uniform linear volume times the number of actually processed axes. -/
namespace IntegerMultBounds.Machine.ButterflyInverseAxisSchedule
noncomputable section
open ButterflyAxisArray (Array Width)
open ButterflyInverseAxisArray (applyAxis width_apply)
open ButterflyStreamData (full)
open ButterflyAxisHeadersBudget (logicalVolume)

def step (D t R p : ℕ) (f : Array D R) : Array D R :=
  if ht : t<D then applyAxis D t R p ht f else f

def run (D start R p : ℕ) : ℕ → Array D R → Array D R
  | 0,f => f
  | n+1,f => step D (start+n) R p (run D start R p n f)

theorem width_step (D t R p : ℕ) (f : Array D R) (hw : Width D R p f) : Width D R p (step D t R p f) := by
  unfold step
  split_ifs with ht
  · exact width_apply D t R p ht f hw
  · exact hw

theorem width_run (D start R p n : ℕ) (f : Array D R) (hw : Width D R p f) :
    Width D R p (run D start R p n f) := by
  induction n with
  | zero => exact hw
  | succ n ih => exact width_step D (start+n) R p _ ih

def endpoint (D start R p n : ℕ) (f : Array D R) :=
  ButterflyAxisOriginal.bank D (start+n) R p (full (fun _ => blank) 0 (run D start R p n f))

def header (bs : List Bool) : Tapes 1 2 := CountedLoopReuseAlphabet.one (RadixZeroFill.encodedBinary bs) 1

def rangeBank (D start R p n : ℕ) (f : Array D R) (bs : List Bool) :=
  CountedLoopHeaderClean.bank ((endpoint D start R p n f).append (header bs))

def rangeProgram := CountedLoopHeaderClean.program (extend ButterflyInverseAxisOriginal.program 1)
  (Fin.natAdd ButterflyAxisOriginal.count (0 : Fin 1))

def cost (D R p n : ℕ) (bs : List Bool) :=
  n*(ButterflyAxisOriginal.constant*logicalVolume D R p)+6*n+11*bs.length+35

theorem body_runs (D start R p n : ℕ) (hfit : start+n<D) (hR : 0<R)
    (f : Array D R) (hw : Width D R p f) :
    HoareTime ButterflyInverseAxisOriginal.program (fun v => v=endpoint D start R p n f)
      (fun v => v=endpoint D start R p (n+1) f)
      (ButterflyAxisOriginal.constant*logicalVolume D R p) := by
  have hh := ButterflyInverseAxisArray.runs D (start+n) R p hfit hR (run D start R p n f)
    (width_run D start R p n f hw)
  simpa only [endpoint,run,step,dite_eq_left hfit,Nat.add_assoc] using hh

/-- An original retained count chooses a contiguous axis interval; only the
actually selected number of passes is charged. No schedule is unrolled into
finite control, and all per-axis descriptor work is included. -/
theorem range_runs (D start R p n : ℕ) (hfit : start+n≤D) (hR : 0<R)
    (f : Array D R) (hw : Width D R p f) (bs : List Bool) (hn : Counter.value bs=n) :
    HoareTime rangeProgram (fun v => v=rangeBank D start R p 0 f bs)
      (fun v => v=rangeBank D start R p n f bs) (cost D R p n bs) := by
  have hh := CountedLoopHeaderClean.runs (extend ButterflyInverseAxisOriginal.program 1)
    (Fin.natAdd ButterflyAxisOriginal.count (0 : Fin 1)) bs n
    (fun i => (endpoint D start R p i f).append (header bs))
    (fun _ => ButterflyAxisOriginal.constant*logicalVolume D R p)
    (by simp [Tapes.append,header,CountedLoopReuseAlphabet.one]) hn
    (by intro i hi; exact hoare_extend_eq (body_runs D start R p i (by omega) hR f hw) (header bs))
  simpa only [rangeProgram,rangeBank,cost,CountedLoopHeaderClean.cost,
    Finset.sum_const,Finset.card_range,smul_eq_mul] using hh

def allProgram := CountedLoopHeaderClean.program ButterflyInverseAxisOriginal.program 0

def allBank (D R p n : ℕ) (f : Array D R) := CountedLoopHeaderClean.bank (endpoint D 0 R p n f)

/-- Small-dimension fallback needs no additional axis-count descriptor: its
original dimension header physically controls the entire loop. -/
theorem all_runs (D R p : ℕ) (hR : 0<R) (f : Array D R) (hw : Width D R p f) :
    HoareTime allProgram (fun v => v=allBank D R p 0 f)
      (fun v => v=allBank D R p D f) (cost D R p D (RecursiveChildQuotientsConstant.bits D)) := by
  have hh := CountedLoopHeaderClean.runs ButterflyInverseAxisOriginal.program 0
    (RecursiveChildQuotientsConstant.bits D) D (fun i => endpoint D 0 R p i f)
    (fun _ => ButterflyAxisOriginal.constant*logicalVolume D R p)
    (by constructor <;> rfl) (RecursiveChildQuotientsConstant.bits_value D)
    (fun i hi => body_runs D 0 R p i (by omega) hR f hw)
  simpa only [allProgram,allBank,cost,CountedLoopHeaderClean.cost,
    Finset.sum_const,Finset.card_range,smul_eq_mul] using hh

def constant := ButterflyAxisOriginal.constant+63

theorem cost_linear (D R p n : ℕ) (hR : 0<R) (hn : 0<n) (bs : List Bool)
    (hc : Counter.value bs=n) (hb : GrowingCounterData.Canonical bs) :
    cost D R p n bs≤constant*logicalVolume D R p*n := by
  have hV := ButterflyAxisHeadersInstall.volume_pos D R p hR
  have hl := GrowingCounterData.canonical_width bs hb
  rw [hc] at hl
  have hh := Nat.log2_le_self n
  have hrest : 6*n+11*bs.length+35≤63*n := by omega
  have hmul := Nat.mul_le_mul_left (63*n) (show 1≤logicalVolume D R p by omega)
  unfold cost constant
  nlinarith

theorem range_runs_linear (D start R p n : ℕ) (hfit : start+n≤D) (hR : 0<R) (hn : 0<n)
    (f : Array D R) (hw : Width D R p f) (bs : List Bool)
    (hc : Counter.value bs=n) (hb : GrowingCounterData.Canonical bs) :
    HoareTime rangeProgram (fun v => v=rangeBank D start R p 0 f bs)
      (fun v => v=rangeBank D start R p n f bs) (constant*logicalVolume D R p*n) :=
  (range_runs D start R p n hfit hR f hw bs hc).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear D R p n hR hn bs hc hb)

theorem all_runs_linear (D R p : ℕ) (hD : 0<D) (hR : 0<R) (f : Array D R) (hw : Width D R p f) :
    HoareTime allProgram (fun v => v=allBank D R p 0 f)
      (fun v => v=allBank D R p D f) (constant*logicalVolume D R p*D) :=
  (all_runs D R p hR f hw).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear D R p D hR hD _ (RecursiveChildQuotientsConstant.bits_value D)
      (RecursiveChildQuotientsConstant.bits_canonical D))

end
end IntegerMultBounds.Machine.ButterflyInverseAxisSchedule
