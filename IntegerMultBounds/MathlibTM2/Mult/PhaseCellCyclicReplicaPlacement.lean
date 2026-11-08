module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassInput

/-! Reuse two existing 300-register cached banks beside one 234-register Schur
bank. Separation is arithmetic on offsets, with no concrete tape enumeration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

namespace CachedReplicaPassPlacement

def standard : CachedReplicaPassPlacement 300 where
  plan := ReplicaCouplingPlacement.standardInterior
  coupling := ReplicaCouplingPlacement.standard
  output := 247
  rhs := 248
  gather_output := by
    intro i hi; have hv := congrArg Fin.val hi
    change i.val = 247 at hv
    have := i.isLt; omega
  gather_rhs := by
    intro i hi; have hv := congrArg Fin.val hi
    change i.val = 248 at hv
    have := i.isLt; omega
  bank_output := fun i => (ReplicaCouplingPlacement.standard_outputs_disjoint i).1
  bank_rhs := fun i => (ReplicaCouplingPlacement.standard_outputs_disjoint i).2
  solver_output := by
    intro i hi; have hv := congrArg Fin.val hi
    change 126+i.val = 247 at hv
    have := i.isLt; omega
  solver_rhs := by
    intro i hi; have hv := congrArg Fin.val hi
    change 126+i.val = 248 at hv
    have := i.isLt; omega
  output_rhs := by decide

def reindex {T T' : ℕ} (job : CachedReplicaPassPlacement T)
    (e : Fin T → Fin T') (he : Function.Injective e) : CachedReplicaPassPlacement T' where
  plan := job.plan.reindex e he
  coupling := job.coupling.reindex e he
  output := e job.output
  rhs := e job.rhs
  gather_output := fun i h => job.gather_output i (he h)
  gather_rhs := fun i h => job.gather_rhs i (he h)
  bank_output := by intro i h; exact job.bank_output i (he (by simpa using h))
  bank_rhs := by intro i h; exact job.bank_rhs i (he (by simpa using h))
  solver_output := fun i h => job.solver_output i (he h)
  solver_rhs := fun i h => job.solver_rhs i (he h)
  output_rhs := he.ne job.output_rhs

theorem reindex_source {T T' : ℕ} (job : CachedReplicaPassPlacement T)
    (e : Fin T → Fin T') (he : Function.Injective e) {k : Fin T'}
    (h : (job.reindex e he).Owns k) : ∃ i, e i = k := by
  cases h with
  | bank i => exact ⟨job.coupling.bank i,by simp [reindex]⟩
  | gather i => exact ⟨job.plan.gather i,rfl⟩
  | solver i => exact ⟨job.plan.solver i,rfl⟩
  | output => exact ⟨job.output,rfl⟩
  | rhs => exact ⟨job.rhs,rfl⟩

end CachedReplicaPassPlacement

namespace CyclicReplicaPlacement

def leftReg (i : Fin 300) : Fin 834 := ⟨i.val,by have := i.isLt; omega⟩
def rightReg (i : Fin 300) : Fin 834 := ⟨300+i.val,by have := i.isLt; omega⟩
def factorReg (i : Fin 234) : Fin 834 := ⟨600+i.val,by have := i.isLt; omega⟩

theorem leftReg_injective : Function.Injective leftReg := by
  intro i j h
  have hv := congrArg (fun k : Fin 834 => k.val) h
  exact Fin.ext hv
theorem rightReg_injective : Function.Injective rightReg := by
  intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; change 300+i.val = 300+j.val at hv; omega
theorem factorReg_injective : Function.Injective factorReg := by
  intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; change 600+i.val = 600+j.val at hv; omega

def left : CachedReplicaPassPlacement 834 := CachedReplicaPassPlacement.standard.reindex leftReg leftReg_injective
def right : CachedReplicaPassPlacement 834 := CachedReplicaPassPlacement.standard.reindex rightReg rightReg_injective

theorem disjoint (k : Fin 834) (hl : left.Owns k) : ¬right.Owns k := by
  intro hr
  obtain ⟨i,hi⟩ := CachedReplicaPassPlacement.reindex_source _ leftReg leftReg_injective hl
  obtain ⟨j,hj⟩ := CachedReplicaPassPlacement.reindex_source _ rightReg rightReg_injective hr
  have hv := congrArg Fin.val (hi.trans hj.symm)
  change i.val = 300+j.val at hv
  have := i.isLt; omega

theorem factor_disjoint (j : Fin 234) : ¬left.Owns (factorReg j) ∧ ¬right.Owns (factorReg j) := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := CachedReplicaPassPlacement.reindex_source _ leftReg leftReg_injective h
    have hv := congrArg Fin.val hi
    change i.val = 600+j.val at hv
    have := i.isLt; omega
  · intro h
    obtain ⟨i,hi⟩ := CachedReplicaPassPlacement.reindex_source _ rightReg rightReg_injective h
    have hv := congrArg Fin.val hi
    change 300+i.val = 600+j.val at hv
    have := i.isLt; omega

end CyclicReplicaPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
