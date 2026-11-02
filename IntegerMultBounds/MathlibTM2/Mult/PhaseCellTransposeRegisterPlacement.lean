module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Place a metadata generator beside any worker. Only its queue output is
redirected into the worker; its consuming count remains in the suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace TransposeRegisterPlacement
variable {T : ℕ}

def worker (i : Fin T) : Fin (T+117) := ⟨i.val,by omega⟩

def generator (queue : Fin T) (j : Fin 117) : Fin (T+117) :=
  if j = 109 then worker queue else ⟨T+j.val,by have := j.isLt; omega⟩

theorem worker_injective : Function.Injective (worker (T := T)) := by
  intro i j h
  have hh := congrArg (fun x : Fin (T+117) => x.val) h
  exact Fin.ext hh

theorem generator_injective (queue : Fin T) : Function.Injective (generator queue) := by
  intro i j h
  have hv := congrArg (fun x : Fin (T+117) => x.val) h
  have hq := queue.isLt
  by_cases hi : i = 109 <;> by_cases hj : j = 109
  · exact hi.trans hj.symm
  · simp [generator,worker,hi,hj] at hv
    omega
  · simp [generator,worker,hi,hj] at hv
    omega
  · apply Fin.ext
    simpa [generator,hi,hj] using hv

@[simp] theorem generator_queue (queue : Fin T) : generator queue 109 = worker queue := by
  simp [generator]

theorem generator_off_worker (queue : Fin T) (j : Fin 117) (hj : j ≠ 109) (i : Fin T) :
    generator queue j ≠ worker i := by
  intro h
  have hv := congrArg (fun x : Fin (T+117) => x.val) h
  have hi := i.isLt
  simp [generator,worker,hj] at hv
  omega

theorem generator_bank_off (queue : Fin T) (j : Fin 117) (hj : j.val < 31) (i : Fin T) :
    generator queue j ≠ worker i :=
  generator_off_worker queue j (by intro h; subst j; norm_num at hj) i

theorem count_off (queue : Fin T) (i : Fin T) : worker i ≠ generator queue 116 :=
  (generator_off_worker queue 116 (by decide) i).symm

end TransposeRegisterPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
