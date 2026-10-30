module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicResidualBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

/-! The periodic residual endpoint preserves the surrounding prepared factor bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem periodicBoundaryResult_preparedBank {A s q w W N : ℕ} [NeZero s]
    (S : Stacks 242 A) (V t band a b : ℕ) (D E : ZMod s → GaussianInt)
    (rhsTail : List (Fin (A+4))) (h : PackedPreparedBank q w W N S) :
    let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
    let R := periodicBoundaryResult (embStk e S) V s t band a b w D E rhsTail
    PackedPreparedBank q w W N (embOvr e R.get S) := by
  let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
  let R := periodicBoundaryResult (embStk e S) V s t band a b w D E rhsTail
  have hinj : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin 242 => k.val) hij
  have hread (i : Fin 168) : (embOvr e R.get S).R (e i) = R.R i := by
    have hh := embOvr_get hinj R.get S (.rt i)
    change (embOvr e R.get S).R (e i) = (R.R i).map id at hh
    simpa only [List.map_id] using hh
  apply h.of_runtime_frame
  · change (embOvr e (embStk e S).get S).L = S.L
    exact congrArg Stacks.L (embOvr_stk (e := e) S)
  · intro k hk
    let i : Fin 168 := ⟨k.val,by omega⟩
    have he : e i = k := Fin.ext rfl
    rw [← he,hread]
    exact periodicBoundaryResult_frame (embStk e S) V s t band a b w D E rhsTail i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff]
      dsimp [i]
      omega)
  · change (embOvr e R.get S).R (e 119) = _
    rw [hread]
    exact periodicBoundaryResult_frame (embStk e S) V s t band a b w D E rhsTail 119 (by decide)
  · intro k hk _
    exact (embOvr_off R.get S (by
      intro i hi
      have hv := congrArg Fin.val hi
      have hi' := i.isLt
      dsimp [e] at hv
      omega)).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
