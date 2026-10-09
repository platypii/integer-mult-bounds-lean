import IntegerMultBounds.Machine.CountedRankSplitEndpoint

/-! Thirteen tapes: the original twelve-tape short-counter splitter bank plus
one third address word. The existing nq/nb descriptors are shared and erased. -/
namespace IntegerMultBounds.Machine.CountedLateRankBank
noncomputable section
variable {a : ℕ}

def one (u : ℤ → Fin (a+4)) (p : ℤ) : Tapes 1 a := ⟨fun _ => p,fun _ => u⟩
def bank (f v w u : ℤ → Fin (a+4)) (p pv pw pu : ℤ) (hs : Fin 3 → List Bool)
    (nq nb : Option (List Bool)) :=
  (CountedRankSplitBank.bank f v w p pv pw hs nq nb).append (one u pu)

def copyUPlace : Fin (4+9) ≃ Fin 13 where
  toFun := ![0,12,8,7,1,2,3,4,5,6,9,10,11]
  invFun := ![0,4,5,6,7,8,9,3,2,10,11,12,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def uPlace : Fin (3+10) ≃ Fin 13 where
  toFun := ![12,8,7,0,1,2,3,4,5,6,9,10,11]
  invFun := ![3,4,5,6,7,8,9,2,1,10,11,12,0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def copyU := Placement.placed (CountedRankSplitCopy.program (a := a)) copyUPlace
def backU := Placement.placed (CountedRankSplitPosition.program (a := a)) uPlace

theorem copiesU (f v w u : ℤ → Fin (a+4)) (p pv pw pu : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hv : Counter.value bs = N) :
    HoareTime (copyU (a := a)) (fun z => z = bank f v w u p pv pw pu hs (some qs) (some bs))
      (fun z => z = bank f v w (putWord u pu (CopyCells.cells f p N))
        (p+N) pv pw (pu+N) hs (some qs) (some bs)) (7*N+7*bs.length+28) := by
  apply CountedRankSplitBank.placed_exact copyUPlace _ _ _ _ _ _ _
    (CountedRankSplitCopy.copies f u p pu bs N hv)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp only [copyUPlace,Equiv.coe_fn_mk,bank,one,
    Tapes.append]
  all_goals rfl

theorem movesU (f v w u : ℤ → Fin (a+4)) (p pv pw pu : ℤ) (hs : Fin 3 → List Bool)
    (qs bs : List Bool) (N : ℕ) (hv : Counter.value bs = N) :
    HoareTime (backU (a := a)) (fun z => z = bank f v w u p pv pw pu hs (some qs) (some bs))
      (fun z => z = bank f v w u p pv pw (pu-N) hs (some qs) (some bs)) (7*N+7*bs.length+28) := by
  apply CountedRankSplitBank.placed_exact uPlace _ _ _ _ _ _ _
    (CountedRankSplitPosition.moves u pu bs N hv)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp only [uPlace,Equiv.coe_fn_mk,bank,one,
    Tapes.append]
  all_goals rfl

end
end IntegerMultBounds.Machine.CountedLateRankBank
