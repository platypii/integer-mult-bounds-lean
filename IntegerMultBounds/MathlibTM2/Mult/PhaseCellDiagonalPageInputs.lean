module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalConversionLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob

/-! Page input assignments reuse retained inverse parameters, including u=alpha^2. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

noncomputable section

def diagonalCoreStart : Fin tapes := recovery (.work 309)
def diagonalCoreEnd : Fin tapes := recovery (.work 310)

def diagonalPageInputs : List (Fin 48 × Fin tapes) :=
  [(34,recovery (.parameter 4)),(35,recovery (.parameter 5)),(36,recovery (.parameter 1)),
    (19,recovery (.parameter 0)),(37,diagonalCoreStart),(47,diagonalCoreEnd)]

def diagonalPageWords (s t u p c n : ℕ) : List (Fin 48 × ℕ) :=
  [(34,s),(35,t),(36,u),(19,p),(37,c),(47,c+n)]

theorem diagonalPageInputs_values {A : ℕ} (S : Stacks tapes A) (s t u p c n : ℕ)
    (hS : (S.R (recovery (.parameter 4))).length = s)
    (hT : (S.R (recovery (.parameter 5))).length = t)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (hp : (S.R (recovery (.parameter 0))).length = p)
    (hc : (S.R diagonalCoreStart).length = c) (hend : (S.R diagonalCoreEnd).length = c+n) :
    diagonalPageInputs.map (fun a => (a.1,(S.R a.2).length)) = diagonalPageWords s t u p c n := by
  simp only [diagonalPageInputs,diagonalPageWords,List.map_cons,List.map_nil,hS,hT,hu,hp,hc,hend]

theorem diagonalPageState_values {A : ℕ} (s t u p c n : ℕ) :
    let st : TblSt 48 A := loadedBinaryState (diagonalPageWords s t u p c n) ⟨fun _ => 0,[]⟩
    st.val 34 = s ∧ st.val 35 = t ∧ st.val 36 = u ∧ st.val 19 = p ∧ st.val 37 = c ∧ st.val 47 = c+n ∧ st.acc = [] := by
  simp [diagonalPageWords,loadedBinaryState]

theorem diagonalPage_squared_parameter {s t p u l alpha : ℕ} [NeZero s] {gap : ℝ}
    (axis : RecoveryAxisBounds s t p u l (alpha : ℝ) gap) : u = alpha^2 := by
  have h := axis.hαu
  exact_mod_cast h.symm

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
