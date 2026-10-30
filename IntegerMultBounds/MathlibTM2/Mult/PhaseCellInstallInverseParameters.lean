module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeScalarBank

/-! Install the eight ordinary inverse parameters from an actual word packet. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM

def inverseParameterWords (p u l target s t a b : ℕ) : List (Fin 25 × ℕ) :=
  [(0,p),(1,u),(2,l),(3,target),(4,s),(5,t),(6,a),(7,b)]

def inverseParameterState {A : ℕ} (p u l target s t a b : ℕ) : TblSt 25 A :=
  loadedBinaryState (inverseParameterWords p u l target s t a b) ⟨fun _ => 0,[]⟩

theorem inverseParameterState_inputs {A : ℕ} (p u l target s t a b : ℕ) (i : Fin 8) :
    (inverseParameterState (A := A) p u l target s t a b).val (Fin.castLE (by decide) i) =
      ![p,u,l,target,s,t,a,b] i := by
  apply loadedBinaryState_val_of_mem _ (by simp [inverseParameterWords])
  fin_cases i <;> simp [inverseParameterWords]

theorem inverseParameterState_zero {A : ℕ} (p u l target s t a b : ℕ) (i : Fin 25) (hi : 8 ≤ i.val) :
    (inverseParameterState (A := A) p u l target s t a b).val i = 0 := by
  apply loadedBinaryState_val_off
  intro r hr
  simp only [inverseParameterWords,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro he
    have hv := congrArg Fin.val he
    norm_num at hv
    omega

@[simp] theorem inverseParameterState_acc {A : ℕ} (p u l target s t a b : ℕ) :
    (inverseParameterState (A := A) p u l target s t a b).acc = [] :=
  loadedBinaryState_acc _ _

theorem inverseParameterState_fits {A : ℕ} (B p u l target s t a b : ℕ)
    (hfit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,b] i < 2^B) :
    ∀ i, (inverseParameterState (A := A) p u l target s t a b).val i < 2^B := by
  intro i
  by_cases hi : i.val < 8
  · have hh := inverseParameterState_inputs (A := A) p u l target s t a b ⟨i.val,hi⟩
    have he : Fin.castLE (by decide : 8 ≤ 25) (⟨i.val,hi⟩ : Fin 8) = i := Fin.ext rfl
    rw [he] at hh
    rw [hh]
    exact hfit _
  · rw [inverseParameterState_zero p u l target s t a b i (by omega)]
    exact Nat.two_pow_pos _

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def installInverseParameters (rg : TblR 25 → Fin T) (src : Fin T) : Pr P T Q A U :=
  installScalarInputs rg src [0,1,2,3,4,5,6,7]

/-- Allocate all private scalar words and consume eight actual ordinary input
words. The resulting fits, zero scratch values and accumulator are derived
from this execution, with no initial encoded scalar-bank premise. -/
theorem installInverseParameters_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (src : Fin T) (hsep : ∀ r, rg r ≠ src) (B p u l target s t a b : ℕ)
    (hfit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,b] i < 2^B)
    (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ r : TblR 25, r ≠ .wr → S.R (rg r) = [])
    (hsrc : S.R src = (inverseParameterWords p u l target s t a b).flatMap (fun r => binSyms B r.2)++tail) :
    ∃ v' F, v'.user = v.user ∧
      Exec body (installInverseParameters rg src) (mk v S) (164*B+166) (mk v' F) ∧
      tblHolds rg F (tblRho B wl [] (inverseParameterState p u l target s t a b)) ∧
      (∀ i, (inverseParameterState (A := A) p u l target s t a b).val i < 2^B) ∧
      F.R src = tail ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → (∀ r, rg r ≠ i) → F.R i = S.R i := by
  obtain ⟨v',F,hu,he,hh,hs,hin,hout,hL,hframe⟩ := installScalarInputs_exec (body := body) rg hrg src hsep
    (inverseParameterWords p u l target s t a b) B wl hwl tail v S hwidth hblank hsrc
  refine ⟨v',F,hu,?_,hh,inverseParameterState_fits B p u l target s t a b hfit,hs,hin,hout,hL,hframe⟩
  convert he using 1 <;> simp [inverseParameterWords,installInverseParameters] <;> ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
