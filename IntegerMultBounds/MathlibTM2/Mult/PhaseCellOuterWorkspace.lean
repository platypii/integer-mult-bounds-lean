module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeUnaryKey

/-! A fixed caller bank isolates the 117-register solver from retained outer
parameters, the key queue and its counter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

def groupReg (i : Fin 117) : Fin 144 := ⟨i.val, by omega⟩

theorem groupReg_injective : Function.Injective groupReg := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun k : Fin 144 => k.val) he

theorem groupReg_off (k : Fin 144) (hk : 117 ≤ k.val) : ∀ i, groupReg i ≠ k := by
  intro i he
  have hh := congrArg (fun k : Fin 144 => k.val) he
  simp only [groupReg] at hh
  omega

theorem groupProject_updateR {A : ℕ} (S : Stacks 144 A) (k : Fin 144)
    (xs : List (Fin (A+4))) (hk : 117 ≤ k.val) :
    embStk groupReg { S with R := Function.update S.R k xs } = embStk groupReg S := by
  ext1
  · rfl
  · rfl
  · rfl
  · funext i
    simp [embStk, groupReg_off k hk i]

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

def takeOuterLengthKey : Pr P 144 Q A U := takeUnaryKey 125 126 128 134 135 136 137

theorem takeOuterLengthKey_exec (V L : ℕ) (hL : L < 2^V) (suffix : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A) (hV : (S.R 125).length = V)
    (hsrc : S.R 126 = binSyms V L ++ suffix)
    (hfresh : ∀ k ∈ [(128 : Fin 144),134,135,136,137], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6*L+19*V+14 ∧
      Exec body takeOuterLengthKey (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R 126 suffix) 128 (List.replicate L tick)) }) :=
  takeUnaryKey_exec (body := body) (by decide) V L hL suffix v S hV hsrc hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
