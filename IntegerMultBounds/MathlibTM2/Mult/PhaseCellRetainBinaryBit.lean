module

public import IntegerMultBounds.MathlibTM2.Node.Params
public import IntegerMultBounds.MathlibTM2.Host.WordTape

/-! Retain a computed binary bit as a unary control before releasing its table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def retainBinaryBit (src dst : Fin T) : Pr P₀ T Q A U :=
  .act (.peek (.rt src) (fun v x => {v with flag := (x.map symBit).getD false})
    (.branch (·.flag) (.push (.rt dst) (fun _ => tick) .done) .done))

theorem retainBinaryBit_exec (src dst : Fin T) (V : ℕ) (hV : 0 < V) (flag : Bool)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms V (if flag then 1 else 0)) :
    Exec body (retainBinaryBit src dst) (mk v S) 1
      (mk {v with flag := flag} {S with R := (Function.update S.R dst
        ((if flag then [tick] else [])++S.R dst))}) := by
  have hread : ((S.R src).head?.map symBit).getD false = flag := by
    cases V with
    | zero => omega
    | succ V => cases flag <;> simp [hsrc,binSyms_succ,symBit_bitSymbol]
  cases flag <;> simpa [retainBinaryBit,Action.run,hread,update_rt] using
    (Exec.act (body := body) (.peek (.rt src) (fun v x => {v with flag := (x.map symBit).getD false})
      (.branch (·.flag) (.push (.rt dst) (fun _ => tick) .done) .done)) (mk v S))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
