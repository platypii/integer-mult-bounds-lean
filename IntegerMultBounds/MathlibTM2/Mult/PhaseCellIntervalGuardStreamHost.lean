module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalGuardBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableStreamHost

/-! Execute a geometry program with one-symbol emissions, publish its stream and release its bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def intervalGuardStreamHost (code : TblCode 17) : Pr P₀ 117 Q A U :=
  .seq (uclear 18) (.seq (.act (.push (.rt 18) (fun _ => tick) .done))
    (.seq (tblHost intervalGuardReg code 109) releaseIntervalGuardBank))

theorem intervalGuardStreamHost_exec {V K : ℕ} (hV : 1 ≤ V) (code : TblCode 17) (st : TblSt 17 A)
    (xs : List (Fin (A+4))) (hacc : st.acc = [])
    (hc : TblDo A V 1 code st (fun st' => st'.acc = xs.reverse++st.acc) K)
    (hbound : ∀ r, st.val r < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds intervalGuardReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ K*tblC V 1+66*V+2*xs.length+70 ∧
      Exec body (intervalGuardStreamHost code) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 32 then [] else if r = 109 then xs++S.R r else S.R r}) := by
  have hnd : intervalGuardPorts.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 117 => k.val) he)
  have he := tableStreamHost_exec (body := body) intervalGuardReg intervalGuardReg_injective
    intervalGuardPorts hnd
    (fun k hk => intervalGuardReg_covers k ((mem_intervalGuardPorts k).mp hk))
    (fun r => (mem_intervalGuardPorts _).mpr (intervalGuardReg_range r))
    109 (by rw [mem_intervalGuardPorts]; decide) hV code st xs hacc hc hbound v S hS
  simp only [mem_intervalGuardPorts] at he
  simpa [intervalGuardStreamHost,tableStreamHost,releaseIntervalGuardBank,
    intervalGuardPorts,intervalGuardReg,Nat.add_assoc] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
