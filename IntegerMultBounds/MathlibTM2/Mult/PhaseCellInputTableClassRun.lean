module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableRetirement
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Install and retire the external table around a certified class trace.
Only the numerical output survives; retained caller sources are unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A n : ℕ} {P U : Type}

noncomputable def inputTableClassProgram (rg : TblR n → Fin T) (input : Fin n → Fin T)
    (width zero : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (chirpBankLoad rg input width zero) (.seq p (clearWords (inputTableWords rg)))

theorem inputTableClassRun_exec_within (body : P → Pr P T Q A U)
    (rg : TblR n → Fin T) (hrg : Function.Injective rg) (input : Fin n → Fin T)
    (width zero : Fin T) (hwidth : ∀ r, rg r ≠ width) (hzero : ∀ r, rg r ≠ zero)
    (hinput : ∀ i r, rg r ≠ input i) (D : ℕ) (value : Fin T → ℕ)
    (hfit : ∀ i, value (input i) < 2^D)
    (v : HS T Q A U) (S : Stacks T A)
    (hw : (S.R width).length = D) (hz : S.R zero = [])
    (hsrc : ∀ i, S.R (input i) = binSyms D (value (input i))) (hblank : ∀ r, S.R (rg r) = [])
    (k : Fin T) (hoff : ∀ r, rg r ≠ k) (p : Pr P T Q A U)
    (runTime : ℝ) (runStock depth : ℕ) (Valid : List (List (Fin (A+4))) → Prop)
    (hrun : ∀ w : HS T Q A U, ∃ w', ∃ m : ℕ, ∃ outputs,
      w'.user = w.user ∧ (m : ℝ) ≤ runTime ∧ Valid outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk w (loadedInputTable rg input D value S))+depth+runStock)
        depth p (Host.mk w (loadedInputTable rg input D value S)) m
        (Host.mk w' {loadedInputTable rg input D value S with R :=
          (Function.update (loadedInputTable rg input D value S).R k
            (outputs.reverse.flatten++(loadedInputTable rg input D value S).R k))})) :
    ∃ v', ∃ m : ℕ, ∃ outputs, v'.user = v.user ∧
      (m : ℝ) ≤ (((10*n+6)*D+10*n+12 : ℕ) : ℝ)+runTime ∧ Valid outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (3*((8*n+4)*D+8*n+9)+runStock)) depth
        (inputTableClassProgram rg input width zero p) (Host.mk v S) m
        (Host.mk v' {S with R := (Function.update S.R k (outputs.reverse.flatten++S.R k))}) := by
  obtain ⟨v₁,hu₁,he₁,hholds⟩ := loadInputTable_exec_within body rg hrg input width zero hwidth hzero hinput
    D value hfit v S hw hz hsrc hblank depth
  obtain ⟨v₂,m₂,outputs,hu₂,hm₂,hvalid,he₂⟩ := hrun v₁
  have hout : (loadedInputTable rg input D value S).R k = S.R k :=
    loadedInputTable_off rg input D value S k (fun r => (hoff r).symm)
  rw [hout] at he₂
  obtain ⟨v₃,hu₃,he₃⟩ := retireInputTable_exec_within body rg hrg input D value k hoff
    (outputs.reverse.flatten++S.R k) v₂ S hblank depth
  refine ⟨v₃,((8*n+4)*D+8*n+9)+(m₂+((2*n+2)*D+2*n+3)),outputs,
    hu₃.trans (hu₂.trans hu₁),?_,hvalid,?_⟩
  · push_cast
    nlinarith only [hm₂]
  · have he := mn_seq_within_add he₁ (mn_seq_within_add he₂ he₃)
    simpa only [inputTableClassProgram,Nat.add_zero] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
