module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateFamilyDispatchBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFullLineGridRecord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDerivedInverseRoundBatch

/-! Construct the full-period supplier's actual record bank from ordinary
headers and live RHS data. Canonical scalar room is derived, not supplied. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem generateFullLineGridBank_exec
    (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (source : Fin 8 → Fin T) (word saved tmp queue carry ambient count : Fin T)
    (hparams : ∀ i, [source i,work (familyInverseScalarReg .wr),word,saved,tmp,queue].Nodup)
    (hcopy : [ambient,work 110,tmp,saved].Nodup)
    (hcount : [count,work (familyInverseCoreReg 246),saved].Nodup)
    (hambientOff : ∀ i, ambient ≠ work i) (hcountOff : ∀ i, count ≠ work i)
    (hscratchOff : ∀ i ∈ [word,saved,tmp,queue], ∀ j, i ≠ work j)
    (p u l target t : ℕ) (hst : s < t) (Fs : List (ZMod s → GaussianInt))
    (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![p,u,l,target,s,t,0,s] i)
    (hwidth : S.R (work (familyInverseScalarReg .wr)) =
      List.replicate (inverseCallerWordWidth p u l target s t) tick)
    (hblank : ∀ i, i ≠ familyInverseScalarReg .wr → S.R (work i) = [])
    (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ i ∈ [word,saved,tmp,queue], S.R i = [])
    (hambient : S.R ambient = cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten)
    (hN : (S.R count).length = Fs.length) (depth : ℕ) :
    let B := inverseCallerWordWidth p u l target s t
    let xs := cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten
    ∃ v' n F, v'.user = v.user ∧
      n ≤ ((p+u+l+target+s+t+0+s)*(4*B+10)+228*B+263)+(6*xs.length+6)+(4*Fs.length+4) ∧
      (∀ i, F.R (work i) = (fullLineGridRecord (A := A) p u l target t Fs).words i) ∧
      (∀ i, (∀ j, i ≠ work j) → F.R i = S.R i) ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((392*B+396)+(2*(6*xs.length+6)+2*(4*Fs.length+4)))) depth
        (generateFamilyDispatchBank work source word saved tmp queue carry ambient count)
        (Host.mk v S) n (Host.mk v' F) := by
  dsimp only
  have hroom := inverseCallerWordWidth_fits_cuts p u l target s t 0 s
  have hfit := inverseInputScalars_fit (A := A) hst (Nat.zero_le s) le_rfl hroom.1 hroom.2.1 hroom.2.2
  have hinputs : ∀ i : Fin 8, ![p,u,l,target,s,t,0,s] i < 2^inverseCallerWordWidth p u l target s t := by
    intro i
    have hvalue : ![p,u,l,target,s,t,0,s] i =
        (inverseInputScalars (A := A) p u l target s t 0 s).val (Fin.castLE (by decide : 8 ≤ 25) i) := by
      fin_cases i <;> rfl
    rw [hvalue]
    exact hfit _
  obtain ⟨v',n,F,hu,hn,hbank,hframe,hI,hO,hL,he⟩ := generateFamilyDispatchBank_exec
    (body := body) work hwork source word saved tmp queue carry ambient count hparams hcopy hcount
    hambientOff hcountOff hscratchOff p u l target s t 0 s _ Fs.length hinputs _ _
    (List.length_replicate ..) v S hvalues hwidth hblank hleft hscratch hambient hN depth
  refine ⟨v',n,F,hu,hn,?_,hframe,hI,hO,hL,he⟩
  intro i
  exact congrArg (fun H : Stacks 303 A => H.R i) hbank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
