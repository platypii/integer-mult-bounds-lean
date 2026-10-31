module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateFullLineGridBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareDescriptorBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSchedule

/-! Ordinary full-period inputs generate their descriptor and dispatch clock.
The exact final frame identifies the generated bank and the two owned controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def generateFullLineDescriptor (work : Fin 303 → Fin T) (source : Fin 8 → Fin T)
    (word saved tmp queue carry ambient count dst clock : Fin T) : Pr P T Q A U :=
  .seq (generateFamilyDispatchBank work source word saved tmp queue carry ambient count)
    (prepareDescriptorBank work dst tmp saved clock)

theorem generateFullLineDescriptor_exec
    (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (source : Fin 8 → Fin T) (word saved tmp queue carry ambient count : Fin T)
    (hparams : ∀ i, [source i,work (familyInverseScalarReg .wr),word,saved,tmp,queue].Nodup)
    (hcopy : [ambient,work 110,tmp,saved].Nodup)
    (hcount : [count,work (familyInverseCoreReg 246),saved].Nodup)
    (hambientOff : ∀ i, ambient ≠ work i) (hcountOff : ∀ i, count ≠ work i)
    (hscratchOff : ∀ i ∈ [word,saved,tmp,queue], ∀ j, i ≠ work j)
    (consumer : Fin 303 → Fin T) (dst clock : Fin T)
    (hemit : ∀ i, [work i,dst,tmp,saved].Nodup) (hclockDst : clock ≠ dst)
    (hclockOff : ∀ i, clock ≠ work i)
    (p u l target t : ℕ) (hst : s < t) (Fs : List (ZMod s → GaussianInt))
    (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![p,u,l,target,s,t,0,s] i)
    (hwidth : S.R (work (familyInverseScalarReg .wr)) =
      List.replicate (inverseCallerWordWidth p u l target s t) tick)
    (hblank : ∀ i, i ≠ familyInverseScalarReg .wr → S.R (work i) = [])
    (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ i ∈ [word,saved,tmp,queue], S.R i = [])
    (hambient : S.R ambient = cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten)
    (hN : (S.R count).length = Fs.length) (hclock : S.R clock = []) (depth : ℕ) :
    let B := inverseCallerWordWidth p u l target s t
    let xs := cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten
    let tape := descriptorScheduleTape consumer FamilyDispatchInput.words [fullLineGridRecord (A := A) p u l target t Fs]
    ∃ v' n F, v'.user = v.user ∧
      n ≤ (((p+u+l+target+s+t+0+s)*(4*B+10)+228*B+263)+(6*xs.length+6)+(4*Fs.length+4))+
        (11*tape.length+2) ∧
      F.R dst = tape++S.R dst ∧ F.R clock = [tick] ∧
      (∀ i, F.R (work i) = (fullLineGridRecord (A := A) p u l target t Fs).words i) ∧
      (∀ i, (∀ j, i ≠ work j) → i ≠ dst → i ≠ clock → F.R i = S.R i) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (((392*B+396)+(2*(6*xs.length+6)+2*(4*Fs.length+4)))+22*tape.length+4)) depth
        (generateFullLineDescriptor work source word saved tmp queue carry ambient count dst clock)
        (Host.mk v S) n (Host.mk v' F) := by
  dsimp only
  obtain ⟨v₁,n₁,M,hu₁,hn₁,hwords,hframe,hI,hO,hL,he₁⟩ := generateFullLineGridBank_exec
    (body := body) work hwork source word saved tmp queue carry ambient count hparams hcopy hcount
    hambientOff hcountOff hscratchOff p u l target t hst Fs v S hvalues hwidth hblank hleft hscratch hambient hN depth
  have hdstOff (i : Fin 303) : dst ≠ work i := by
    have hr := hemit i
    regs_ne hr
    exact Ne.symm ‹work i ≠ dst›
  have hdstM : M.R dst = S.R dst := hframe dst hdstOff
  have htmpM : M.R tmp = [] := (hframe tmp (hscratchOff tmp (by simp))).trans (hscratch tmp (by simp))
  have hsavedM : M.R saved = [] := (hframe saved (hscratchOff saved (by simp))).trans (hscratch saved (by simp))
  have hclockM : M.R clock = [] := (hframe clock hclockOff).trans hclock
  have htape := descriptorBankTape_sources_eq work consumer
    (fullLineGridRecord (A := A) p u l target t Fs).words M.R hwords
  change _ = descriptorBankTape (placedDescriptorFields consumer (fullLineGridRecord (A := A) p u l target t Fs).words) at htape
  let tape := descriptorScheduleTape consumer FamilyDispatchInput.words [fullLineGridRecord (A := A) p u l target t Fs]
  have htape' : descriptorBankTape ((List.ofFn work).map (fun i => (i,M.R i))) = tape := by
    simpa only [tape,descriptorScheduleTape,List.flatMap_cons,List.flatMap_nil,List.append_nil] using htape
  obtain ⟨v₂,hu₂,he₂⟩ := prepareDescriptorBank_exec (body := body) work dst tmp saved clock hemit hclockDst
    v₁ M htmpM hsavedM hclockM depth
  rw [htape'] at he₂
  let F : Stacks T A := {M with R := (Function.update (Function.update M.R dst (tape++M.R dst)) clock [tick])}
  have hwhole := mn_seq_within_add he₁ he₂
  have hcost := emitDescriptorBankCost_le M.R (List.ofFn work)
  rw [htape'] at hcost
  have hemitTime : emitDescriptorBankCost M.R (List.ofFn work)+1 ≤ 11*tape.length+2 := by omega
  have htime := Nat.add_le_add hn₁ hemitTime
  refine ⟨v₂,n₁+(emitDescriptorBankCost M.R (List.ofFn work)+1),F,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hu₂.trans hu₁
  · exact htime
  · simp only [F,Function.update_of_ne hclockDst.symm,Function.update_self,hdstM]
    rfl
  · simp only [F,Function.update_self]
  · intro i
    simp only [F,Function.update_of_ne (hclockOff i).symm,Function.update_of_ne (hdstOff i).symm,hwords]
  · intro i hi hd hc
    simp only [F,Function.update_of_ne hd,Function.update_of_ne hc]
    exact hframe i hi
  · exact hI
  · exact hO
  · exact hL
  · exact hwhole.mono (by intro d z hz; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
