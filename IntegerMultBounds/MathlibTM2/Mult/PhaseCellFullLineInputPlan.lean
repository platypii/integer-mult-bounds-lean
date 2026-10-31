module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateFullLineGridBank

/-! Static placement and ordinary inputs for one full-period RHS batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure FullLineInputPlan (T : ℕ) where
  work : Fin 303 → Fin T
  injective : Function.Injective work
  parameters : Fin 8 → Fin T
  word : Fin T
  saved : Fin T
  tmp : Fin T
  queue : Fin T
  carry : Fin T
  ambient : Fin T
  replicas : Fin T
  parameterRegs : ∀ i, [parameters i,work (familyInverseScalarReg .wr),word,saved,tmp,queue].Nodup
  copyRegs : [ambient,work 110,tmp,saved].Nodup
  countRegs : [replicas,work (familyInverseCoreReg 246),saved].Nodup
  ambientOff : ∀ i, ambient ≠ work i
  replicasOff : ∀ i, replicas ≠ work i
  scratchOff : ∀ k ∈ [word,saved,tmp,queue], ∀ i, k ≠ work i

namespace FullLineInputPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

structure Ready (plan : FullLineInputPlan T) (p u l target t : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (S : Stacks T A) : Prop where
  parameters : ∀ i, (S.R (plan.parameters i)).length = ![p,u,l,target,s,t,0,s] i
  width : S.R (plan.work (familyInverseScalarReg .wr)) =
    List.replicate (inverseCallerWordWidth p u l target s t) tick
  blank : ∀ i, i ≠ familyInverseScalarReg .wr → S.R (plan.work i) = []
  left : ∀ i, S.L (plan.work i) = []
  scratch : ∀ k ∈ [plan.word,plan.saved,plan.tmp,plan.queue], S.R k = []
  ambient : S.R plan.ambient = cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten
  replicas : (S.R plan.replicas).length = Fs.length

def generate (plan : FullLineInputPlan T) : Pr P T Q A U :=
  generateFamilyDispatchBank plan.work plan.parameters plan.word plan.saved plan.tmp plan.queue plan.carry plan.ambient plan.replicas

noncomputable def setupTime (p u l target s t N : ℕ) [NeZero s] : ℕ :=
  let B := inverseCallerWordWidth p u l target s t
  let volume := N*s*inverseFullInputWidth p u l target s t
  ((p+u+l+target+s+t+0+s)*(4*B+10)+228*B+263)+(6*volume+6)+(4*N+4)

noncomputable def setupStock (p u l target s t N : ℕ) [NeZero s] : ℕ :=
  let B := inverseCallerWordWidth p u l target s t
  let volume := N*s*inverseFullInputWidth p u l target s t
  (392*B+396)+(2*(6*volume+6)+2*(4*N+4))

theorem generate_exec (plan : FullLineInputPlan T) (p u l target t : ℕ) (hst : s < t)
    (Fs : List (ZMod s → GaussianInt)) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.Ready p u l target t Fs S) (depth : ℕ) :
    ∃ v' n F, v'.user = v.user ∧ n ≤ setupTime p u l target s t Fs.length ∧
      (∀ i, F.R (plan.work i) = (fullLineGridRecord (A := A) p u l target t Fs).words i) ∧
      (∀ i, (∀ j, i ≠ plan.work j) → F.R i = S.R i) ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+setupStock p u l target s t Fs.length)
        depth plan.generate (Host.mk v S) n (Host.mk v' F) := by
  obtain ⟨v',n,F,hu,hn,hwords,hframe,hI,hO,hL,he⟩ := generateFullLineGridBank_exec (body := body) plan.work plan.injective plan.parameters plan.word plan.saved plan.tmp
    plan.queue plan.carry plan.ambient plan.replicas plan.parameterRegs plan.copyRegs plan.countRegs
    plan.ambientOff plan.replicasOff plan.scratchOff p u l target t hst Fs v S hready.parameters
    hready.width hready.blank hready.left hready.scratch hready.ambient hready.replicas depth
  have hvolume : (cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten).length =
      Fs.length*s*inverseFullInputWidth p u l target s t := by
    simp only [length_cstream,List.length_flatten,List.map_map,Function.comp_def,length_chirpLine,
      List.map_const',List.sum_replicate,smul_eq_mul]
  rw [hvolume] at hn he
  exact ⟨v',n,F,hu,hn,hwords,hframe,hI,hO,hL,he⟩

end FullLineInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
