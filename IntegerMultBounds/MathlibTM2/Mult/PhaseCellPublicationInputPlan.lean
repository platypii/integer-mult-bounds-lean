module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratePublicationFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateDescriptorFrame
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Compose publication and descriptor setup with one injective placement.
The retained bank holds radius, width, four ordinary headers, payload and scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure PublicationInputPlan (T : ℕ) where
  reg : Fin 285 → Fin T
  injective : Function.Injective reg

namespace PublicationInputPlan
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def work (plan : PublicationInputPlan T) (i : Fin 276) : Fin T := plan.reg (Fin.castAdd 9 i)
def retained (plan : PublicationInputPlan T) (i : Fin 9) : Fin T := plan.reg (Fin.natAdd 276 i)
def headers (plan : PublicationInputPlan T) (i : Fin 4) : Fin T := plan.retained ⟨2+i.val,by omega⟩

theorem work_injective (plan : PublicationInputPlan T) : Function.Injective plan.work := by
  intro i j he
  exact Fin.ext (congrArg (fun x : Fin 285 => x.val) (plan.injective he))

theorem retained_off (plan : PublicationInputPlan T) (i : Fin 9) (j : Fin 276) :
    plan.retained i ≠ plan.work j := by
  intro he
  have hv := congrArg (fun x : Fin 285 => x.val) (plan.injective he)
  have hj := j.isLt
  change 276+i.val = j.val at hv
  omega

def program (plan : PublicationInputPlan T) : Pr P T Q A U :=
  .seq (toBinary (plan.retained 0) (plan.retained 1) (plan.work 252) (plan.retained 8) (plan.retained 7) (plan.retained 8))
    (generateDescriptorFrame plan.work plan.headers (plan.retained 6) (plan.retained 7) (plan.retained 8))

private theorem extend_trans (S : Stacks 242 A) :
    extendStacks (by decide : 263 ≤ 276) (extendStacks (by decide : 242 ≤ 263) S) =
      extendStacks (by decide : 242 ≤ 276) S := by
  refine Stacks.ext rfl rfl ?_ ?_
  all_goals
    funext i
    simp only [extendStacks]
    split_ifs <;> first | rfl | omega

theorem exec (plan : PublicationInputPlan T) (p W N packet radius V : ℕ)
    (xs : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A) (M : Stacks 242 A)
    (hview : embStk plan.work S = extendStacks (by decide : 242 ≤ 276) M)
    (hradius : (S.R (plan.retained 0)).length = radius)
    (hwidth : (S.R (plan.retained 1)).length = V)
    (hvalues : ∀ i, (S.R (plan.headers i)).length = ![N,W,p,packet] i)
    (hpayload : S.R (plan.retained 6) = xs)
    (htmp : S.R (plan.retained 7) = []) (hsaved : S.R (plan.retained 8) = []) (depth : ℕ) :
    let rs := descriptorHeaderCopies plan.work plan.headers
    let value := fun i => (S.R i).length
    ∃ v' n F, v'.user = v.user ∧
      n ≤ radius*(4*V+10)+4*V+8+(copyUnaryHeadersCost value rs+(6*xs.length+6)) ∧
      embStk plan.work F = packedKeyDescriptorInput (packedKeyPublicationInput M V radius) p W N packet xs ∧
      (∀ i, (∀ j, i ≠ plan.work j) → F.R i = S.R i) ∧ F.L = S.L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (2*(4*V+4)+(2*copyUnaryHeadersCost value rs+2*(6*xs.length+6)))) depth plan.program (Host.mk v S) n (Host.mk v' F) := by
  dsimp only
  have hreg : [plan.retained 0,plan.retained 1,plan.work 252,plan.retained 8,plan.retained 7].Nodup := by
    change ([276,277,252,284,283] : List (Fin 285)).map plan.reg |>.Nodup
    exact List.Nodup.map plan.injective (by decide)
  have hblank : S.R (plan.work 252) = [] := by
    have hv := congrArg (fun C : Stacks 276 A => C.R 252) hview
    exact hv.trans (extendStacks_fresh (by decide : 242 ≤ 276) M 252 (by decide)).2
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toBinary_exec_within (body := body) hreg (plan.retained 8) v S hblank hsaved htmp depth
  rw [hradius,hwidth] at hn₁ he₁
  let H : Stacks T A := {S with R := Function.update S.R (plan.work 252) (binSyms V radius)}
  have hframe (i : Fin 9) : H.R (plan.retained i) = S.R (plan.retained i) :=
    Function.update_of_ne (plan.retained_off i 252) _ _
  have hH : embStk plan.work H = extendStacks (by decide : 263 ≤ 276) (packedKeyPublicationInput M V radius) := by
    rw [embStk_updateR plan.work_injective,hview]
    unfold packedKeyPublicationInput
    rw [extendStacks_updateR,extend_trans]
    rfl
  have hcopy : [plan.retained 6,plan.work 263,plan.retained 7,plan.retained 8].Nodup := by
    change ([282,263,283,284] : List (Fin 285)).map plan.reg |>.Nodup
    exact List.Nodup.map plan.injective (by decide)
  obtain ⟨v₂,hu₂,hbank,he₂⟩ := generateDescriptorFrame_exec (body := body) plan.work plan.work_injective
    plan.headers (plan.retained 6) (plan.retained 7) (plan.retained 8)
    (fun i j => plan.retained_off _ _) (by
      intro i he
      have hv := congrArg (fun x : Fin 285 => x.val) (plan.injective he)
      have hi := i.isLt
      change 276+(2+i.val) = 276+8 at hv
      omega)
    (fun i => plan.retained_off _ _) (fun i => plan.retained_off _ _) hcopy (fun i => plan.retained_off _ _)
    p W N packet xs v₁ H (packedKeyPublicationInput M V radius) hH
    (by intro i; simpa only [headers,hframe] using hvalues i)
    (by rw [hframe]; exact hpayload) (by rw [hframe]; exact htmp) (by rw [hframe]; exact hsaved) depth
  have hcost : copyUnaryHeadersCost (fun i => (H.R i).length) (descriptorHeaderCopies plan.work plan.headers) =
      copyUnaryHeadersCost (fun i => (S.R i).length) (descriptorHeaderCopies plan.work plan.headers) := by
    unfold copyUnaryHeadersCost descriptorHeaderCopies
    simp only [List.map_ofFn,Function.comp_def,headers,hframe]
  rw [hcost] at he₂
  have hwhole := mn_seq_within_add he₁ he₂
  refine ⟨v₂,n₁+(copyUnaryHeadersCost (fun i => (S.R i).length) (descriptorHeaderCopies plan.work plan.headers)+(6*xs.length+6)),_,hu₂.trans hu₁,by omega,hbank,?_,rfl,hwhole⟩
  intro i hi
  change Function.update (unaryCopiesR (fun j => (H.R j).length) H.R
    (descriptorHeaderCopies plan.work plan.headers)) (plan.work 263) xs i = _
  rw [Function.update_of_ne (hi 263)]
  rw [unaryCopiesR_off _ _ _ _ (by
    intro r hr he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact hi _ he.symm)]
  exact Function.update_of_ne (hi 252) _ _

end PublicationInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
