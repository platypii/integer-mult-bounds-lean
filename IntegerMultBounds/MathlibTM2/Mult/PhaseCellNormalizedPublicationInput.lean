module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationInputPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateNormalizedFrame
public import IntegerMultBounds.MathlibTM2.Host.ExtendFrame

/-! One physical input setup from the native factory bank to all outer words.
Publication, payload installation and normalization share restored scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace PublicationInputPlan
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def normalized (plan : PublicationInputPlan T) (work : Fin 325 → Fin T)
    (parameters : Fin 8 → Fin T) (width core word : Fin T) : Pr P T Q A U :=
  .seq plan.program (generateNormalizedFrame work parameters width core word
    (plan.retained 8) (plan.retained 7) (plan.retained 8))

theorem normalized_exec (plan : PublicationInputPlan T) (work : Fin 325 → Fin T)
    (hwork : Function.Injective work) (hprefix : ∀ i, work (Fin.castLE (by decide : 276 ≤ 325) i) = plan.work i)
    (parameters : Fin 8 → Fin T) (width core word : Fin T)
    (hborrow : ∀ i ∈ width::core::word::plan.retained 8::plan.retained 7::List.ofFn parameters, ∀ j, i ≠ work j)
    (hcore : [core,width,work 277,plan.retained 8,plan.retained 7].Nodup)
    (hparams : ∀ i, [parameters i,width,word,plan.retained 8,plan.retained 7,work 324].Nodup)
    (p W N packet radius V u l target s t a b B L : ℕ)
    (xs : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A) (M : Stacks 242 A)
    (hview : embStk work S = extendStacks (by decide : 242 ≤ 325) M)
    (hradius : (S.R (plan.retained 0)).length = radius)
    (hwidthV : (S.R (plan.retained 1)).length = V)
    (hvalues : ∀ i, (S.R (plan.headers i)).length = ![N,W,p,packet] i)
    (hpayload : S.R (plan.retained 6) = xs)
    (htmp : S.R (plan.retained 7) = []) (hsaved : S.R (plan.retained 8) = [])
    (hparameters : ∀ i, (S.R (parameters i)).length = ![p,u,l,target,s,t,a,b] i)
    (hwidthB : (S.R width).length = B) (hlen : (S.R core).length = L)
    (hword : S.R word = []) (depth : ℕ) :
    let rs := descriptorHeaderCopies plan.work plan.headers
    let value := fun i => (S.R i).length
    let M' := packedKeyDescriptorInput (packedKeyPublicationInput M V radius) p W N packet xs
    let ps := (inverseParameterWords p u l target s t a b).flatMap (fun r => binSyms B r.2)
    ∃ v' n F, v'.user = v.user ∧
      n ≤ (radius*(4*V+10)+4*V+8+(copyUnaryHeadersCost value rs+(6*xs.length+6)))+
        ((L+p+u+l+target+s+t+a+b)*(4*B+10)+72*B+109) ∧
      embStk work F = packedNormalizedInputBank M' B L (List.replicate B tick) ps ∧
      (∀ i, (∀ j, i ≠ work j) → F.R i = S.R i) ∧ F.L = S.L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((2*(4*V+4)+(2*copyUnaryHeadersCost value rs+2*(6*xs.length+6)))+10*(2*(4*B+4)))) depth
        (plan.normalized work parameters width core word) (Host.mk v S) n (Host.mk v' F) := by
  dsimp only
  have hsmall : embStk plan.work S = extendStacks (by decide : 242 ≤ 276) M := by
    rw [← embStk_prefix_eq (by decide : 276 ≤ 325) plan.work work hprefix,hview]
    exact embStk_extend_prefix (by decide : 242 ≤ 276) (by decide : 276 ≤ 325) M
  obtain ⟨v₁,n₁,F,hu₁,hn₁,hbank,hframe,hleft,he₁⟩ := plan.exec (body := body)
    p W N packet radius V xs v S M hsmall hradius hwidthV hvalues hpayload htmp hsaved depth
  have hlarge : embStk work F = extendStacks (by decide : 276 ≤ 325)
      (packedKeyDescriptorInput (packedKeyPublicationInput M V radius) p W N packet xs) := by
    apply embStk_extend_of_frame (by decide : 276 ≤ 325) plan.work work hwork hprefix S F _ hbank _ hleft hframe
    intro i hi
    have hvL := congrArg (fun C : Stacks 325 A => C.L i) hview
    have hvR := congrArg (fun C : Stacks 325 A => C.R i) hview
    have hb := extendStacks_fresh (by decide : 242 ≤ 325) M i (by omega)
    exact ⟨hvL.trans hb.1,hvR.trans hb.2⟩
  have hretained (i : Fin T)
      (hi : i ∈ width::core::word::plan.retained 8::plan.retained 7::List.ofFn parameters) : F.R i = S.R i := by
    apply hframe i
    intro j he
    exact hborrow i hi _ (he.trans (hprefix j).symm)
  have hblank : ∀ i ∈ [word,plan.retained 8,plan.retained 7], F.R i = [] := by
    intro i hi
    have hi' := List.mem_cons_of_mem width (List.mem_cons_of_mem core (List.mem_append_left (List.ofFn parameters) hi))
    rw [hretained i hi']
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact hword
    · exact hsaved
    · exact htmp
  obtain ⟨v₂,n₂,hu₂,hn₂,hbank₂,he₂⟩ := generateNormalizedFrame_exec (body := body)
    work hwork parameters width core word (plan.retained 8) (plan.retained 7) (plan.retained 8)
    hborrow hcore hparams p u l target s t a b B L v₁ F
    (packedKeyDescriptorInput (packedKeyPublicationInput M V radius) p W N packet xs) hlarge
    (by
      intro i
      have hi : parameters i ∈ List.ofFn parameters := List.mem_ofFn.mpr ⟨i,rfl⟩
      rw [hretained (parameters i) (List.mem_append_right [width,core,word,plan.retained 8,plan.retained 7] hi)]
      exact hparameters i)
    (by rw [hretained width (by simp)]; exact hwidthB)
    (by rw [hretained core (by simp)]; exact hlen) hblank depth
  have hwhole := mn_seq_within_add he₁ he₂
  refine ⟨v₂,n₁+n₂,_,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hbank₂,?_,hleft,hwhole⟩
  intro i hi
  change Function.update (Function.update (Function.update F.R
    (work (packedNormalizedScalarReg .wr)) (List.replicate B tick)) (work 277) (binSyms B L))
    (work 324) _ i = _
  rw [Function.update_of_ne (hi 324),Function.update_of_ne (hi 277),Function.update_of_ne (hi _)]
  apply hframe i
  intro j he
  exact hi _ (he.trans (hprefix j).symm)

end PublicationInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
