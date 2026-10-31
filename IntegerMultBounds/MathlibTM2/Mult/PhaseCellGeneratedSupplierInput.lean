module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallPackedFactoryStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedPublicationInput

/-! Generate the complete supplier input bank from retained ordinary headers
and a live local payload. No prepared numerical or outer bank is supplied. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace PublicationInputPlan
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def factoryWork (work : Fin 325 → Fin T) (i : Fin 242) : Fin T := work (Fin.castLE (by decide) i)

def fromHeaders (plan : PublicationInputPlan T) (work : Fin 325 → Fin T)
    (masters : Fin 10 → Fin T) (parameters : Fin 8 → Fin T) (width core word span : Fin T) : Pr P T Q A U :=
  .seq (installPackedFactory (factoryWork work) masters (plan.retained 1) span (plan.retained 7) (plan.retained 8) (plan.retained 8))
    (plan.normalized work parameters width core word)

theorem fromHeaders_exec (plan : PublicationInputPlan T) (work : Fin 325 → Fin T)
    (hwork : Function.Injective work) (hprefix : ∀ i, work (Fin.castLE (by decide : 276 ≤ 325) i) = plan.work i)
    (masters : Fin 10 → Fin T) (parameters : Fin 8 → Fin T) (width core word span : Fin T)
    (hmasterOff : ∀ i j, masters i ≠ work j) (hmasterTmp : ∀ i, masters i ≠ plan.retained 7)
    (hretainedOff : ∀ i j, plan.retained i ≠ work j)
    (hspanOff : ∀ j, span ≠ work j)
    (hgeometry : [masters 8,masters 9,plan.retained 1,factoryWork work 155,factoryWork work 165,
      factoryWork work 163,span,plan.retained 7,plan.retained 8].Nodup)
    (hborrow : ∀ i ∈ width::core::word::plan.retained 8::plan.retained 7::List.ofFn parameters, ∀ j, i ≠ work j)
    (hcore : [core,width,work 277,plan.retained 8,plan.retained 7].Nodup)
    (hparams : ∀ i, [parameters i,width,word,plan.retained 8,plan.retained 7,work 324].Nodup)
    (precision stage q band p W N packet radius V u l target s t a b B L : ℕ)
    (xs : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hblankWork : ∀ i, S.R (work i) = []) (hleftWork : ∀ i, S.L (work i) = [])
    (hmasters : ∀ i, (S.R (masters i)).length = masterHeaderValues precision stage q l s t u band a b i)
    (hradius : (S.R (plan.retained 0)).length = radius)
    (hwidthV : (S.R (plan.retained 1)).length = V)
    (hvalues : ∀ i, (S.R (plan.headers i)).length = ![N,W,p,packet] i)
    (hpayload : S.R (plan.retained 6) = xs)
    (htmp : S.R (plan.retained 7) = []) (hsaved : S.R (plan.retained 8) = []) (hspan : S.R span = [])
    (hparameters : ∀ i, (S.R (parameters i)).length = ![p,u,l,target,s,t,a,b] i)
    (hwidthB : (S.R width).length = B) (hlen : (S.R core).length = L)
    (hword : S.R word = []) (depth : ℕ) :
    let masterCopies := masterHeaderCopies (factoryWork work ∘ packedFactoryNativeReg) masters
    let headerCopies := descriptorHeaderCopies plan.work plan.headers
    let value := fun i => (S.R i).length
    let native := packedFactoryInputBank (embStk (factoryWork work) S) precision stage q l s t u band a b V
    let M := packedKeyDescriptorInput (packedKeyPublicationInput native V radius) p W N packet xs
    let ps := (inverseParameterWords p u l target s t a b).flatMap (fun r => binSyms B r.2)
    ∃ v' n F, v'.user = v.user ∧
      n ≤ (copyUnaryHeadersCost value masterCopies+factoryGeometryCost a b V)+
        ((radius*(4*V+10)+4*V+8+(copyUnaryHeadersCost value headerCopies+(6*xs.length+6)))+
          ((L+p+u+l+target+s+t+a+b)*(4*B+10)+72*B+109)) ∧
      embStk work F = packedNormalizedInputBank M B L (List.replicate B tick) ps ∧
      (∀ i, (∀ j, i ≠ work j) → F.R i = S.R i) ∧ F.L = S.L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((2*copyUnaryHeadersCost value masterCopies+(8*a+8*b+24*V+40))+
          ((2*(4*V+4)+(2*copyUnaryHeadersCost value headerCopies+2*(6*xs.length+6)))+10*(2*(4*B+4))))) depth
        (plan.fromHeaders work masters parameters width core word span) (Host.mk v S) n (Host.mk v' F) := by
  dsimp only
  have hn : Function.Injective (factoryWork work) := by
    intro i j he
    exact Fin.ext (congrArg (fun x : Fin 325 => x.val) (hwork he))
  have hpref : ∀ i, work (Fin.castLE (by decide : 242 ≤ 325) i) = factoryWork work i := fun _ => rfl
  obtain ⟨v₁,n₁,hu₁,hn₁,hbank,he₁⟩ := installPackedFactory_exec_within (body := body)
    (factoryWork work) hn masters (plan.retained 1) span (plan.retained 7) (plan.retained 8) (plan.retained 8)
    (fun i j => hmasterOff i _) hmasterTmp (fun i => (hretainedOff 7 _).symm) hgeometry
    precision stage q l s t u band a b V v S hmasters hwidthV (fun i => hretainedOff 1 _)
    (fun i => hblankWork _) (fun i => hleftWork _)
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl <;> assumption)
    (by intro i hi j; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl | rfl | rfl
        · exact hspanOff _
        · exact hretainedOff 7 _
        · exact hretainedOff 8 _) depth
  let rs := masterHeaderCopies (factoryWork work ∘ packedFactoryNativeReg) masters
  let H₀ : Stacks T A := {S with R := unaryCopiesR (fun i => (S.R i).length) S.R rs}
  let H : Stacks T A := {H₀ with R := (Function.update (Function.update (Function.update H₀.R
    (factoryWork work 163) (List.replicate V tick)) (factoryWork work 155) (binSyms V a))
    (factoryWork work 165) (binSyms V (b-a)))}
  have hframe (i : Fin T) (hi : ∀ j, i ≠ factoryWork work j) : H.R i = S.R i := by
    change Function.update (Function.update (Function.update H₀.R _ _) _ _) _ _ i = _
    rw [Function.update_of_ne (hi 165),Function.update_of_ne (hi 155),Function.update_of_ne (hi 163)]
    apply unaryCopiesR_off
    intro r hr he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact hi _ he.symm
  have hlarge : embStk work H = extendStacks (by decide : 242 ≤ 325)
      (packedFactoryInputBank (embStk (factoryWork work) S) precision stage q l s t u band a b V) :=
    embStk_extend_of_frame (by decide) (factoryWork work) work hwork hpref S H _ hbank
      (fun i hi => ⟨hleftWork i,hblankWork i⟩) rfl hframe
  have hretained (i : Fin 9) : H.R (plan.retained i) = S.R (plan.retained i) :=
    hframe _ (fun j => hretainedOff i _)
  have hborrowFrame (i : Fin T)
      (hi : i ∈ width::core::word::plan.retained 8::plan.retained 7::List.ofFn parameters) : H.R i = S.R i :=
    hframe _ (fun j => hborrow i hi _)
  obtain ⟨v₂,n₂,F,hu₂,hn₂,hbank₂,hframe₂,hleft₂,he₂⟩ := plan.normalized_exec (body := body)
    work hwork hprefix parameters width core word hborrow hcore hparams
    p W N packet radius V u l target s t a b B L xs v₁ H
    (packedFactoryInputBank (embStk (factoryWork work) S) precision stage q l s t u band a b V) hlarge
    (by rw [hretained]; exact hradius) (by rw [hretained]; exact hwidthV)
    (by intro i; simpa only [headers,hretained] using hvalues i)
    (by rw [hretained]; exact hpayload) (by rw [hretained]; exact htmp) (by rw [hretained]; exact hsaved)
    (by
      intro i
      have hi : parameters i ∈ List.ofFn parameters := List.mem_ofFn.mpr ⟨i,rfl⟩
      rw [hborrowFrame _ (List.mem_append_right [width,core,word,plan.retained 8,plan.retained 7] hi)]
      exact hparameters i)
    (by rw [hborrowFrame width (by simp)]; exact hwidthB)
    (by rw [hborrowFrame core (by simp)]; exact hlen)
    (by rw [hborrowFrame word (by simp)]; exact hword) depth
  have hcost : copyUnaryHeadersCost (fun i => (H.R i).length) (descriptorHeaderCopies plan.work plan.headers) =
      copyUnaryHeadersCost (fun i => (S.R i).length) (descriptorHeaderCopies plan.work plan.headers) := by
    unfold copyUnaryHeadersCost descriptorHeaderCopies
    simp only [List.map_ofFn,Function.comp_def,headers,hretained]
  rw [hcost] at hn₂ he₂
  have hwhole := mn_seq_within_add he₁ he₂
  refine ⟨v₂,n₁+n₂,F,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hbank₂,?_,hleft₂,hwhole⟩
  intro i hi
  rw [hframe₂ i hi]
  exact hframe i (fun j => hi _)

end PublicationInputPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
