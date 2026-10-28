module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorBankFacts
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! A fixed register placement loads its next bank from the physical packet tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def descriptorReadyBank (work : Fin 303 → Fin T) (words : Fin 303 → List (Fin (A+4)))
    (S : Stacks T A) : Stacks 303 A := {embStk work S with R := words}

def placedDescriptorFields (work : Fin N → Fin T) (words : Fin N → List (Fin (A+4))) :=
  List.ofFn (fun i => (work i,words i))

def placedDescriptorState (work : Fin N → Fin T) (words : Fin N → List (Fin (A+4)))
    (src saved : Fin T) (rest : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (descriptorBankR (placedDescriptorFields work words) S.R) src rest)
    saved ((descriptorBankTape (placedDescriptorFields work words)).reverse++S.R saved))}

def takePlacedDescriptorBank (work : Fin N → Fin T) (src saved count tmp spare : Fin T) : Pr P T Q A U :=
  takeDescriptorBank src saved count tmp spare (List.ofFn work)

theorem takePlacedDescriptorBank_exec (work : Fin N → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (words : Fin N → List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (rest : List (Fin (A+4))) (hsrc : S.R src = descriptorBankTape (placedDescriptorFields work words)++rest)
    (hblank : ∀ i, S.R (work i) = [])
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ takeDescriptorBankCost (placedDescriptorFields work words) ∧
      Exec body (takePlacedDescriptorBank work src saved count tmp spare) (mk v S) n
        (mk v' (placedDescriptorState work words src saved rest S)) ∧
      embStk work (placedDescriptorState work words src saved rest S) = {embStk work S with R := words} := by
  obtain ⟨v',n,hu,hn,he⟩ := takeDescriptorBank_exec (body := body) src saved count tmp spare hreg
    (placedDescriptorFields work words)
    (by intro f hf; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf; exact hsep i)
    v S rest hsrc hcount htmp hspare
  refine ⟨v',n,hu,hn,?_,?_⟩
  · simpa only [placedDescriptorFields,List.map_ofFn,Function.comp_def,placedDescriptorState,takePlacedDescriptorBank] using he
  · refine Stacks.ext rfl rfl rfl ?_
    funext i
    have hs : work i ≠ src := by intro he; exact hsep i (by simp [he])
    have hv : work i ≠ saved := by intro he; exact hsep i (by simp [he])
    change (placedDescriptorState work words src saved rest S).R (work i) = words i
    dsimp only [placedDescriptorState]
    rw [Function.update_of_ne hv,Function.update_of_ne hs]
    simpa only [placedDescriptorFields,hblank,List.append_nil] using descriptorBankR_ofFn work hwork words S.R i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
