module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedComponentInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! # Component preparation on packed halos

The existing component splitter already works on arbitrary lists. Remapping
its length counter to a private register separates physical length from the
ambient-period header, without copying or replacing that header at runtime.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def packedComponentReg (i : Fin 148) : Fin 149 :=
  if i = 121 then 148 else ⟨i.val,by omega⟩

theorem packedComponentReg_injective : Function.Injective packedComponentReg := by
  intro i j he
  have hv := congrArg Fin.val he
  simp only [packedComponentReg] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all <;> omega

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

def packedComponentInputs : Pr P 149 Q A U :=
  embProg packedComponentReg id retainedComponentInputs

theorem packedComponentInputs_exec {s : ℕ} (hA : 4 ≤ A) (a L w : ℕ)
    (F : ZMod s → GaussianInt) (hfit : a+L ≤ s)
    (tail : List (Fin (A+4))) (v : HS 149 Q A U) (S : Stacks 149 A)
    (hL : (S.R 148).length = L) (hw : (S.R 94).length = w)
    (hsrc : S.R 110 = cstream A w (packedInterval a L F)++tail)
    (hclean : ∀ i ∈ ([131,134,135,136,137,147] : List (Fin 149)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retainedComponentInputsCost L w ∧
      Exec (embTab packedComponentReg (embTab componentReg body)) packedComponentInputs
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R
          110 (cstream A w ((packedInterval a L F).map realPartWord)++tail))
          144 (cstream A w ((packedInterval a L F).map imagPartWord)++S.R 144))}) := by
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := retainedComponentInputs_exec (body := body) hA L w
    (packedInterval a L F) (packedInterval_length F hfit) tail
    (embDn packedComponentReg v) (embStk packedComponentReg S)
    (by simpa [embStk,packedComponentReg] using hL)
    (by simpa [embStk,packedComponentReg] using hw)
    (by simpa [embStk,packedComponentReg] using hsrc)
    (by simpa [embStk,packedComponentReg] using hclean 131 (by simp))
    (by simpa [embStk,packedComponentReg] using hclean 134 (by simp))
    (by simpa [embStk,packedComponentReg] using hclean 135 (by simp))
    (by simpa [embStk,packedComponentReg] using hclean 136 (by simp))
    (by simpa [embStk,packedComponentReg] using hclean 137 (by simp))
    (by simpa [embStk,packedComponentReg] using hclean 147 (by simp))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id)
    (body' := embTab packedComponentReg (embTab componentReg body))
    packedComponentReg_injective (fun _ => rfl) he₁ v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,?_⟩
  dsimp only [packedComponentInputs]
  convert he₂ using 1
  apply congrArg (mk v₂)
  let B := embStk packedComponentReg S
  let X := cstream A w ((packedInterval a L F).map realPartWord)++tail
  let Y := cstream A w ((packedInterval a L F).map imagPartWord)++B.R 144
  rw [embOvr_updR packedComponentReg_injective {B with R := Function.update B.R 110 X} S 144 Y,
    embOvr_updR packedComponentReg_injective B S 110 X,embOvr_stk]
  simp [X,Y,B,embStk,packedComponentReg]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
