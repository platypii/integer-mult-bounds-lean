module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectWeightKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedProcessHaloLengthKey

/-! Place the cached class caller below the family queue, saved header and completed packets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

def weightFamilyCoreReg (i : Fin 148) : Fin 151 := ⟨i.val,by omega⟩

theorem weightFamilyCoreReg_injective : Function.Injective weightFamilyCoreReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 151 => k.val) h)

theorem weightFamilyCoreReg_off (i : Fin 151) (hi : 148 ≤ i.val) :
    ∀ j, weightFamilyCoreReg j ≠ i := by
  intro j he
  have hv := congrArg (fun k : Fin 151 => k.val) he
  dsimp [weightFamilyCoreReg] at hv
  omega

def loadedWeightKeyBank {A : ℕ} (S : Stacks 151 A) (page rest : List (Fin (A+4))) : Stacks 151 A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    148 rest) 144 page) 145 (List.replicate page.length tick)) 149 (blank::List.replicate page.length tick))}

def collectedWeightKeyBank {A : ℕ} (S : Stacks 151 A) (page : List (Fin (A+4))) : Stacks 151 A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    144 []) 145 []) 149 []) 150 ((weightKeyPacket page).reverse++S.R 150))}

theorem loadedWeightKeyBank_project {A : ℕ} (S : Stacks 151 A) (page rest : List (Fin (A+4))) :
    embStk weightFamilyCoreReg (loadedWeightKeyBank S page rest) =
      {embStk weightFamilyCoreReg S with R := (Function.update
        (Function.update (embStk weightFamilyCoreReg S).R 144 page) 145 (List.replicate page.length tick))} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have h148 : i.val ≠ 148 := by omega
  have h149 : i.val ≠ 149 := by omega
  simp [loadedWeightKeyBank,embStk,weightFamilyCoreReg,Function.update_apply,Fin.ext_iff,h148,h149]

theorem loadedWeightKeyBank_low {A : ℕ} (S : Stacks 151 A) (page rest : List (Fin (A+4)))
    (i : Fin 148) (hi : i.val < 144) :
    (embStk weightFamilyCoreReg (loadedWeightKeyBank S page rest)).R i = (embStk weightFamilyCoreReg S).R i := by
  rw [loadedWeightKeyBank_project]
  have h144 : i ≠ (144 : Fin 148) := by intro he; subst i; norm_num at hi
  have h145 : i ≠ (145 : Fin 148) := by intro he; subst i; norm_num at hi
  simp [h144,h145]

theorem collectedWeightKeyBank_projectR {A : ℕ} (S : Stacks 151 A) (page : List (Fin (A+4))) :
    (embStk weightFamilyCoreReg (collectedWeightKeyBank S page)).R =
      Function.update (Function.update (embStk weightFamilyCoreReg S).R 144 []) 145 [] := by
  funext i
  have h149 : i.val ≠ 149 := by omega
  have h150 : i.val ≠ 150 := by omega
  simp [collectedWeightKeyBank,embStk,weightFamilyCoreReg,Function.update_apply,Fin.ext_iff,h149,h150]

theorem weightFamily_release_published {A : ℕ} (R : Regs 148 A)
    (page clock keys published : List (Fin (A+4))) (h144 : R 144 = []) (h145 : R 145 = []) :
    Function.update (Function.update
      (publishedClassR (Function.update (Function.update (Function.update R 144 page) 145 clock) 126 keys) published)
      144 []) 145 [] = publishedClassR (Function.update R 126 keys) published := by
  funext i
  by_cases hi144 : i = 144 <;> by_cases hi145 : i = 145 <;>
    simp [publishedClassR,Function.update_apply,hi144,hi145,h144,h145]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
