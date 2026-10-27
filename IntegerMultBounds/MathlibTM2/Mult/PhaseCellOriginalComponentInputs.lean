module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalInputReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedComponentInputs

/-! Preserve the original complex line and prepare both real component inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def originalComponentInputs : Pr P₀ 148 Q A U :=
  .seq saveOriginalInput preparedComponentInputs

def originalComponentInputsCost (q s : ℕ) : ℕ :=
  saveOriginalInputCost q s+preparedComponentInputsCost q s

theorem originalComponentInputs_exec {P N q l s t u band : ℕ} [NeZero s]
    (hA : 4 ≤ A) (F : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P N q l s t u band 0 0
      (cstream A (2*q+8) (chirpLine s F)++tail) (embStk componentReg S))
    (h147 : S.R 147 = []) :
    let X := cstream A (2*q+8) (chirpLine s (fun i => realPartWord (F i)))++tail
    let Y := cstream A (2*q+8) (chirpLine s (fun i => imagPartWord (F i)))++S.R 144
    let O := cstream A (2*q+8) (chirpLine s F)++S.R 146
    let S' : Stacks 148 A := {S with R := Function.update (Function.update (Function.update S.R 146 O) 110 X) 144 Y}
    ∃ v' n, v'.user = v.user ∧ n ≤ originalComponentInputsCost q s ∧
      Exec (embTab componentReg body) originalComponentInputs (mk v S) n (mk v' S') ∧
      LengthKeyReady P N q l s t u band 0 0 X (embStk componentReg S') := by
  dsimp only
  let raw := cstream A (2*q+8) (chirpLine s F)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hready₁⟩ := saveOriginalInput_ready (body := body)
    raw tail (by simp [raw,chirpLine]) v S hready h147
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 146 (raw++S.R 146)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hready₂⟩ := preparedComponentInputs_exec (body := body)
    hA F tail v₁ S₁ hready₁ (by simpa [S₁] using h147)
  have hreal : (chirpLine s F).map realPartWord = chirpLine s (fun i => realPartWord (F i)) := by
    simp [chirpLine,List.map_map,Function.comp_def]
  have himag : (chirpLine s F).map imagPartWord = chirpLine s (fun i => imagPartWord (F i)) := by
    simp [chirpLine,List.map_map,Function.comp_def]
  simp only [hreal,himag] at he₂ hready₂
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_,?_⟩
  · exact Exec.seq he₁ he₂
  · exact hready₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
