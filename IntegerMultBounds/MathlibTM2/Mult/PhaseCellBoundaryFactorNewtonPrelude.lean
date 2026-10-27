module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorNewtonBudget

/-! Build the Newton digit-count operand from retained masters, releasing the intermediate dimensions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryFactorNewtonPreludeOps : List (UnarySetup.Op 224) :=
  [.div 128 117 184 0, .add 1 119 223 0, .push 223 1,
   .mul 184 223 221 0 1, .clear 184, .clear 223]

def boundaryFactorNewtonPrelude : Pr P 224 Q A U := UnarySetup.program boundaryFactorNewtonPreludeOps

def boundaryFactorNewtonPreludeCost (p q : ℕ) : ℕ :=
  (4*(2^15*p)+4)+(4*q+4)+1+(256*p*(4*(q+1)+9)+4)+(2*(256*p)+2)+(2*(q+1)+2)+1

private theorem newton_master_div (p : ℕ) : (32768*p)/128 = 256*p := by
  norm_num
  omega

theorem boundaryFactorNewtonPrelude_exec (p q : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hp : (S.R 117).length = 2^15*p) (hq : (S.R 119).length = q)
    (h0 : S.R 0 = []) (h1 : S.R 1 = [])
    (h184 : S.R 184 = []) (h223 : S.R 223 = []) (h221 : S.R 221 = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ boundaryFactorNewtonPreludeCost p q ∧
      Exec body boundaryFactorNewtonPrelude (mk v S) steps
        (mk v' {S with R := Function.update S.R 221 (List.replicate (256*p*(q+1)) tick)}) := by
  have hready : UnarySetup.Ready boundaryFactorNewtonPreludeOps S.R := by
    simp [boundaryFactorNewtonPreludeOps,UnarySetup.Ready,UnarySetup.Op.Ready,UnarySetup.Op.runR,h0,h1]
  obtain ⟨v',steps,hu,hs,he⟩ := UnarySetup.exec (body := body) boundaryFactorNewtonPreludeOps v S hready
  have hcost : UnarySetup.cost boundaryFactorNewtonPreludeOps S.R = boundaryFactorNewtonPreludeCost p q := by
    simp [boundaryFactorNewtonPreludeOps,UnarySetup.cost,UnarySetup.Op.cost,UnarySetup.Op.runR,
      boundaryFactorNewtonPreludeCost,h184,h223,h221,hp,hq,newton_master_div,Nat.add_assoc]
    omega
  have hR : UnarySetup.runR boundaryFactorNewtonPreludeOps S.R =
      Function.update S.R 221 (List.replicate (256*p*(q+1)) tick) := by
    funext i
    by_cases hi184 : i = 184 <;> by_cases hi223 : i = 223 <;> by_cases hi221 : i = 221 <;>
      simp [boundaryFactorNewtonPreludeOps,UnarySetup.runR,UnarySetup.Op.runR,h184,h223,h221,
        hp,hq,newton_master_div,hi184,hi223,hi221]
  exact ⟨v',steps,hu,hcost ▸ hs,by simpa only [boundaryFactorNewtonPrelude,hR] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
