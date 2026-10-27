module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorMultiplierSetup

/-! Generate every factor dimension except the Newton iteration count from retained masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryFactorDimensionOps : List (UnarySetup.Op 224) :=
  [.add 12 124 185 0, .add 1 185 187 0, .push 187 1,
   .add 2 187 190 0, .add 1 116 192 0,
   .mul 185 160 189 0 1, .mul 190 160 188 0 1,
   .add 1 188 193 0, .add 1 160 193 0,
   .add 1 187 223 0, .push 223 1, .mul 223 193 194 0 1, .clear 223]

def boundaryFactorDimensionPorts : List (Fin 224) := [185,187,190,192,189,188,193,194,223]

def boundaryFactorDimensions : Pr P 224 Q A U := UnarySetup.program boundaryFactorDimensionOps

def boundaryFactorDimensionsCost (band N w : ℕ) : ℕ :=
  let k := 12*band
  let W := k+1
  (4*band+4)+(4*k+4)+1+(4*W+4)+(4*N+4)+
    (k*(4*w+9)+4)+(2*W*(4*w+9)+4)+(4*(2*W*w)+4)+(4*w+4)+
    (4*W+4)+1+((W+1)*(4*((2*W+1)*w)+9)+4)+(2*(W+1)+2)+1

theorem boundaryFactorDimensionOps_ready (R : Regs 224 A) (h0 : R 0 = []) (h1 : R 1 = []) :
    UnarySetup.Ready boundaryFactorDimensionOps R := by
  simp [boundaryFactorDimensionOps,UnarySetup.Ready,UnarySetup.Op.Ready,UnarySetup.Op.runR,h0,h1]

theorem boundaryFactorDimensions_lengths (band N w : ℕ) (R : Regs 224 A)
    (hband : (R 124).length = band) (hN : (R 116).length = N) (hw : (R 160).length = w)
    (hblank : ∀ r ∈ boundaryFactorDimensionPorts, R r = []) :
    let R' := UnarySetup.runR boundaryFactorDimensionOps R
    (R' 185).length = 12*band ∧ (R' 187).length = 12*band+1 ∧
    (R' 190).length = 2*(12*band+1) ∧ (R' 192).length = N ∧
    (R' 189).length = (12*band)*w ∧ (R' 188).length = 2*(12*band+1)*w ∧
    (R' 193).length = (2*(12*band+1)+1)*w ∧
    (R' 194).length = (12*band+1+1)*(2*(12*band+1)+1)*w ∧ R' 223 = [] := by
  have h185 := hblank 185 (by simp [boundaryFactorDimensionPorts])
  have h187 := hblank 187 (by simp [boundaryFactorDimensionPorts])
  have h190 := hblank 190 (by simp [boundaryFactorDimensionPorts])
  have h192 := hblank 192 (by simp [boundaryFactorDimensionPorts])
  have h189 := hblank 189 (by simp [boundaryFactorDimensionPorts])
  have h188 := hblank 188 (by simp [boundaryFactorDimensionPorts])
  have h193 := hblank 193 (by simp [boundaryFactorDimensionPorts])
  have h194 := hblank 194 (by simp [boundaryFactorDimensionPorts])
  have h223 := hblank 223 (by simp [boundaryFactorDimensionPorts])
  simp [boundaryFactorDimensionOps,UnarySetup.runR,UnarySetup.Op.runR,h185,h187,h190,h192,h189,h188,h193,h194,h223,
    hband,hN,hw,Nat.mul_assoc,Nat.add_mul,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem boundaryFactorDimensions_exec (band N w : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hband : (S.R 124).length = band) (hN : (S.R 116).length = N) (hw : (S.R 160).length = w)
    (h0 : S.R 0 = []) (h1 : S.R 1 = [])
    (hblank : ∀ r ∈ boundaryFactorDimensionPorts, S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryFactorDimensionsCost band N w ∧
      Exec body boundaryFactorDimensions (mk v S) n
        (mk v' {S with R := UnarySetup.runR boundaryFactorDimensionOps S.R}) := by
  obtain ⟨v',n,hu,hn,he⟩ := UnarySetup.exec (body := body) boundaryFactorDimensionOps v S
    (boundaryFactorDimensionOps_ready S.R h0 h1)
  have h185 := hblank 185 (by simp [boundaryFactorDimensionPorts])
  have h187 := hblank 187 (by simp [boundaryFactorDimensionPorts])
  have h190 := hblank 190 (by simp [boundaryFactorDimensionPorts])
  have h192 := hblank 192 (by simp [boundaryFactorDimensionPorts])
  have h189 := hblank 189 (by simp [boundaryFactorDimensionPorts])
  have h188 := hblank 188 (by simp [boundaryFactorDimensionPorts])
  have h193 := hblank 193 (by simp [boundaryFactorDimensionPorts])
  have h194 := hblank 194 (by simp [boundaryFactorDimensionPorts])
  have h223 := hblank 223 (by simp [boundaryFactorDimensionPorts])
  have hcost : UnarySetup.cost boundaryFactorDimensionOps S.R = boundaryFactorDimensionsCost band N w := by
    simp [boundaryFactorDimensionOps,UnarySetup.cost,UnarySetup.Op.cost,UnarySetup.Op.runR,
      boundaryFactorDimensionsCost,h185,h187,h190,h192,h189,h188,h193,h194,h223,hband,hN,hw]
    ring
  exact ⟨v',n,hu,hcost ▸ hn,he⟩

theorem boundaryFactorDimensions_off (R : Regs 224 A) (i : Fin 224)
    (hi : i ∉ boundaryFactorDimensionPorts) : UnarySetup.runR boundaryFactorDimensionOps R i = R i := by
  have hports : ∀ op ∈ boundaryFactorDimensionOps, op.dst ∈ boundaryFactorDimensionPorts := by decide
  apply UnarySetup.runR_off
  intro op hop he
  subst i
  exact hi (hports op hop)

theorem boundaryFactorDimensions_ready (q w : ℕ) (S : Stacks 224 A)
    (hready : RsbReady (boundaryFactorState S) w q) :
    RsbReady (boundaryFactorState {S with R := UnarySetup.runR boundaryFactorDimensionOps S.R}) w q := by
  have hcm (c : CR) : UnarySetup.runR boundaryFactorDimensionOps S.R (boundaryFactorReg (.cm c)) =
      S.R (boundaryFactorReg (.cm c)) := by
    apply boundaryFactorDimensions_off
    cases c <;> decide
  constructor
  · change (UnarySetup.runR boundaryFactorDimensionOps S.R (boundaryFactorReg (.cm .wn))).length = w
    rw [hcm]; exact hready.wn
  · change (UnarySetup.runR boundaryFactorDimensionOps S.R (boundaryFactorReg (.cm .pn))).length = q
    rw [hcm]; exact hready.pn
  · change (UnarySetup.runR boundaryFactorDimensionOps S.R (boundaryFactorReg (.cm .nn))).length = _
    rw [hcm]; exact hready.nn
  · intro c hxs hys hout hwn hpn hnn
    change UnarySetup.runR boundaryFactorDimensionOps S.R (boundaryFactorReg (.cm c)) = []
    rw [hcm]
    exact hready.empty c hxs hys hout hwn hpn hnn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
