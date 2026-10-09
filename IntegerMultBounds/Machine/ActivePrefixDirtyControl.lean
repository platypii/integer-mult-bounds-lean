import IntegerMultBounds.Machine.ActivePrefixDirtyControlCleanup

/-! Clean original-input dirty-U offset production. The volume includes the
wide target width explicitly; compact-U fit alone does not imply n*q≤W. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControl
noncomputable section
open ActivePrefixDirtyControlData
open ActivePrefixDirtyControlHeaders (bank)
open BinaryVaryingOffsetGatherPlaced (Kind sourceWidth outputWidth)
variable {a : ℕ} {k : Kind}

def program (k : Kind) := seq (ActivePrefixDirtyControlRun.program (a := a) k) ActivePrefixDirtyControlCleanup.program
def input (hs : Fin 6 → List Bool) := bank (base (a := a) hs)
def output (s : Shape k) (hs : Fin 6 → List Bool) := bank (ActivePrefixDirtyControlCleanup.result (a := a) s hs)
def cost (s : Shape k) := ActivePrefixDirtyControlRun.cost s+1+ActivePrefixDirtyControlCleanup.cost s
def volume (s : Shape k) := 2^s.W*(s.W+s.n*s.q+s.q+s.b+1)
def constant := FixedBasePowerDescriptor.constant 2+3*BinaryPrefixFieldTableRun.constant+4000

theorem runs (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a) k) (fun v => v=input hs) (fun v => v=output s hs) (cost s) :=
  (ActivePrefixDirtyControlRun.runs s hs hv hc).seq (ActivePrefixDirtyControlCleanup.runs s hs)

theorem cost_bound (s : Shape k) : cost s≤constant*volume s := by
  let P := 2^s.W
  let V := volume s
  have hP : 1≤P := Nat.one_le_pow _ _ (by decide)
  have hVP : P≤V := Nat.le_mul_of_pos_right _ (by omega)
  have hV : 1≤V := hP.trans hVP
  have hnb : s.n*s.b≤s.W := by have := s.controlFits; omega
  have hn : s.n≤s.W := (Nat.le_mul_of_pos_right _ s.hb).trans hnb
  have htemp : tempWidth s≤s.W := by have := s.tempFits; dsimp [tempWidth]; omega
  have hW : P*(s.W+1)≤V := Nat.mul_le_mul_left P (by omega)
  have hN : P*s.n≤V := Nat.mul_le_mul_left P (by omega)
  have hB : P*(s.n*s.b)≤V := Nat.mul_le_mul_left P (by omega)
  have hQ : P*(s.n*s.q)≤V := Nat.mul_le_mul_left P (by omega)
  have hT : P*tempWidth s≤V := Nat.mul_le_mul_left P (by omega)
  have hsmall : s.q+s.b+1≤V := (by
    have h : s.q+s.b+1≤s.W+s.n*s.q+s.q+s.b+1 := by omega
    exact h.trans (Nat.le_mul_of_pos_left _ hP))
  have hpar : (P*s.n+1)*(s.b+2)≤5*V := by
    have hb : s.b+2≤2*V := by omega
    nlinarith
  have hgat : (P*s.n+1)*(s.q+s.b+1)≤4*V := by nlinarith
  have hnq : s.n*s.q≤V := (Nat.le_mul_of_pos_left _ hP).trans hQ
  have hnbV : s.n*s.b≤V := (Nat.le_mul_of_pos_left _ hP).trans hB
  have hO : outputRowWidth s≤s.n*s.q := by
    cases k <;> simp only [outputRowWidth,outputWidth]
    · exact le_rfl
    · exact le_rfl
    · exact Nat.mul_le_mul_left s.n (by have := s.hbq; omega)
  have hOV : P*outputRowWidth s≤V := (Nat.mul_le_mul_left P hO).trans hQ
  have hh := CompactGadgetReservationHeadersCarvedPlacedCleanup.cost_bound (derivedWords s) V hV
    (by intro i; fin_cases i <;> exact RecursiveChildQuotientsConstant.bits_canonical _)
    (by
      intro i; fin_cases i <;> simp [derivedWords,RecursiveChildQuotientsConstant.bits_value]
      · exact hVP
      · exact hnbV
      · simpa only [Nat.mul_comm] using hN
      · exact hnq)
  have hproj := Nat.mul_le_mul_left (3*BinaryPrefixFieldTableRun.constant) hW
  have hpow := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hVP
  unfold cost ActivePrefixDirtyControlRun.cost ActivePrefixDirtyControlHeaders.cost
    ActivePrefixDirtyControlCleanup.cost constant
  simp only [tempWord,sourceWord,clockWord,BinaryPrefixFieldTableData.word_length,control_length,offset_length]
  rw [BinaryPrefixFieldTableData.word_length s.W s.startT (tempWidth s) s.tempFits]
  change FixedBasePowerDescriptor.constant 2*P+(53*(s.n*s.b)+28)+
    (53*(s.n*P)+28)+(53*(s.n*s.q)+28)+3+
    3*(BinaryPrefixFieldTableRun.constant*(P*(s.W+1)))+
    330*((P*s.n+1)*(s.b+2))+320*((P*s.n+1)*(s.q+s.b+1))+5+1+
    (P*tempWidth s+P*s.n+2*(P*(s.n*s.b))+P*outputRowWidth s+12+
      (2*(P*s.n)+3)+CompactGadgetReservationHeadersCarvedPlacedCleanup.cost (derivedWords s)+2)≤
    (FixedBasePowerDescriptor.constant 2+3*BinaryPrefixFieldTableRun.constant+4000)*V
  nlinarith

theorem runs_linear (s : Shape k) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a) k) (fun v => v=input hs) (fun v => v=output s hs) (constant*volume s) :=
  (runs s hs hv hc).consequence (fun _ h => h) (fun _ h => h) (cost_bound s)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControl
