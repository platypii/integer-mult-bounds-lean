import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineBudgetWords

/-! Shared arithmetic absorption of every actual scan/preparation/cleanup
charge. Fixed program constants remain symbolic throughout these proofs. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineBudgetArithmetic

def modelCost (C A N S E F P I J H : ℕ) :=
  200*(A+1)+1+N*(C*(A+1)+10)+3*S+(74*A+5)*E+(2*A+3)*H+A+14+1+
    E+2*J+4*A+P+F+I+S+72

theorem paid_bound (C A N R S E F P I J H : ℕ) (hN : 0<N)
    (hS : S≤N*(R+2)) (hE : E≤H*(A+R+2)) (hF : F≤N*(R+2))
    (hP : P≤H*(R+2)) (hI : I≤2*N*(R+2)) (hJ : J≤A) (hH : H≤N) :
    modelCost C A N S E F P I J H≤
      (C+1000)*(N*R+N*(A+1)+H*(A+1)*(R+A+1)) := by
  set V := N*R
  set W := N*(A+1)
  set X := H*(A+1)*(R+A+1)
  have hP' : P≤N*(R+2) := hP.trans (Nat.mul_le_mul_right (R+2) hH)
  have hsort : (74*A+6)*E≤148*X := by
    have h0 := Nat.mul_le_mul (by omega : 74*A+6≤74*(A+1)) hE
    have h1 := Nat.mul_le_mul_left (74*(A+1)*H) (by omega : A+R+2≤2*(R+A+1))
    dsimp only [X]
    nlinarith
  have hx : H*(A+1)≤X := Nat.le_mul_of_pos_right _ (by omega : 0<R+A+1)
  have hholes : (2*A+3)*H≤3*X := by nlinarith
  have hsetup : 200*(A+1)+26*N+7*A+88≤400*W := by
    dsimp only [W]
    nlinarith
  have hc : modelCost C A N S E F P I J H≤C*W+8*V+400*W+151*X := by
    unfold modelCost
    dsimp only [V,W] at *
    nlinarith
  exact hc.trans (by nlinarith [Nat.zero_le (C*V),Nat.zero_le (C*X)])

theorem volume_absorb (N R A H D : ℕ) (hR : A+1≤R) (hH : H*(A+1)≤D*N) :
    N*R+N*(A+1)+H*(A+1)*(R+A+1)≤(2+2*D)*(N*R) := by
  have h0 := Nat.mul_le_mul_left N hR
  have h1 := Nat.mul_le_mul_left (H*(A+1)) (by omega : R+A+1≤2*R)
  have h2 := Nat.mul_le_mul_right (2*R) hH
  nlinarith

end IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineBudgetArithmetic
