module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualUniformBound
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedWorkspaceSizedPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInteriorSharedNumericalWorkspace

/-! The uniform halo worker reuses generated setup and zero-replica arithmetic.
Only scalar dimension bounds enter the common physical envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem arithmeticWorkspace_le_staged (R K q cExp e l w L : ℕ) :
    cellArithmeticWorkspace R K q cExp e l w 0 L ≤ stagedCellWorkspace R K q cExp e l w 0 L := by
  unfold stagedCellWorkspace publishedCellWorkspace
  omega

@[irreducible] noncomputable def uniformHaloWorkspaceConstant : ℕ :=
  4*ringSharedWorkspaceConstant+5000000000*(ssMulConst+1)

theorem solveHaloInteriorUniformWorkspace_poly (J R K p l s t u target rhsExp Z : ℕ)
    (hZ : 1 ≤ Z)
    (hL : (s/(t-s)+1)-2*PhaseCellBand.width p u ≤ 4*p+1)
    (hdim : ∀ x ∈ [J,R,K,2^15*p,l,s,t,u,PhaseCellBand.width p u,
      executionStagePrecision p l target rhsExp+1,executionPrecision p l target rhsExp,
      executionWidth p l target rhsExp,2^l,4*p+1,
      generatedSetupScale p l target rhsExp t u (PhaseCellBand.width p u),
      weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (2*executionPrecision p l target rhsExp+8) t u,
      haloGeometryWidth t (2*executionPrecision p l target rhsExp+8),
      executionPrecision p l target rhsExp+sourceExponent l target rhsExp+(8*p+1)+2*l+3], x ≤ Z) :
    solveHaloInteriorUniformWorkspace J R K p l s t u target rhsExp ≤ uniformHaloWorkspaceConstant*Z^11 := by
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth (2^15*p) q (2*q+8) t u
  let G := haloGeometryWidth t (2*q+8)
  let N := executionStagePrecision p l target rhsExp+1
  have hJ := hdim J (by simp)
  have hR := hdim R (by simp)
  have hK := hdim K (by simp)
  have hP := hdim (2^15*p) (by simp)
  have hl := hdim l (by simp)
  have hs := hdim s (by simp)
  have ht := hdim t (by simp)
  have hu := hdim u (by simp)
  have hb : band ≤ Z := hdim band (by simp [band])
  have hN : N ≤ Z := hdim N (by simp [N])
  have hq : q ≤ Z := hdim q (by simp [q])
  have hw : w ≤ Z := hdim w (by simp [w])
  have hr := hdim (2^l) (by simp)
  have hlength := hdim (4*p+1) (by simp)
  have hscale := hdim (generatedSetupScale p l target rhsExp t u band) (by simp [band])
  have hV : V ≤ Z := hdim V (by simp [V,q])
  have hG : G ≤ Z := hdim G (by simp [G,q])
  have hprecision : q+cExp+(8*p+1)+2*l+3 ≤ Z := hdim _ (by simp [q,cExp])
  have hqpos : 1 ≤ q := by unfold q executionPrecision executionExponent inputExponent sourceExponent; omega
  have hlq : l ≤ q := by unfold q executionPrecision executionExponent inputExponent sourceExponent; omega
  have hwidth : w = 2*q+8 := by dsimp only [w,q,executionWidth,executionPrecision]; omega
  have hwq : w ≤ 10*q := by rw [hwidth]; omega
  have hwpos : 1 ≤ w := by unfold w executionWidth; omega
  have hnum := stagedCellWorkspace_zero_poly hZ hR hK hqpos hlq hwq hwpos hw hlength hr hprecision
  have harithmetic := (arithmeticWorkspace_le_staged R K q cExp (8*p+1) l w (4*p+1)).trans hnum
  have hgenerated := generatedBatchSetupWorkspace_sized_poly J p l s t u band target rhsExp
  have hgeneratedBound : generatedBatchSetupWorkspace J (2^15*p) N q s t u band l (4*p+1) 0 ≤
      288*Z*(ssMulConst+1)*Z^3+100000000*(Z+1)*(Z+1)^3+
        1000000*(Z+Z+Z+Z+1)*(Z+1) := by
    apply hgenerated.trans
    gcongr
  have hkey := haloKeySharedSetup_mono J R K p l s t u target rhsExp _ (4*p+1) hL
  have hupper : haloKeySharedSetup J R K p l s t u target rhsExp (4*p+1) ≤
      (288*Z*(ssMulConst+1)*Z^3+100000000*(Z+1)*(Z+1)^3+
        1000000*(Z+Z+Z+Z+1)*(Z+1))+
        (4*ringSharedWorkspaceConstant+1000000*(ssMulConst+1))*Z^11 := by
    unfold haloKeySharedSetup
    exact Nat.add_le_add hgeneratedBound harithmetic
  have hkeyBound := hkey.trans hupper
  have htable (x : ℕ) (hx : x ≤ Z) : tblC x x ≤ 808*Z^2 := by
    have hsq := Nat.pow_le_pow_left (show x+4 ≤ 5*Z by omega) 2
    unfold tblC
    have hpow : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
    nlinarith only [hsq,hx,hpow]
  have haux : haloKeyAuxWorkspace R K p l s t u target rhsExp V ≤
      9*(808*Z^2)+50000*(8*Z+1)*(3*Z+1)+
        (100000*(2*Z+1)*(Z+1)*(2*Z+1)*(4*Z+1)+30000*((Z+1)+1)*(Z+1)*(2*Z+1))+
        20000*((Z+1)+Z+Z+Z+1)*(Z+1)+3*(25*Z+14) := by
    unfold haloKeyAuxWorkspace
    dsimp only
    gcongr
    all_goals first | exact htable G hG | (change G+V+q ≤ 3*Z; omega) | omega
  have hinit : 18*(200*tblC V V+10000*((2^15*p)+N+q+l+s+t+u+band+s+s+1)*(V+q+1)) ≤
      18*(200*(808*Z^2)+10000*(10*Z+1)*(2*Z+1)) := by
    gcongr
    all_goals first | exact htable V hV | omega
  have hpow (k : ℕ) (hk : k ≤ 11) : Z^k ≤ Z^11 := Nat.pow_le_pow_right hZ hk
  have hscalePow := Nat.mul_le_mul_left (ssMulConst+1) (hpow 4 (by decide))
  have hbase : Z^11 ≤ (ssMulConst+1)*Z^11 := Nat.le_mul_of_pos_left _ (by omega)
  unfold solveHaloInteriorUniformWorkspace uniformHaloWorkspaceConstant
  change 18*(200*tblC V V+10000*((2^15*p)+N+q+l+s+t+u+band+s+s+1)*(V+q+1))+
    (haloKeySharedSetup J R K p l s t u target rhsExp ((s/(t-s)+1)-2*band)+
      haloKeyAuxWorkspace R K p l s t u target rhsExp V) ≤
    (4*ringSharedWorkspaceConstant+5000000000*(ssMulConst+1))*Z^11
  nlinarith only [hkeyBound,haux,hinit,hpow 0 (by decide),hpow 1 (by decide),
    hpow 2 (by decide),hpow 3 (by decide),hpow 4 (by decide),hscalePow,hbase]

end IntegerMultBounds.MathlibTM2.Cost
