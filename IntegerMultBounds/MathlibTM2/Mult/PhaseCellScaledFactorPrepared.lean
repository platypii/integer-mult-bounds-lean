module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledFactorSetupFacts
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorPrepared

/-! Every physical factorizer precondition follows from the generated setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

theorem scaledFactorSetupR_prepared {A : ℕ} (scale p q band N : ℕ) (S : Stacks 224 A)
    (hband : (S.R 124).length = band) (hN : (S.R 116).length = N)
    (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = [])
    (hready : RsbReady (boundaryFactorState {S with R := scaledFactorSetupR (12*scale) p q S.R}) (2*q+8) q) :
    BoundaryFactorPrepared (boundaryFactorState {S with R := scaledFactorSetupR (12*scale) p q S.R}) p q (scale*band) N := by
  obtain ⟨hdst,hms,hm2n,hsn,hm2wn,hmwn,hsmwn,htswn,_⟩ := scaledFactorSetupR_dimensions (12*scale) p q band N S.R hband hN hnew
  obtain ⟨hkn,hseed,hmask⟩ := scaledFactorSetupR_constants (12*scale) p q S.R
  exact ⟨hready,hseed,hmask,by simpa only [boundaryFactorState,boundaryFactorReg,Nat.mul_assoc] using htswn,hsn,hkn,
    by simpa only [boundaryFactorState,boundaryFactorReg,Nat.mul_assoc] using hms,by simpa only [boundaryFactorState,boundaryFactorReg,Nat.mul_assoc] using hm2n,
    by simpa only [boundaryFactorState,boundaryFactorReg,Nat.mul_assoc] using hmwn,by simpa only [boundaryFactorState,boundaryFactorReg,Nat.mul_assoc] using hsmwn,
    by simpa only [boundaryFactorState,boundaryFactorReg,Nat.mul_assoc] using hm2wn,by simpa only [boundaryFactorState,boundaryFactorReg,Nat.mul_assoc] using hdst,
    scaledFactorSetupR_empty (12*scale) p q S.R hnew⟩

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem scaledFactorSetup_prepared_exec (scale p q band N : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hp : (S.R 117).length = 2^15*p) (hq : (S.R 119).length = q)
    (hband : (S.R 124).length = band) (hN : (S.R 116).length = N)
    (hclean : ∀ i : Fin 224, i.val < 26 → S.R i = [])
    (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ scaledFactorSetupCost (12*scale) p q band N ∧
      Exec body (scaledFactorSetup (12*scale)) (mk v S) n (mk v' {S with R := scaledFactorSetupR (12*scale) p q S.R}) ∧
      BoundaryFactorPrepared (boundaryFactorState {S with R := scaledFactorSetupR (12*scale) p q S.R}) p q (scale*band) N := by
  obtain ⟨v',n,hu,hn,he,hready⟩ := scaledFactorSetup_exec (body := body) (12*scale) p q band N v S hp hq hband hN hclean hnew
  exact ⟨v',n,hu,hn,he,scaledFactorSetupR_prepared scale p q band N S hband hN hnew hready⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
