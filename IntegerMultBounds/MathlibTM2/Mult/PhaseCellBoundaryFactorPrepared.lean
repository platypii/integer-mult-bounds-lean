module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSetupFacts

/-! Every physical factorizer precondition follows from the generated setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

structure BoundaryFactorPrepared {A : ℕ} (σ : RsbR → List (Fin (A+4))) (p q band N : ℕ) : Prop where
  ready : RsbReady σ (2*q+8) q
  seed : σ .bx = csyms A (2*q+8) (⟨(2 : ℤ)^(q-2),0⟩ : GaussianInt)
  mask : σ .msk = csyms A (2*q+8) 0
  tswn : (σ .tswn).length = (12*band+1+1)*(2*(12*band+1)+1)*(2*q+8)
  sn : (σ .sn).length = N
  kn : (σ .kn).length = factorNewtonSteps p q
  ms : (σ .ms).length = 12*band+1
  m2n : (σ .m2n).length = 2*(12*band+1)
  mwn : (σ .mwn).length = 2*(12*band+1)*(2*q+8)
  smwn : (σ .smwn).length = (2*(12*band+1)+1)*(2*q+8)
  m2wn : (σ .m2wn).length = (12*band)*(2*q+8)
  dst : (σ .dst).length = 12*band
  empty : ∀ r ∈ boundaryFactorScratch, σ r = []

theorem BoundaryFactorPrepared.at_width {A p q band N : ℕ} {σ : RsbR → List (Fin (A+4))}
    (h : BoundaryFactorPrepared σ p q band N) (w : ℕ) (hw : w = 2*q+8) :
    RsbReady σ w q ∧ σ .bx = csyms A w (⟨(2 : ℤ)^(q-2),0⟩ : GaussianInt) ∧
      σ .msk = csyms A w 0 ∧
      (σ .tswn).length = (12*band+1+1)*(2*(12*band+1)+1)*w ∧
      (σ .mwn).length = 2*(12*band+1)*w ∧
      (σ .smwn).length = (2*(12*band+1)+1)*w ∧ (σ .m2wn).length = (12*band)*w := by
  subst w
  exact ⟨h.ready,h.seed,h.mask,h.tswn,h.mwn,h.smwn,h.m2wn⟩

theorem boundaryFactorSetupR_prepared {A : ℕ} (p q band N : ℕ) (S : Stacks 224 A)
    (hband : (S.R 124).length = band) (hN : (S.R 116).length = N)
    (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = [])
    (hready : RsbReady (boundaryFactorState {S with R := boundaryFactorSetupR p q S.R}) (2*q+8) q) :
    BoundaryFactorPrepared (boundaryFactorState {S with R := boundaryFactorSetupR p q S.R}) p q band N := by
  obtain ⟨hdst,hms,hm2n,hsn,hm2wn,hmwn,hsmwn,htswn,_⟩ := boundaryFactorSetupR_dimensions p q band N S.R hband hN hnew
  obtain ⟨hkn,hseed,hmask⟩ := boundaryFactorSetupR_constants p q S.R
  exact ⟨hready,hseed,hmask,htswn,hsn,hkn,hms,hm2n,hmwn,hsmwn,hm2wn,hdst,
    boundaryFactorSetupR_empty p q S.R hnew⟩

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem boundaryFactorSetup_prepared_exec (p q band N : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hp : (S.R 117).length = 2^15*p) (hq : (S.R 119).length = q)
    (hband : (S.R 124).length = band) (hN : (S.R 116).length = N)
    (hclean : ∀ i : Fin 224, i.val < 26 → S.R i = [])
    (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryFactorSetupCost p q band N ∧
      Exec body boundaryFactorSetup (mk v S) n (mk v' {S with R := boundaryFactorSetupR p q S.R}) ∧
      BoundaryFactorPrepared (boundaryFactorState {S with R := boundaryFactorSetupR p q S.R}) p q band N := by
  obtain ⟨v',n,hu,hn,he,hready⟩ := boundaryFactorSetup_exec (body := body) p q band N v S hp hq hband hN hclean hnew
  exact ⟨v',n,hu,hn,he,boundaryFactorSetupR_prepared p q band N S hband hN hnew hready⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
