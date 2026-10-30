module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedCoreGather

/-! The source/header contract for protected gathering, with no execution premise. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

structure ProtectedCoreGatherInput {A : ℕ} (V q s width radius L : ℕ)
    (C : ZMod s → GaussianInt) (M : Stacks 272 A) : Prop where
  hwidth : 0 < width
  hwide : s+width+2*radius < 2^V
  hLfit : L < 2^V
  hwV : 2*q+8 < 2^V
  hvol : s*(2*q+8) < 2^V
  hA : 4 ≤ A
  hVpos : 0 < V
  h163 : (M.R 163).length = V
  hq : (M.R 119).length = q
  hs : M.R 264 = binSyms V s
  hw : M.R 265 = binSyms V width
  hr : M.R 266 = binSyms V radius
  hL : M.R 165 = binSyms V L
  hz : M.R 268 = []
  hblank : ∀ i : Fin 168, i.val < 31 → M.R (protectedCoreGatherReg i) = []
  hclean : ∀ i ∈ [(88 : Fin 168),89,90,92,93,95,96,97,98,99,100,101,102,103,104,105,106,115],
      M.R (protectedCoreGatherReg i) = []
  h261 : M.R 261 = []
  h262 : M.R 262 = []
  h267 : M.R 267 = []
  hsource : M.R 110 = cstream A (2*q+8) (chirpLine s C)

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 272 Q A U}

theorem ProtectedCoreGatherInput.run {V q s width radius L : ℕ}
    {C : ZMod s → GaussianInt} {M : Stacks 272 A}
    (h : ProtectedCoreGatherInput V q s width radius L C M)
    (hgroup : 0 < (coreGatherIndices s width radius L).length) (v : HS 272 Q A U) :
    ∃ v' n, v'.user = v.user ∧ n ≤ protectedCoreGatherCost V q s width radius L ∧
      Exec body protectedCoreGather (IntegerMultBounds.MathlibTM2.Host.mk v M) n
        (IntegerMultBounds.MathlibTM2.Host.mk v' {M with R := (Function.update (Function.update (Function.update M.R
          256 ((coreGatherIndices s width radius L).flatMap
            (fun k => cstream A (2*q+8) (packedInterval (coreStart width k-radius) L C))++M.R 256))
          257 ((coreGatherIndices s width radius L).flatMap
            (fun k => binSyms V (coreStart width k-radius))++M.R 257))
          261 (List.replicate (coreGatherIndices s width radius L).length tick))}) :=
  protectedCoreGather_spec h.hwidth h.hwide h.hLfit h.hwV h.hvol h.hA h.hVpos hgroup v M
    h.h163 h.hq h.hs h.hw h.hr h.hL h.hz h.hblank h.hclean h.h261 h.h262 h.h267 C h.hsource

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
