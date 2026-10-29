module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloOutputFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloBuffer
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPublication

/-! The executed zero allocator establishes the full local solver input contract
from its persistent setup frame and borrowed core/radius headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

theorem prepareHaloBuffer_input {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (S : Stacks 242 A)
    (hframe : PackedHaloFrame (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail S)
    (width k radius : ℕ) (ha : a = coreStart width k-radius)
    (hb : b = coreStart width k+coreLength s width k+radius)
    (hleft : radius ≤ coreStart width k)
    (v : HS 256 Q A U) (M : Stacks 256 A)
    (hview : embStk packedHaloPublicationReg M = extendStacks (by decide) S)
    (hoffset : (M.R 249).length = radius) (hrows : (M.R 250).length = coreLength s width k)
    (hfresh : ∀ i ∈ ([253,254,255] : List (Fin 256)), M.R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let E := cstream A (2*q+8) (List.replicate (coreLength s width k+2*radius) (0 : GaussianInt))
    let S' : Stacks 242 A := {S with R := Function.update S.R 132 (E++S.R 132)}
    ∃ v' F n, v'.user = v.user ∧ n ≤ prepareHaloBufferCost q (coreLength s width k) radius ∧
      Exec body prepareHaloBuffer (mk v M) n (mk v' F) ∧
      PackedHaloInput (p := p) (l := l) (t := t) (u := u) (target := target)
        (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail E (S.R 132) S' ∧
      embStk packedHaloPublicationReg F = extendStacks (by decide) S' ∧
      ∀ i : Fin 256, 248 ≤ i.val → F.R i = M.R i := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let N := coreLength s width k+2*radius
  let E := cstream A (2*q+8) (List.replicate N (0 : GaussianInt))
  let S' : Stacks 242 A := {S with R := Function.update S.R 132 (E++S.R 132)}
  have hread (i : Fin 242) : M.R ⟨i.val,by omega⟩ = S.R i := by
    have hh := congrArg (fun G : Stacks 248 A => G.R (Fin.castLE (by decide) i)) hview
    change M.R ⟨i.val,by omega⟩ = (extendStacks (by decide : 242 ≤ 248) S).R (Fin.castLE (by decide) i) at hh
    simpa [extendStacks] using hh
  have hqS : (S.R 119).length = q := by
    have hh := hframe.hready.masters (119,112) (by simp [groupHeaderCopies])
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
      preparedBoundaryCoreReg,packedBoundaryFactorReg,packedBoundaryTableRouting,
      Equiv.swap_apply_def,groupHeaderValue,q,bits,B] using hh
  have hblank (i : Fin 144) (hi : i.val < 109) (hi93 : i ≠ 93) : S.R ⟨i.val,by omega⟩ = [] := by
    have hh := hframe.hready.blank i (by omega) hi93 (by intro he; subst i; simp at hi)
    have hn109 : i.val ≠ 109 := by omega
    have hn115 : i.val ≠ 115 := by omega
    have hn116 : i.val ≠ 116 := by omega
    have hn140 : i.val ≠ 140 := by omega
    have hn143 : i.val ≠ 143 := by omega
    have hn206 : i.val ≠ 206 := by omega
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
      preparedBoundaryCoreReg,packedBoundaryFactorReg,packedBoundaryTableRouting,
      Equiv.swap_apply_def,Fin.ext_iff,hn109,hn115,hn116,hn140,hn143,hn206,
      show i.val < 154 by omega,show i.val ≠ 132 by omega,show i.val ≠ 220 by omega] using hh
  obtain ⟨v₁,n,hu,hn,he⟩ := prepareHaloBuffer_exec (body := body) q (coreLength s width k) radius v M
    ((congrArg List.length (hread 119)).trans hqS) hrows hoffset (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact (hread 104).trans (hblank 104 (by decide) (by decide))
      · exact (hread 105).trans (hblank 105 (by decide) (by decide))
      · exact hfresh 253 (by decide)
      · exact hfresh 254 (by decide)
      · exact hfresh 255 (by decide))
  have hN : N = b-a := by dsimp only [N]; omega
  have hww : 2*q+8 = executionWidth p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card) rhsExp := by
    calc
      2*q+8 = executionWidth p l (initialSchurTarget p u bits 2) 2 := by
        dsimp only [q,executionPrecision,executionWidth]; omega
      _ = _ := (boundaryHaloTarget_sizing p u l (boundaryRecoveryTarget p target) rhsExp B.card).2.2.symm
  dsimp only [B] at hww
  have hinput : PackedHaloInput (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail E (S.R 132) S' := by
    apply hframe.with_output E
    · simp only [E,length_cstream,List.length_replicate,hN,hww]
    · simpa only [E,← hww] using encodedRange_zero_words A N (2*q+8) _ _
  let F : Stacks 256 A := {M with R := Function.update M.R 132 (E++M.R 132)}
  refine ⟨v₁,F,n,hu,hn,he,hinput,?_,?_⟩
  · have hinj : Function.Injective packedHaloPublicationReg := by
      intro i j hij; exact Fin.ext (congrArg (fun k : Fin 256 => k.val) hij)
    have h132 : packedHaloPublicationReg 132 = 132 := by decide
    have hM132 : M.R 132 = S.R 132 := hread 132
    have hp := embStk_updateR hinj M (132 : Fin 248) (E++M.R 132)
    rw [h132,hview,hM132] at hp
    have hx := extendStacks_updateR (by decide : 242 ≤ 248) S (132 : Fin 242) (E++S.R 132)
    rw [show Fin.castLE (by decide : 242 ≤ 248) (132 : Fin 242) = 132 by decide] at hx
    simpa only [F,S',hM132,E,N,q,bits,B] using hp.trans hx.symm
  · intro i hi
    have hn132 : i ≠ 132 := by intro he; subst i; omega
    exact Function.update_of_ne hn132 _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
