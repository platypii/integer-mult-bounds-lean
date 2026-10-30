module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSourceFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAttachQueuedHalo

/-! Turn one executed queue transfer into the actual local solver frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 264 Q A U}

def queuedHaloBaseReg : Fin 242 → Fin 264 := Fin.castLE (by decide)

theorem queuedHaloBaseReg_injective : Function.Injective queuedHaloBaseReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 264 => k.val) he)

theorem attachQueuedHalo_frame {p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    (C : ZMod s → GaussianInt) (S : Stacks 242 A)
    (hsetup : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S)
    (v : HS 264 Q A U) (M : Stacks 264 A)
    (hview : embStk queuedHaloBaseReg M = S) (tail : List (Fin (A+4)))
    (hqueue : M.R 256 = cstream A (executionWidth p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
      (packedInterval a (b-a) C)++tail)
    (hfresh : ∀ i ∈ [(258 : Fin 264),259,260], M.R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let j := boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card) 2) 2
    let xs := cstream A (executionWidth p l j rhsExp) (packedInterval a (b-a) C)
    let S' : Stacks 242 A := {S with R := Function.update S.R 110 (xs++S.R 110)}
    ∃ v' F n, v'.user = v.user ∧ n ≤ attachQueuedHaloCost V q (b-a) ∧
      Exec body attachQueuedHalo (mk v M) n (mk v' F) ∧
      F = {M with R := (Function.update (Function.update M.R 256 tail) 110 (xs++M.R 110))} ∧
      PackedHaloFrame (p := p) (l := l) (t := t) (u := u) (target := target)
        (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C (S.R 110) S' ∧
      embStk queuedHaloBaseReg F = S' ∧ F.R 256 = tail ∧
      ∀ i, i ≠ 110 → i ≠ 256 → F.R i = M.R i := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let j := boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp B.card
  let xs := cstream A (executionWidth p l j rhsExp) (packedInterval a (b-a) C)
  have hread (i : Fin 242) : M.R (queuedHaloBaseReg i) = S.R i :=
    congrArg (fun D : Stacks 242 A => D.R i) hview
  have hq : (S.R 119).length = q := by
    have hh := hsetup.hreadyBase.masters (119,112) (by simp [groupHeaderCopies])
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,
      preparedBoundaryCoreReg,packedBoundaryFactorReg,packedBoundaryTableRouting,
      Equiv.swap_apply_def,groupHeaderValue,q,bits,B] using hh
  have hblank (i : Fin 144) (hi : i.val < 109) (hi93 : i ≠ 93) : S.R ⟨i.val,by omega⟩ = [] := by
    have hh := hsetup.hreadyBase.blank i (by omega) hi93 (by intro he; subst i; simp at hi)
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
  have hwidth : executionWidth p l j rhsExp = 2*q+8 := by
    have hw := (boundaryHaloTarget_sizing p u l (boundaryRecoveryTarget p target) rhsExp B.card).2.2
    change executionWidth p l j rhsExp = executionWidth p l (initialSchurTarget p u bits 2) 2 at hw
    rw [hw]
    dsimp only [executionWidth,q,executionPrecision]
    omega
  have hlen : xs.length = (b-a)*(2*q+8) := by
    rw [length_cstream,packedInterval_length C (by have ha := hsetup.hab; have hb := hsetup.hbs; omega),hwidth]
  have hL : b-a < 2^V := by have hh := hsetup.hfitV; omega
  have hreg110 : queuedHaloBaseReg 110 = 110 := by decide
  have hreg119 : queuedHaloBaseReg 119 = 119 := by decide
  have hreg165 : queuedHaloBaseReg 165 = 165 := by decide
  obtain ⟨v₁,n,hu,hn,he⟩ := attachQueuedHalo_exec (body := body) V q (b-a) hL xs tail hlen v M
    (by rw [←hreg165,hread]; exact hsetup.h165)
    (by rw [←hreg119,hread]; exact hq) hqueue
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa only [show queuedHaloBaseReg 104 = 104 by decide] using
          (hread 104).trans (hblank 104 (by decide) (by decide))
      · simpa only [show queuedHaloBaseReg 105 = 105 by decide] using
          (hread 105).trans (hblank 105 (by decide) (by decide))
      · simpa only [show queuedHaloBaseReg 106 = 106 by decide] using
          (hread 106).trans (hblank 106 (by decide) (by decide))
      · exact hfresh 258 (by simp)
      · exact hfresh 259 (by simp)
      · exact hfresh 260 (by simp))
  let F : Stacks 264 A := {M with R := (Function.update (Function.update M.R 256 tail) 110 (xs++M.R 110))}
  refine ⟨v₁,F,n,hu,hn,he,rfl,hsetup.with_source (S.R 110),?_,?_,?_⟩
  · change embStk queuedHaloBaseReg
      {{M with R := Function.update M.R 256 tail} with R := (Function.update
        (Function.update M.R 256 tail) 110 (xs++M.R 110))} = _
    rw [←hreg110, embStk_updateR queuedHaloBaseReg_injective]
    rw [embStk_updateR_off M 256 tail (by
      intro i he
      have hv := congrArg (fun k : Fin 264 => k.val) he
      have hi := i.isLt
      change i.val = 256 at hv
      omega),hview,hread 110]
  · simp [F]
  · intro i hi110 hi256
    simp [F,hi110,hi256]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
