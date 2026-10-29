module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloInput

/-! Allocating a local output does not alter the solver's input frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

theorem packedBoundaryFactoryView_update_output {A : ℕ} (S : Stacks 242 A) (xs : List (Fin (A+4))) :
    embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting {S with R := Function.update S.R 132 xs}) =
      embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S) := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have he : packedBoundaryTableRouting 220 = 132 := by decide
  have hoff : packedBoundaryTableRouting (packedBoundaryFactorReg i) ≠ 132 := by
    rw [← he]
    exact packedBoundaryTableRouting_injective.ne (packedBoundaryFactorReg_ne_table i)
  simp only [embStk,Function.comp_apply,Function.update_of_ne hoff]

theorem PackedHaloSetup.update_output {A p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    {C : ZMod s → GaussianInt} {S : Stacks 242 A}
    (h : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S) (xs : List (Fin (A+4))) :
    PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C {S with R := Function.update S.R 132 xs} := by
  constructor
  · exact h.hp
  · exact h.hwidth
  · exact h.hα
  · exact h.hst
  · exact h.hu
  · exact h.hαu
  · exact h.hθ
  · exact h.hgap
  · exact h.hbudget
  · exact h.hband
  · exact h.has
  · exact h.hbs
  · exact h.hpad
  · simpa only [packedBoundaryFactoryView_update_output] using h.h109
  · simpa only [packedBoundaryFactoryView_update_output] using h.h115
  · simpa only [packedBoundaryFactoryView_update_output] using h.h116
  · simpa only [packedBoundaryFactoryView_update_output] using h.hleft
  · simpa only [packedBoundaryFactoryView_update_output, Function.update_of_ne (by decide : (110 : Fin 242) ≠ 132)] using h.hreadyBase
  · simpa only [packedBoundaryFactoryView_update_output] using h.haMaster
  · simpa only [packedBoundaryFactoryView_update_output] using h.hbMaster
  · simpa only [packedBoundaryFactoryView_update_output] using h.h0
  · simpa only [packedBoundaryFactoryView_update_output] using h.h139
  · simpa only [packedBoundaryFactoryView_update_output] using h.h127
  · simpa only [packedBoundaryFactoryView_update_output] using h.h138
  · simpa only [packedBoundaryFactoryView_update_output] using h.h143
  · simpa only [packedBoundaryFactoryView_update_output] using h.h147
  · simpa only [packedBoundaryFactoryView_update_output] using h.h151
  · simpa only [packedBoundaryFactoryView_update_output] using h.h153
  · simpa only [packedBoundaryFactoryView_update_output] using h.h152
  · simpa only [packedBoundaryFactoryView_update_output] using h.hnew
  · exact h.h132left
  · simpa only [Function.update_of_ne (by decide : (163 : Fin 242) ≠ 132)] using h.hV
  · simpa only [Function.update_of_ne (by decide : (155 : Fin 242) ≠ 132)] using h.h155
  · simpa only [Function.update_of_ne (by decide : (165 : Fin 242) ≠ 132)] using h.h165
  · exact h.hfitV
  · intro i hi
    have hn : i ≠ 132 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hn] using h.hgeometryBlank i hi
  · simpa only [Function.update_of_ne (by decide : (239 : Fin 242) ≠ 132)] using h.h239
  · exact h.hab
  · exact h.haLt
  · exact h.hsep
  · exact h.hwide
  · exact h.hVeq
  · exact h.hwV
  · exact h.hcoords
  · exact h.hunits
  · exact h.hC
  · simpa only [Function.update_of_ne (by decide : (157 : Fin 242) ≠ 132)] using h.h157
  · simpa only [Function.update_of_ne (by decide : (158 : Fin 242) ≠ 132)] using h.h158
  · simpa only [Function.update_of_ne (by decide : (167 : Fin 242) ≠ 132)] using h.h167
  · intro i hi
    have hn : packedHaloRuntimeReg i ≠ 132 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [embStk,Function.comp_apply,Function.update_of_ne hn] using h.hfresh i hi
  · exact h.hdom

theorem PackedHaloFrame.update_output {A p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    {C : ZMod s → GaussianInt} {tail : List (Fin (A+4))} {S : Stacks 242 A}
    (h : PackedHaloFrame (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail S) (xs : List (Fin (A+4))) :
    PackedHaloFrame (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail {S with R := Function.update S.R 132 xs} :=
  { toPackedHaloSetup := h.toPackedHaloSetup.update_output xs
    hsource := by simpa using h.hsource }

theorem PackedHaloFrame.with_output {A p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    {C : ZMod s → GaussianInt} {tail : List (Fin (A+4))} {S : Stacks 242 A}
    (h : PackedHaloFrame (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail S)
    (E : List (Fin (A+4)))
    (hE : E.length = (b-a)*executionWidth p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
    (hrange : EncodedRange A (executionWidth p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
      (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
      (interiorOutputExponent p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) E) :
    PackedHaloInput (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail E (S.R 132)
      {S with R := Function.update S.R 132 (E++S.R 132)} :=
  { toPackedHaloFrame := h.update_output _
    houtput := by simp
    hE := hE
    hrange := hrange }

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
