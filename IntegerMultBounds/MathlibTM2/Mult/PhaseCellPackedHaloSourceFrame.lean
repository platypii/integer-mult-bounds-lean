module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloInput
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Attach an executed local RHS without assuming its source equation in setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

def packedHaloSourceReg (i : Fin 144) : Fin 242 :=
  packedBoundaryTableRouting (packedBoundaryFactorReg (preparedBoundaryCoreReg
    (boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg (componentReg i))))))

theorem packedHaloSourceReg_injective : Function.Injective packedHaloSourceReg :=
  packedBoundaryTableRouting_injective.comp (packedBoundaryFactorReg_injective.comp
    (preparedBoundaryCoreReg_injective.comp (boundaryFactorLegacyReg_injective.comp
      (tableReg_injective.comp (boundaryArithmeticReg_injective.comp componentReg_injective)))))

theorem packedHaloSourceView_update {A : ℕ} (S : Stacks 242 A) (xs : List (Fin (A+4))) :
    embStk packedHaloSourceReg {S with R := Function.update S.R 110 xs} =
      {embStk packedHaloSourceReg S with R := Function.update (embStk packedHaloSourceReg S).R 110 xs} := by
  have he : packedHaloSourceReg 110 = 110 := by decide
  simpa only [he] using embStk_updateR packedHaloSourceReg_injective S 110 xs

theorem packedHaloFactoryView_update_source {A : ℕ} (S : Stacks 242 A) (xs : List (Fin (A+4))) :
    embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting {S with R := Function.update S.R 110 xs}) =
      {embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S) with R :=
        (Function.update (embStk packedBoundaryFactorReg (embStk packedBoundaryTableRouting S)).R 110 xs)} := by
  let reg := fun i => packedBoundaryTableRouting (packedBoundaryFactorReg i)
  have hinj : Function.Injective reg := packedBoundaryTableRouting_injective.comp packedBoundaryFactorReg_injective
  have he : reg 110 = 110 := by decide
  have h := embStk_updateR hinj S 110 xs
  rw [he] at h
  simpa only [reg, embStk, Function.comp_def] using h

theorem PackedHaloSetup.update_source {A p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    {C : ZMod s → GaussianInt} {S : Stacks 242 A}
    (h : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S) (xs : List (Fin (A+4))) :
    PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C {S with R := Function.update S.R 110 xs} := by
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
  · simpa [packedHaloFactoryView_update_source] using h.h109
  · simpa [packedHaloFactoryView_update_source] using h.h115
  · simpa [packedHaloFactoryView_update_source] using h.h116
  · simpa [packedHaloFactoryView_update_source] using h.hleft
  · change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _
      (embStk packedHaloSourceReg {S with R := Function.update S.R 110 xs})
    rw [packedHaloSourceView_update]
    exact h.hreadyBase.update_source xs
  · simpa [packedHaloFactoryView_update_source] using h.haMaster
  · simpa [packedHaloFactoryView_update_source] using h.hbMaster
  · simpa [packedHaloFactoryView_update_source] using h.h0
  · simpa [packedHaloFactoryView_update_source] using h.h139
  · simpa [packedHaloFactoryView_update_source] using h.h127
  · simpa [packedHaloFactoryView_update_source] using h.h138
  · simpa [packedHaloFactoryView_update_source] using h.h143
  · simpa [packedHaloFactoryView_update_source] using h.h147
  · simpa [packedHaloFactoryView_update_source] using h.h151
  · simpa [packedHaloFactoryView_update_source] using h.h153
  · simpa [packedHaloFactoryView_update_source] using h.h152
  · intro i hi
    have hn : preparedBoundaryCoreReg i ≠ 110 := by
      intro he
      have hv := congrArg (fun k : Fin 226 => k.val) he
      change i.val = 110 at hv
      omega
    simpa only [packedHaloFactoryView_update_source, Function.update_of_ne hn] using h.hnew i hi
  · exact h.h132left
  · simpa only [Function.update_of_ne (by decide : (163 : Fin 242) ≠ 110)] using h.hV
  · simpa only [Function.update_of_ne (by decide : (155 : Fin 242) ≠ 110)] using h.h155
  · simpa only [Function.update_of_ne (by decide : (165 : Fin 242) ≠ 110)] using h.h165
  · exact h.hfitV
  · intro i hi
    have hn : i ≠ 110 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hn] using h.hgeometryBlank i hi
  · simpa only [Function.update_of_ne (by decide : (239 : Fin 242) ≠ 110)] using h.h239
  · exact h.hab
  · exact h.haLt
  · exact h.hsep
  · exact h.hwide
  · exact h.hVeq
  · exact h.hwV
  · exact h.hcoords
  · exact h.hunits
  · exact h.hC
  · simpa only [Function.update_of_ne (by decide : (157 : Fin 242) ≠ 110)] using h.h157
  · simpa only [Function.update_of_ne (by decide : (158 : Fin 242) ≠ 110)] using h.h158
  · simpa only [Function.update_of_ne (by decide : (167 : Fin 242) ≠ 110)] using h.h167
  · intro i hi
    have hn : packedHaloRuntimeReg i ≠ 110 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [embStk,Function.comp_apply,Function.update_of_ne hn] using h.hfresh i hi
  · exact h.hdom

theorem PackedHaloSetup.with_source {A p l s t u target rhsExp a b V : ℕ} [NeZero s] {α d : ℝ}
    {C : ZMod s → GaussianInt} {S : Stacks 242 A}
    (h : PackedHaloSetup (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C S) (tail : List (Fin (A+4))) :
    PackedHaloFrame (p := p) (l := l) (t := t) (u := u) (target := target)
      (rhsExp := rhsExp) (a := a) (b := b) (V := V) α d C tail
      {S with R := (Function.update S.R 110
        (cstream A (executionWidth p l
          (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
            (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)
          (packedInterval a (b-a) C)++tail))} :=
  { toPackedHaloSetup := h.update_source _
    hsource := by simp }

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
