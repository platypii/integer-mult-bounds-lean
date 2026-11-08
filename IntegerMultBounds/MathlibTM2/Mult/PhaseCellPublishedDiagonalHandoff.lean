module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompleteDiagonalBatch

/-! Raw recovery readiness and the published endpoint supply the diagonal caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}
noncomputable section

theorem diagonal_after_publication (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (N offset rows alpha : ℕ)
    (hprecision : r.problem.p = d.p) (hprec : 13 ≤ d.p) (halpha : 2 ≤ alpha)
    (hsquare : d.u = alpha^2) (hbudget : alpha^2 ≤ d.p)
    (hfit : d.a+offset+rows ≤ s) (hwide : d.p+2 ≤ r.W) (hroom : 4*r.W+2 < 2^d.B)
    (wl : List (Fin (A+4))) (hwl : wl.length = d.B) (S F : Stacks tapes A)
    (hready : plan.CroppedReady crop d r N offset rows wl S)
    (hinput : S.R (plan.work 124) = []) (hleft : ∀ k, S.L k = [])
    (hframe : ∀ i, F.R (recovery i) = S.R (recovery i)) (hL : F.L = S.L)
    (Gs : List (ZMod s → GaussianInt)) (hlen : Gs.length = N)
    (hG : ∀ G ∈ Gs, ∀ x ∈ packedInterval (d.a+offset) rows G, Fits r.W x)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      diagonalMul diagonalMul_injective diagonal_tapes hQ (rsbCr diagonalRole .src .df .dst)) ≤ C)
    (v : HS tapes Q A U) :
    let packet := Gs.flatMap (fun G => cstream A r.W (packedInterval (d.a+offset) rows G))++F.R (crop.reg 12)
    let E : Stacks tapes A := {F with R := Function.update (Function.update F.R source []) (crop.reg 12) packet}
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ completeDiagonalBatchCost E d.B d.p r.W d.u d.t d.a offset rows Gs.length ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v E)+depth+
        (16*diagonalPreparationCost E d.B d.p r.W d.u d.t d.a offset rows+
          (2*bulkSelectionCountsCost Gs.length rows r.W+
            (2*(6*(rows*r.W)+6)+realWeightWorkspace C r.W rows))))
        depth (completeDiagonalBatch hQ) (mk v E) steps
        (mk v' {E with R := (Function.update (Function.update E.R diagonalQueue (F.R (crop.reg 12)))
          (diagonalRole .dst) (Gs.reverse.flatMap (fun G => cstream A r.W
            (packedInterval (d.a+offset) rows (diagonalProduct s d.t alpha d.p G)))))}) := by
  dsimp only
  let packet := Gs.flatMap (fun G => cstream A r.W (packedInterval (d.a+offset) rows G))++F.R (crop.reg 12)
  let E : Stacks tapes A := {F with R := Function.update (Function.update F.R source []) (crop.reg 12) packet}
  have hfresh : DiagonalFresh E := diagonalFresh_of_cropped d r N offset rows wl S F hready hinput hleft hframe hL packet
  have hread (i : RecoveryBank) (hi : i ≠ .control .cropDst) : E.R (recovery i) = S.R (recovery i) := by
    have hc : recovery i ≠ crop.reg 12 := by
      change recovery i ≠ recovery (.control .cropDst)
      exact recovery_injective.ne hi
    have hs : recovery i ≠ source := (geometry_ne_recovery 108 i).symm
    exact (Function.update_of_ne hc _ _).trans ((Function.update_of_ne hs _ _).trans (hframe i))
  have hvalues (i : Fin 8) : (E.R (recovery (.parameter i))).length = d.values i :=
    (congrArg List.length (hread _ (by simp))).trans (hready.values i)
  have hprecE : (E.R (recovery (.control .precision))).length = d.p :=
    ((congrArg List.length (hread _ (by simp))).trans hready.precision).trans hprecision
  have hpacketE : (E.R (recovery (.control .packet))).length = r.W :=
    (congrArg List.length (hread _ (by simp))).trans hready.packet
  have hwidthE : (E.R diagonalWidthSource).length = d.B :=
    (congrArg List.length ((hread _ (by simp)).trans hready.width)).trans hwl
  have hstartE : (E.R diagonalHaloStart).length = d.a := by simpa [diagonalHaloStart,InverseMasterInput.values] using hvalues 6
  have hoffsetE : (E.R diagonalCropOffset).length = offset :=
    (congrArg List.length (hread _ (by simp))).trans hready.offset
  have hrowsE : (E.R diagonalCropRows).length = rows :=
    (congrArg List.length (hread _ (by simp))).trans hready.rows
  have hNE : (E.R (recovery (.control .replicas))).length = Gs.length :=
    ((congrArg List.length (hread _ (by simp))).trans hready.replicas).trans hlen.symm
  let : NeZero d.t := ⟨Nat.ne_of_gt ((NeZero.pos s).trans d.hst)⟩
  obtain ⟨v',steps,hv,hm,he⟩ := completeDiagonalBatch_exec (body := body) hQ hA
    d.u alpha d.B d.p r.W d.a offset rows (NeZero.pos s) d.hst.le hfit hprec halpha hsquare hbudget
    hwide hroom Gs hG C hpush v E (F.R (crop.reg 12))
    (by simpa [InverseMasterInput.values] using hvalues 4)
    (by simpa [InverseMasterInput.values] using hvalues 5)
    (by simpa [InverseMasterInput.values] using hvalues 1)
    (by simpa [InverseMasterInput.values] using hvalues 0)
    hprecE hpacketE hwidthE hstartE hoffsetE hrowsE hNE
    (by change Function.update (Function.update F.R source []) (crop.reg 12) packet (crop.reg 12) = _
        exact Function.update_self ..) hfresh
  refine ⟨v',steps,hv,hm,fun depth => ?_⟩
  simpa only [hfresh.role .dst,List.append_nil] using he depth

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
