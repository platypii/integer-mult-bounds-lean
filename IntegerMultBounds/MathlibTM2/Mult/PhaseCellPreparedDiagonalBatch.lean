module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPageReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedDiagonalBatch

/-! Ordinary page and multiplier setup followed by the shared diagonal batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s t Q A : ℕ} [NeZero s] [NeZero t] {P U : Type} {body : P → Pr P tapes Q A U}
noncomputable section

def preparedDiagonalBatch (hQ : SS.states ≤ Q) : Pr P tapes Q A U :=
  .seq prepareDiagonalPage (countedDiagonalBatch hQ)

def diagonalPreparationCost (S : Stacks tapes A) (B p w u t a radius n : ℕ) : ℕ :=
  ordinaryDiagonalPageCost S p w u t a radius n+diagonalMultiplierLocalCost B p w

theorem preparedDiagonalBatch_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (u alpha B p w a radius n : ℕ) (hs : 0 < s) (hst : s ≤ t) (hfit : a+radius+n ≤ s)
    (hp : 13 ≤ p) (halpha : 2 ≤ alpha) (hsquare : u = alpha^2) (hbudget : alpha^2 ≤ p)
    (hw : p+2 ≤ w) (hroom : 4*w+2 < 2^B)
    (Ds : List (ZMod s → GaussianInt))
    (hD : ∀ D ∈ Ds, ∀ z ∈ packedInterval (a+radius) n D, Fits w z)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      diagonalMul diagonalMul_injective diagonal_tapes hQ (rsbCr diagonalRole .src .df .dst)) ≤ C)
    (v : HS tapes Q A U) (S : Stacks tapes A) (tail : List (Fin (A+4)))
    (hS : (S.R (recovery (.parameter 4))).length = s)
    (hT : (S.R (recovery (.parameter 5))).length = t)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (hprec : (S.R (recovery (.parameter 0))).length = p)
    (hprecision : (S.R (recovery (.control .precision))).length = p)
    (hpacket : (S.R (recovery (.control .packet))).length = w)
    (hB : (S.R diagonalWidthSource).length = B)
    (ha : (S.R diagonalHaloStart).length = a)
    (hradius : (S.R diagonalCropOffset).length = radius)
    (hn : (S.R diagonalCropRows).length = n)
    (hN : (S.R (recovery (.control .replicas))).length = Ds.length)
    (hqueue : S.R diagonalQueue = Ds.flatMap (fun D =>
      cstream A w (packedInterval (a+radius) n D))++tail) (hfresh : DiagonalFresh S) :
    let page := cstream A w (packedInterval (a+radius) n (diagonalField s t alpha p))++S.R (diagonalRole .df)
    let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
    let M : Stacks tapes A := {E with R := diagonalCounterR p w E.R}
    ∃ v' F steps, v'.user = v.user ∧
      steps ≤ diagonalPreparationCost S B p w u t a radius n+
        (bulkSelectionCountsCost Ds.length n w+localDiagonalBatchCost Ds.length n w) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        (16*diagonalPreparationCost S B p w u t a radius n+
          (2*bulkSelectionCountsCost Ds.length n w+(2*(6*(n*w)+6)+realWeightWorkspace C w n))))
        depth (preparedDiagonalBatch hQ) (mk v S) steps (mk v' F)) ∧
      F.R diagonalClock = [] ∧ F.R diagonalQueue = tail ∧
      F.R (diagonalRole .dst) = Ds.reverse.flatMap (fun D =>
        cstream A w (packedInterval (a+radius) n (diagonalProduct s t alpha p D))) ∧
      F.R (diagonalRole .df) = cstream A w (packedInterval (a+radius) n (diagonalField s t alpha p)) ∧
      F.R (diagonalRole .src) = [] ∧
      F = diagonalBatchOutputState (diagonalBatchCounterState M Ds.length n w) tail
        (Ds.reverse.flatMap (fun D => cstream A w (packedInterval (a+radius) n (diagonalProduct s t alpha p D)))) := by
  dsimp only
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁,hready⟩ := prepareDiagonalPage_exec (body := body)
    s t u alpha B p w a radius n hs hst hfit hp halpha hsquare hbudget (by omega) (by omega)
    hroom v S hS hT hu hprec hprecision hpacket hB ha hradius hn hfresh
  let page := cstream A w (packedInterval (a+radius) n (diagonalField s t alpha p))++S.R (diagonalRole .df)
  let E : Stacks tapes A := {S with R := Function.update S.R (diagonalRole .df) page}
  let M : Stacks tapes A := {E with R := diagonalCounterR p w E.R}
  have hcounter (k : Fin tapes) (hw : k ≠ diagonalCr .wn) (hp : k ≠ diagonalCr .pn)
      (hn : k ≠ diagonalCr .nn) (hd : k ≠ diagonalRole .df) : M.R k = S.R k :=
    (chirpMultiplierSetup_off diagonalCr E.R p w k hw hp hn).trans (Function.update_of_ne hd _ _)
  have hcontrol (c : RecoveryControl) : M.R (recovery (.control c)) = S.R (recovery (.control c)) := by
    apply hcounter
    all_goals simp [diagonalCr,diagonalRole,recovery_injective.eq_iff]
  have hwork (i : Fin 392) (hi : 100 ≤ i.val) : M.R (recovery (.work i)) = [] :=
    (hcounter _ (diagonalRole_ne_work (.cm .wn) i hi).symm
      (diagonalRole_ne_work (.cm .pn) i hi).symm (diagonalRole_ne_work (.cm .nn) i hi).symm
      (diagonalRole_ne_work .df i hi).symm).trans (hfresh.work i)
  obtain ⟨hclean,hpage,hsrc,hdst⟩ := diagonalPage_multiplier_frame p w S hfresh page
  have hdstM : M.R (diagonalRole .dst) = [] := hdst
  have hpage' : M.R (diagonalRole .df) =
      cstream A w (packedInterval (a+radius) n (diagonalField s t alpha p)) := by
    exact hpage.trans (by simp only [page,hfresh.role .df,List.append_nil])
  have hqueueM : M.R diagonalQueue = S.R diagonalQueue := hcontrol .cropDst
  obtain ⟨v₂,F,m₂,hv₂,hm₂,he₂,hclock,hq,hout,hpageF,hsrcF,hfinal⟩ := countedDiagonalBatch_exec
    (body := body) hQ hA alpha p w (a+radius) n hw hp (by omega) hbudget Ds hfit hD
    (fun r => M.R (diagonalRole r)) hready hpage' C hpush v₁ M tail
    (by rw [hcontrol .replicas]; exact hN) (by rw [hcontrol .cropRows]; exact hn)
    (by rw [hcontrol .packet]; exact hpacket)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact hwork _ (by decide))
    (hqueueM.trans hqueue) hsrc hclean (fun _ => rfl)
  refine ⟨v₂,F,m₁+m₂,hv₂.trans hv₁,?_,fun depth => ?_,hclock,hq,?_,hpageF.trans hpage',hsrcF,hfinal⟩
  · change m₁ ≤ diagonalPreparationCost S B p w u t a radius n at hm₁
    omega
  · exact mn_seq_within_add (he₁ depth) (he₂ depth)
  · simpa only [hdstM,List.append_nil] using hout

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
