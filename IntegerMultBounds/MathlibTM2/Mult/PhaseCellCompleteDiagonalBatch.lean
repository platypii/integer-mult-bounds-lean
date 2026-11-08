module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalBatchRetirement

/-! A complete diagonal batch, including ordinary setup and shared storage retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s t Q A : ℕ} [NeZero s] [NeZero t] {P U : Type} {body : P → Pr P tapes Q A U}
noncomputable section

def completeDiagonalBatch (hQ : SS.states ≤ Q) : Pr P tapes Q A U :=
  .seq (preparedDiagonalBatch hQ) retireDiagonalBatch

def diagonalRetirementCost (p w n : ℕ) : ℕ :=
  2*(n*w+n*w+w+p+IntegerMultBounds.Schoenhage.Schedule.topN w)+11

def completeDiagonalBatchCost (S : Stacks tapes A) (B p w u t a radius n N : ℕ) : ℕ :=
  diagonalPreparationCost S B p w u t a radius n+
    (bulkSelectionCountsCost N n w+localDiagonalBatchCost N n w)+diagonalRetirementCost p w n

theorem completeDiagonalBatch_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ completeDiagonalBatchCost S B p w u t a radius n Ds.length ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        (16*diagonalPreparationCost S B p w u t a radius n+
          (2*bulkSelectionCountsCost Ds.length n w+(2*(6*(n*w)+6)+realWeightWorkspace C w n))))
        depth (completeDiagonalBatch hQ) (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R diagonalQueue tail)
          (diagonalRole .dst) ((Ds.reverse.flatMap (fun D => cstream A w
            (packedInterval (a+radius) n (diagonalProduct s t alpha p D))))++S.R (diagonalRole .dst)))}) := by
  obtain ⟨v₁,F,m,hv₁,hm,he,_,_,_,_,_,hfinal⟩ := preparedDiagonalBatch_exec (body := body)
    hQ hA u alpha B p w a radius n hs hst hfit hp halpha hsquare hbudget hw hroom Ds hD C hpush
    v S tail hS hT hu hprec hprecision hpacket hB ha hradius hn hN hqueue hfresh
  let page := cstream A w (packedInterval (a+radius) n (diagonalField s t alpha p))++S.R (diagonalRole .df)
  let output := Ds.reverse.flatMap (fun D => cstream A w
    (packedInterval (a+radius) n (diagonalProduct s t alpha p D)))
  let live := diagonalBatchLiveState S p w Ds.length n page tail output
  have hF : F = live := hfinal
  rw [hF] at he
  obtain ⟨v₂,hv₂,hretire⟩ := retireDiagonalBatch_exec (body := body) S p w Ds.length n page tail output hfresh v₁
  have hpageLength : page.length = n*w := by
    simp only [page,hfresh.role .df,List.append_nil,length_cstream,packedInterval_length _ hfit]
  have hretireCost : retireDiagonalBatchCost live = diagonalRetirementCost p w n := by
    rw [retireDiagonalBatchCost_eq S p w Ds.length n page tail output hfresh,hpageLength]
    rfl
  refine ⟨v₂,m+retireDiagonalBatchCost live,hv₂.trans hv₁,?_,fun depth => ?_⟩
  · rw [hretireCost]
    dsimp only [completeDiagonalBatchCost]
    omega
  · simpa only [Nat.add_zero,completeDiagonalBatch,live,output] using
      mn_seq_within_add (he depth) (hretire depth)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
