module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallSparseUnaryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicCallerInput
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Install generated seed masters into the two physical caller banks.
The two sides share one structural proof; payload registers remain blank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

def seedBank (side : Bool) : Fin 392 → Fin tapes := if side then seedR else seedL

private theorem seedBank_injective (side : Bool) : Function.Injective (seedBank side) := by
  cases side <;> intro i j h
  · exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (port_injective h)))
  · exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (port_injective h))))

private theorem seedBank_ne_tmp (side : Bool) (i : Fin 392) : seedBank side i ≠ caller.tmp := by
  cases side <;> simp [seedBank,seedL,seedR,caller,aux,port_injective.eq_iff]

def installRetainedSeeds (side : Bool) (source : Fin 392 → Fin tapes) : Pr P tapes Q A U :=
  installRecoverySeedHeaders source (seedBank side) caller.tmp

theorem installRetainedSeeds_exec (side : Bool) (source : Fin 392 → Fin tapes)
    (H : ReplicaHaloProblem s) (W N : ℕ) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hsource : ∀ i j, source i ≠ seedBank side j)
    (hsourceTmp : ∀ i, source i ≠ caller.tmp)
    (hvalues : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (source i)).length = recoverySeedHeader H W N i)
    (hblank : ∀ i, S.R (seedBank side i) = []) (htmp : S.R caller.tmp = []) :
    let cost := copyUnaryHeadersCost (fun r => (S.R r).length)
      (recoverySeedHeaderCopies source (seedBank side))
    ∃ v' F, v'.user = v.user ∧
      (∀ i, F.R (seedBank side i) = List.replicate (recoverySeedHeader H W N i) tick) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ r, (∀ i, r ≠ seedBank side i) → F.R r = S.R r) ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*cost)
        depth (installRetainedSeeds side source) (mk v S) cost (mk v' F) := by
  dsimp only
  obtain ⟨v',hu,hfields,hframe,_,he⟩ := installSparseUnaryHeaders_exec (body := body)
    recoverySeedHeaderPorts (by decide) 124 (by decide) (recoverySeedHeader H W N)
    (recoverySeedHeader_off H W N) source (seedBank side) (seedBank_injective side) caller.tmp
    hsource hsourceTmp (seedBank_ne_tmp side) v S hvalues (fun i _ => hblank i)
    [] (hblank 124) htmp
  let F : Stacks tapes A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R (recoverySeedHeaderCopies source (seedBank side))}
  refine ⟨v',F,hu,?_,rfl,rfl,rfl,hframe,he⟩
  intro i
  by_cases hi : i = 124
  · subst i
    simpa only [F,recoverySeedHeaderCopies,ite_true,recoverySeedHeader_off H W N 124 (by decide),List.replicate_zero] using hfields 124
  · simpa only [F,recoverySeedHeaderCopies,hi,ite_false] using hfields i

private theorem seedBank_separated (i j : Fin 392) : seedBank false i ≠ seedBank true j := by
  simp [seedBank,seedL,seedR,port_injective.eq_iff]

private theorem seedBank_ne_numeric (side : Bool) (i : Fin 392) (j : Fin 909) :
    seedBank side i ≠ numeric j := by
  cases side <;> simp [seedBank,seedL,seedR,numeric,port_injective.eq_iff]

private theorem seedBank_ne_aux (side : Bool) (i : Fin 392) (j : Fin 9) :
    seedBank side i ≠ aux j := by
  cases side <;> simp [seedBank,seedL,seedR,aux,port_injective.eq_iff]

private theorem seedBank_ne_control (side : Bool) (i : Fin 392) (j : Fin 3) :
    seedBank side i ≠ caller.controls j := by
  change seedBank side i ≠ controls j
  fin_cases j <;> cases side <;>
    simp [seedBank,seedL,seedR,controls,geometry,selector,aux,port_injective.eq_iff]

def installRetainedSeedPair (sourceL sourceR : Fin 392 → Fin tapes) : Pr P tapes Q A U :=
  .seq (installRetainedSeeds false sourceL) (installRetainedSeeds true sourceR)

theorem installRetainedSeedPair_exec
    (sourceL sourceR : Fin 392 → Fin tapes) (H K : ReplicaHaloProblem s)
    (W N radius rows : ℕ) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hsource : ∀ side i j, sourceL i ≠ seedBank side j ∧ sourceR i ≠ seedBank side j)
    (hsourceTmp : ∀ i, sourceL i ≠ caller.tmp ∧ sourceR i ≠ caller.tmp)
    (hvaluesL : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (sourceL i)).length = recoverySeedHeader H W N i)
    (hvaluesR : ∀ i ∈ recoverySeedHeaderPorts,
      (S.R (sourceR i)).length = recoverySeedHeader K W N i)
    (hblank : ∀ side i, S.R (seedBank side i) = [])
    (hbank : ∀ i, S.L (caller.bank i) = [] ∧ S.R (caller.bank i) = [])
    (hcontrols : ∀ i, (S.R (caller.controls i)).length = ![W,radius,rows] i)
    (hsaved : S.R caller.saved = []) (htmp : S.R caller.tmp = []) :
    let leftCost := copyUnaryHeadersCost (fun r => (S.R r).length)
      (recoverySeedHeaderCopies sourceL (seedBank false))
    let rightCost := copyUnaryHeadersCost (fun r => (S.R r).length)
      (recoverySeedHeaderCopies sourceR (seedBank true))
    ∃ vf F, vf.user = v.user ∧ caller.InputContext H K W N radius rows F ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ r, (∀ side i, r ≠ seedBank side i) → F.R r = S.R r) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(2*leftCost+2*rightCost)) depth
        (installRetainedSeedPair sourceL sourceR) (mk v S) (leftCost+rightCost) (mk vf F) := by
  dsimp only
  obtain ⟨vl,M,hul,hleft,hML,hMin,hMout,hframeL,heL⟩ :=
    installRetainedSeeds_exec (body := body) false sourceL H W N v S
      (fun i j => (hsource false i j).1) (fun i => (hsourceTmp i).1)
      hvaluesL (hblank false) htmp
  have hread (i : Fin 392) : M.R (sourceR i) = S.R (sourceR i) :=
    hframeL _ (fun j => (hsource false i j).2)
  obtain ⟨vf,F,hur,hright,hFL,hFin,hFout,hframeR,heR⟩ :=
    installRetainedSeeds_exec (body := body) true sourceR K W N vl M
      (fun i j => (hsource true i j).2) (fun i => (hsourceTmp i).2)
      (by intro i hi; rw [hread]; exact hvaluesR i hi)
      (fun i => (hframeL _ (fun j => (seedBank_separated j i).symm)).trans (hblank true i))
      ((hframeL _ (fun i => (seedBank_ne_tmp false i).symm)).trans htmp)
  have hcost : copyUnaryHeadersCost (fun r => (M.R r).length)
      (recoverySeedHeaderCopies sourceR (seedBank true)) =
      copyUnaryHeadersCost (fun r => (S.R r).length)
        (recoverySeedHeaderCopies sourceR (seedBank true)) := by
    simp only [copyUnaryHeadersCost,recoverySeedHeaderCopies,List.map_map,Function.comp_def]
    congr 2
    apply List.map_congr_left
    intro i _
    rw [hread]
  have hframe (r : Fin tapes) (hr : ∀ side i, r ≠ seedBank side i) : F.R r = S.R r :=
    (hframeR r (hr true)).trans (hframeL r (hr false))
  have hcontext : caller.InputContext H K W N radius rows F := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro i
      refine ⟨(congrFun (hFL.trans hML) _).trans (hbank i).1,?_⟩
      exact (hframe _ (fun side j => (seedBank_ne_numeric side j i).symm)).trans (hbank i).2
    · intro i _
      have h := (hframeR _ (fun j => seedBank_separated i j)).trans (hleft i)
      simpa only [caller,seedBank,Bool.false_eq_true,ite_false,List.length_replicate] using congrArg List.length h
    · intro i _
      simpa only [caller,seedBank,ite_true,List.length_replicate] using congrArg List.length (hright i)
    · intro i
      rw [hframe _ (fun side j => (seedBank_ne_control side j i).symm)]
      exact hcontrols i
    · exact (hframe _ (fun side j => (seedBank_ne_aux side j 3).symm)).trans hsaved
    · exact (hframe _ (fun side j => (seedBank_ne_tmp side j).symm)).trans htmp
  refine ⟨vf,F,hur.trans hul,hcontext,hFL.trans hML,hFin.trans hMin,hFout.trans hMout,hframe,?_⟩
  intro depth
  have heR' := heR depth
  rw [hcost] at heR'
  exact mn_seq_within_add (heL depth) heR'

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
