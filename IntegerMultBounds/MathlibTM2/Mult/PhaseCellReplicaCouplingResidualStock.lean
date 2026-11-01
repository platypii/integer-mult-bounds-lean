module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingResidual

/-! Residual finishing preserves an arbitrary worker's intermediate-workspace
allowance, using the common exact endpoint identity. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem replicaCouplingResidual_finish_within {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (worker : Pr P T Q A U)
    (volume dst saved tmp : Fin T) (L : ℕ)
    (field ys tail rhsTail : List (Fin (A+4))) (hfieldLen : field.length = L) (hys : ys.length = L)
    (v v₁ : HS T Q A U) (S : Stacks T A) (n₁ cost depth W : ℕ)
    (hu₁ : v₁.user = v.user) (hn₁ : n₁ ≤ cost)
    (he₁ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+W) depth worker (mk v S) n₁
      (mk v₁ {S with R := (Function.update (Function.update S.R (placement.bank 93) rhsTail)
        (placement.bank 110) (ys++S.R (placement.bank 110)))}))
    (hreg : [volume,placement.bank 132,placement.bank 110,dst,saved,tmp,placement.bank 93].Nodup)
    (hvolume : (S.R volume).length = L) (hsource : S.R (placement.bank 132) = field++tail)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cost+finishReplicaCouplingRowCost L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(W+2*finishReplicaCouplingRowCost L))
        depth (.seq worker (finishReplicaCouplingRow volume (placement.bank 132) (placement.bank 110) dst saved tmp))
        (mk v S) m (mk v' (replicaResidualState placement dst tail rhsTail ys S)) := by
  have hr := hreg
  regs_ne hr
  let J : Stacks T A := {S with R := Function.update (Function.update S.R (placement.bank 93) rhsTail) (placement.bank 110) (ys++S.R (placement.bank 110))}
  obtain ⟨v₂,hu₂,he₂⟩ := finishReplicaCouplingRow_exec_within (body := body) volume (placement.bank 132)
    (placement.bank 110) dst saved tmp (by regs_nodup) L
    field ys tail (S.R (placement.bank 110)) hfieldLen hys v₁ J
    (by simpa [J,‹volume ≠ placement.bank 110›,‹volume ≠ placement.bank 93›] using hvolume)
    (by simpa [J,‹placement.bank 132 ≠ placement.bank 110›,‹placement.bank 132 ≠ placement.bank 93›] using hsource)
    (by simp [J])
    (by simpa [J,‹placement.bank 110 ≠ saved›.symm,‹saved ≠ placement.bank 93›] using hsaved)
    (by simpa [J,‹placement.bank 110 ≠ tmp›.symm,‹tmp ≠ placement.bank 93›] using htmp) depth
  have hsize := he₁.final
  change mnSize (mk v₁ J)+depth ≤ _ at hsize
  have hex : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(W+2*finishReplicaCouplingRowCost L)) depth
      (.seq worker (finishReplicaCouplingRow volume (placement.bank 132) (placement.bank 110) dst saved tmp))
      (mk v S) (n₁+finishReplicaCouplingRowCost L) _ :=
    .seq (he₁.mono (by intro d z hz; omega)) (he₂.mono (by intro d z hz; omega))
  refine ⟨v₂,n₁+finishReplicaCouplingRowCost L,hu₂.trans hu₁,by omega,hex.cast rfl ?_⟩
  exact congrArg (mk v₂) (replicaResidualState_finish placement volume dst saved tmp tail rhsTail ys S hreg)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
