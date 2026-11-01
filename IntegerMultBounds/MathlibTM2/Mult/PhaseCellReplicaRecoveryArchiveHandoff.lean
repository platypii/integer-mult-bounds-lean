module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPreparationCursor
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove

/-! Move the actual first-pass residual archive into the preparation cursor.
The retained RHS is copied in its original order; the residual order is preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def replicaRecoveryArchiveHandoff (plan : ReplicaInteriorPlacement T)
    (worker : Fin 257 → Fin T) (reversed : Fin T) : Pr P T Q A U :=
  .seq (prepareReplicaRecoveryRhs plan (worker 93) reversed)
    (moveRightOrdered (plan.gather 125) (plan.gather 88) (worker 238))

theorem replicaRecoveryArchiveHandoff_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (X : ℕ → ZMod s → ℝ) (plan : ReplicaInteriorPlacement T)
    (worker : Fin 257 → Fin T) (hinj : Function.Injective worker) (reversed : Fin T)
    (hgrhs : ∀ k, plan.gather k ≠ worker 93)
    (hgres : ∀ k, plan.gather k ≠ worker 238)
    (hgrev : ∀ k, plan.gather k ≠ reversed) (hrev : worker 93 ≠ reversed)
    (buffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaRecoveryRhsHeaders H plan.gather buffers S) (hblank : S.R reversed = [])
    (Ds : List (ZMod s → GaussianInt)) (hlen : Ds.length = H.Fs.length)
    (harchive : S.R (plan.gather 125) = Ds.flatMap
      (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)))
    (hgood : ∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) Ds[j.val]) :
    let J := {S with R := Function.update S.R (worker 93) (H.Fs.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++S.R (worker 93))}
    let F := {J with R := Function.update (Function.update J.R (plan.gather 125) []) (worker 238) (S.R (plan.gather 125)++S.R (worker 238))}
    ∃ v' n, v'.user = v.user ∧
      n ≤ copyRowsOrderedCost H.Fs.length (H.span*H.wordWidth)+4*(H.Fs.length*(H.span*H.wordWidth))+4 ∧
      Exec body (replicaRecoveryArchiveHandoff plan worker reversed) (mk v S) n (mk v' F) ∧
      ReplicaRecoveryPreparationCursor H target X (S.R (worker 238)) (S.R (worker 93))
        (F.R (worker 125)) (F.R (worker 256)) 0 (embStk worker F) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, k ≠ worker 93 → k ≠ worker 238 → k ≠ plan.gather 125 → F.R k = S.R k) := by
  dsimp only
  let J := {S with R := Function.update S.R (worker 93) (H.Fs.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++S.R (worker 93))}
  let F := {J with R := Function.update (Function.update J.R (plan.gather 125) []) (worker 238) (S.R (plan.gather 125)++S.R (worker 238))}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareReplicaRecoveryRhs_exec (body := body) H plan (worker 93) reversed
    hgrhs hgrev hrev buffers v S headers hblank
  have hJ (k : Fin 126) : J.R (plan.gather k) = S.R (plan.gather k) :=
    Function.update_of_ne (hgrhs k) _ _
  have htmp : J.R (plan.gather 88) = [] := (hJ 88).trans (headers.fresh 88 (by simp))
  obtain ⟨v',hu₂,he₂⟩ := moveRightOrdered_exec (body := body)
    (plan.gather 125) (plan.gather 88) (worker 238) (plan.gather_injective.ne (by decide))
    (hgres 125) (hgres 88) v₁ J htmp
  have hlenArchive : (S.R (plan.gather 125)).length = H.Fs.length*(H.span*H.wordWidth) := by
    rw [harchive,List.length_flatMap]
    simp only [length_cstream,packedInterval_length _ H.span_fit,List.map_const',List.sum_replicate,hlen,smul_eq_mul]
  refine ⟨v',n₁+(4*(J.R (plan.gather 125)).length+4),hu₂.trans hu₁,?_,?_,?_,rfl,rfl,rfl,?_⟩
  · rw [hJ,hlenArchive]
    omega
  · have hres : J.R (worker 238) = S.R (worker 238) :=
      Function.update_of_ne (hinj.ne (by decide : (238 : Fin 257) ≠ 93)) _ _
    simpa only [replicaRecoveryArchiveHandoff,F,hJ,hres] using (Exec.seq he₁ he₂)
  · apply ReplicaRecoveryPreparationCursor.initial H target X (embStk worker F) Ds hlen
    · change F.R (worker 238) = _
      simp only [F,Function.update_self,harchive]
    · exact hgood
    · change F.R (worker 93) = _
      simp only [F,Function.update_of_ne (hinj.ne (by decide : (93 : Fin 257) ≠ 238)),
        Function.update_of_ne (hgrhs 125).symm,J,Function.update_self]

  · intro k h93 h238 h125
    simp only [Function.update_of_ne h93,Function.update_of_ne h238,Function.update_of_ne h125]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
