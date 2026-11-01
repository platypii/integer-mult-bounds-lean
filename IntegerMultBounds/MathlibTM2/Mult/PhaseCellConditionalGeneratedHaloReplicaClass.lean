module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedHaloReplicaClass
public import IntegerMultBounds.MathlibTM2.Host.WhenRightNonempty
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Generate class pages once, inspect their actual count, skip numerical work
for empty candidates, and retire the pages through the same suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def conditionalGeneratedHaloReplicaClass (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (placedPairedLocalHaloClass plan)
    (.seq (whenRightNonempty (plan.gather 116) (repeatableGatheredReplicaClass plan dst hR hQ))
      (releaseGatheredOriginPages plan))

def conditionalGeneratedHaloReplicaClassCost (p l N V origin span L s t u target rhsExp : ℕ) :=
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band origin (origin+span) L).length
  preparedPairedLocalHaloClassCost V s t band origin (origin+span) L+
    ((if B = 0 then 3 else repeatableGatheredReplicaClassCost p l N B V span L s t u target rhsExp+2)+
      releasePairedOriginPagesCost B V)

noncomputable def conditionalGeneratedHaloReplicaClassWorkspace {Q A : ℕ} {U : Type} (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp : ℕ) :=
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band origin (origin+span) L).length
  3*preparedPairedLocalHaloClassCost V s t band origin (origin+span) L+
    ((if B = 0 then 0 else repeatableGatheredReplicaClassWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp)+
      2*releasePairedOriginPagesCost B V)

theorem repeatableGatheredReplicaClass_firstAction (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) :
    FirstAction (peekR (plan.gather 114))
      (repeatableGatheredReplicaClass (P := P) (A := A) (U := U) plan dst hR hQ) := by
  repeat apply FirstAction.seq
  exact FirstAction.act

/-- Reuse the nonempty numerical trace and its exact endpoint. The prefix's
counter fact is supplied by the already proved page-generation contract. -/
theorem conditionalGeneratedHaloReplicaClass_of_nonempty_trace (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {z z' : Store (HΓ (T := T) A) (HS T Q A U)} {n depth bound : ℕ}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ bound) depth
      (generatedHaloReplicaClass plan dst hR hQ) z n z')
    (hcount : ∀ m state, Exec body (placedPairedLocalHaloClass plan) z m state → state.stk (.rt (plan.gather 116)) ≠ []) :
    ExecWithin body (fun d state => mnSize state+d ≤ bound) depth
      (conditionalGeneratedHaloReplicaClass plan dst hR hQ) z (n+2) z' := by
  exact guard_middle_exec_within (plan.gather 116) (plan.gather 114)
    (placedPairedLocalHaloClass plan) (repeatableGatheredReplicaClass plan dst hR hQ)
    (releaseGatheredOriginPages plan) (repeatableGatheredReplicaClass_firstAction plan dst hR hQ)
    he (fun state m h => hcount m state h)

/-- The concrete generated-page endpoint discharges the guard premise by
execution uniqueness; the numerical trace and all of its postconditions survive. -/
theorem conditionalGeneratedHaloReplicaClass_of_generated_pages (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (V s t band a b L : ℕ) (S : Stacks T A) (v v₁ : HS T Q A U)
    {z' : Store (HΓ (T := T) A) (HS T Q A U)} {m n depth bound : ℕ}
    (hpages : Exec body (placedPairedLocalHaloClass plan) (mk v S) m
      (mk v₁ (pairedLocalHaloClassBank plan S V s t band a b L)))
    (hne : haloLengthGroup s t band a b L ≠ [])
    (he : ExecWithin body (fun d state => mnSize state+d ≤ bound) depth
      (generatedHaloReplicaClass plan dst hR hQ) (mk v S) n z') :
    ExecWithin body (fun d state => mnSize state+d ≤ bound) depth
      (conditionalGeneratedHaloReplicaClass plan dst hR hQ) (mk v S) (n+2) z' := by
  apply conditionalGeneratedHaloReplicaClass_of_nonempty_trace plan dst hR hQ he
  intro steps state hstate
  have hsame := (hpages.unique hstate).2
  rw [← hsame]
  simpa [pairedLocalHaloClassBank] using hne

theorem conditionalGeneratedHaloReplicaClassCost_nonempty
    (p l N V origin span L s t u target rhsExp : ℕ)
    (hB : (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length ≠ 0) :
    conditionalGeneratedHaloReplicaClassCost p l N V origin span L s t u target rhsExp =
      generatedHaloReplicaClassCost p l N V origin span L s t u target rhsExp+2 := by
  simp only [conditionalGeneratedHaloReplicaClassCost,generatedHaloReplicaClassCost,hB,ite_false]
  omega

theorem conditionalGeneratedHaloReplicaClassWorkspace_nonempty (hQ : SS.states ≤ Q)
    (R K p l N V origin span L s t u target rhsExp : ℕ)
    (hB : (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length ≠ 0) :
    conditionalGeneratedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp =
      generatedHaloReplicaClassWorkspace (A := A) (U := U) hQ R K p l N V origin span L s t u target rhsExp := by
  simp only [conditionalGeneratedHaloReplicaClassWorkspace,generatedHaloReplicaClassWorkspace,hB,ite_false]

/-- A candidate with no cells performs only shared control work and restores
all tapes, with no numerical-bank, RHS, accuracy or coefficient assumptions. -/
theorem conditionalGeneratedHaloReplicaClass_empty_exec_within (plan : ReplicaInteriorPlacement T)
    (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (V s t band a b L : ℕ) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hbs : b ≤ s)
    (hL : 0 < L) (hLwidth : L < 2^V) (hA : 4 ≤ A)
    (hempty : haloLengthGroup s t band a b L = []) (v : HS T Q A U) (S : Stacks T A)
    (hsSrc : (S.R (plan.gather 97)).length = s) (htSrc : (S.R (plan.gather 98)).length = t)
    (hbSrc : (S.R (plan.gather 100)).length = band) (haSrc : (S.R (plan.gather 111)).length = a)
    (hbEndSrc : (S.R (plan.gather 113)).length = b) (hLSrc : (S.R (plan.gather 102)).length = L)
    (hV : (S.R (plan.gather 115)).length = V)
    (hfresh : ∀ k ∈ [(104 : Fin 126),105,106,116], S.R (plan.gather k) = [])
    (hblank : ∀ k : Fin 126, k.val < 31 → S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedPairedLocalHaloClassCost V s t band a b L+23 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*preparedPairedLocalHaloClassCost V s t band a b L+40)) depth
        (conditionalGeneratedHaloReplicaClass plan dst hR hQ) (mk v S) n (mk v' S) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedPairedLocalHaloClass_exec_width (body := body) plan V s t band a b L
    hwide hs hst hband hab hbs hL hLwidth hA v S hsSrc htSrc hbSrc haSrc hbEndSrc hLSrc hV
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hfresh _ (by simp)) hblank depth
  have hcount : S.R (plan.gather 116) = [] := hfresh _ (by simp)
  have hM : pairedLocalHaloClassBank plan S V s t band a b L = S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = plan.gather 116
    · subst k
      simp [pairedLocalHaloClassBank,hempty,hcount]
    · simp [pairedLocalHaloClassBank,haloOriginPackets,haloPackedOffsets,haloOrigins,
        hempty,hk]
  rw [hM] at he₁
  let v₂ := {v₁ with flag := false}
  have he₂ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth) depth
      (whenRightNonempty (plan.gather 116) (repeatableGatheredReplicaClass plan dst hR hQ))
      (mk v₁ S) 3 (mk v₂ S) :=
    whenRightNonempty_empty_within (plan.gather 116) _ (mk v₁ S) depth _ (by rfl) hcount
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := releaseGatheredOriginPages_exec_within (body := body) plan V s t band a b L
    v₂ S S hV
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hfresh _ (by simp))
    (by rw [hM]) depth
  have hrestore : releasedGatheredOriginPagesBank plan (pairedLocalHaloClassBank plan S V s t band a b L) S = S :=
    pairedLocalHaloClassBank_restore plan S V s t band a b L hcount
  rw [hM] at hrestore
  rw [hrestore] at he₃
  have hn₃' : n₃ ≤ 20 := by simpa [hempty,releasePairedOriginPagesCost] using hn₃
  have he₃' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+40) depth
      (releaseGatheredOriginPages plan) (mk v₂ S) n₃ (mk v₃ S) := by
    simpa [hempty,releasePairedOriginPagesCost,mnSize] using he₃
  refine ⟨v₃,n₁+(3+n₃),hu₃.trans hu₁,by omega,?_⟩
  refine .seq (he₁.mono ?_) (.seq (he₂.mono ?_) (he₃'.mono ?_))
  all_goals intro d z hz; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
