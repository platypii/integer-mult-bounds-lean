module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinArchiveClasses
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaClassGroups

/-! Actual archive assembly followed by prepared class-major publication.
The join's exact frame supplies all publication readiness; time, workspace and
physical replica accuracy refer to the composed execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s width B : ℕ} [NeZero s] {P U : Type} {src dst : Fin T}

theorem joinedReplicaClassGroups_exec (body : P → Pr P T Q A U)
    (plans : CorePublicationClass s width → PreparedPublicationPlan T src dst) (clock lineRows saved : Fin T)
    (gs : List (CorePublicationClass s width))
    (hreg : ∀ g ∈ gs, ((plans g).support++[src,dst,clock,lineRows]).Nodup)
    (banks : List (Fin T)) (hnodup : banks.Nodup) (hsavedOff : src ≠ saved)
    (hoff : ∀ bank ∈ banks, bank ≠ src ∧ bank ≠ saved)
    (hbankOff : ∀ bank ∈ banks, ∀ g ∈ gs, bank ∉ (plans g).support)
    (hports : ∀ i ∈ [dst,clock,lineRows], i ≠ src ∧ i ∉ banks)
    (q w : ℕ) (hw : 0 < width) (hw1 : 1 ≤ w)
    (rows : CorePublicationClass s width → Fin B → ℕ → List GaussianInt)
    (padded : CorePublicationClass s width → Fin B → List (List GaussianInt))
    (missing : CorePublicationClass s width → ℕ) (borrowed : CorePublicationClass s width → List (Fin (A+4)))
    (hrows : ∀ g ∈ gs, ∀ j k, k ∈ g.indices → (rows g j k).length = g.length)
    (hpadded : ∀ g ∈ gs, ∀ j row, row ∈ padded g j → row.length = g.length)
    (hcount : ∀ g ∈ gs, ∀ j, missing g+g.indices.length = (padded g j).length)
    (hreal : ∀ g ∈ gs, ∀ j, (padded g j).flatten.drop (missing g*g.length) = (g.indices.map (rows g j)).flatten)
    (hcover : ∀ k ∈ coreIndices s width, ∃ g ∈ gs, k ∈ g.indices)
    (target : Fin B → ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ g ∈ gs, ∀ j k, k ∈ g.indices → PhaseCellInterface.ErrorOn (ownedCore s width k)
      (packedIntervalRead q w (coreStart width k) (cstream A w (rows g j k))) (target j) error)
    (ambient : Fin B → List (Fin (A+4))) (hambient : ∀ j, (ambient j).length = s*w)
    (X : List (Fin (A+4))) (data : Fin T → List (Fin (A+4)))
    (sourceTail outputTail : List (Fin (A+4)))
    (hconcat : X++banks.flatMap data = gs.flatMap (fun g => (List.ofFn fun j => cstream A w (padded g j).flatten).flatten)++sourceTail)
    (v : HS T Q A U) (S : Stacks T A)
    (hready : ∀ g ∈ gs, (plans g).Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      w (missing g) (borrowed g) S)
    (hclock : (S.R clock).length = B) (hline : (S.R lineRows).length = s)
    (hsrc : S.R src = X) (hsaved : S.R saved = []) (hbanks : ∀ bank ∈ banks, S.R bank = data bank)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail) :
    let joinCost := 4*banks.length*(X.length+(banks.flatMap data).length)+6*banks.length+1
    let publicationCost := replicaClassGroupsCost B w missing gs
    ∃ v' F n, v'.user = v.user ∧ n ≤ joinCost+publicationCost ∧
      Exec body (.seq (joinArchiveClasses src saved banks) (replicaClassGroupsProgram plans clock lineRows gs))
        (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ (∀ bank ∈ banks, F.R bank = []) ∧
      F.R dst = (List.ofFn fun j => corePublicationGroupsOutput w hw (fun g => rows g j) gs (ambient j)).flatten++outputTail ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → i ∉ banks → F.R i = S.R i) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+joinCost+2*publicationCost) depth
        (.seq (joinArchiveClasses src saved banks) (replicaClassGroupsProgram plans clock lineRows gs))
        (mk v S) n (mk v' F)) ∧
      ∀ j : Fin B, ∀ i, ‖pairedCellRead q w ((F.R dst).drop (j.val*(s*w))) i-target j i‖ ≤ error := by
  dsimp only
  obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hs,hclear,hi,ho,hl,hframe⟩ :=
    joinArchiveClasses_exec (body := body) src saved hsavedOff banks hnodup hoff X data v S hsrc hsaved hbanks
  have hreadyM : ∀ g ∈ gs, (plans g).Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      w (missing g) (borrowed g) M := by
    intro g hg
    apply (hready g hg).of_frame
    intro i hi
    apply hframe i ((plans g).support_off hi).1
    intro hb
    exact hbankOff i hb g hg hi
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs',hd,hi',ho',hl',hframe'⟩ := replicaClassGroups_exec body plans clock lineRows gs hreg
    w hw hw1 rows padded missing borrowed hrows hpadded hcount hreal ambient hambient sourceTail outputTail v₁ M hreadyM
    (by rw [hframe _ (hports clock (by simp)).1 (hports clock (by simp)).2]; exact hclock)
    (by rw [hframe _ (hports lineRows (by simp)).1 (hports lineRows (by simp)).2]; exact hline)
    (hs.trans hconcat) (by rw [hframe _ (hports dst (by simp)).1 (hports dst (by simp)).2]; exact hdst)
  refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hs',?_,hd,
    hi'.trans hi,ho'.trans ho,hl'.trans hl,?_,?_,?_⟩
  · intro bank hb
    have hbd : bank ≠ dst := by intro he; subst bank; exact (hports dst (by simp)).2 hb
    rw [hframe' bank (hoff bank hb).1 hbd]
    exact hclear bank hb
  · intro i his hid hib
    exact (hframe' i his hid).trans (hframe i his hib)
  · intro depth
    have hj := joinArchiveClasses_within he₁ hn₁ depth
    have hp := replicaClassGroups_within he₂ hn₂ depth
    have hm := hj.final
    apply ExecWithin.seq
    · exact hj.mono (by intro d z hz; omega)
    · exact hp.mono (by intro d z hz; omega)
  · exact replicaClassGroups_accuracy q w hw gs rows hrows hcover ambient hambient target error hgood (F.R dst) outputTail hd

/-- Class scheduling pays padding per replica and ambient movement per class.
Numerical setup and external exposure are not included in this movement bill. -/
theorem replicaClassGroupsCost_linear (w : ℕ) (hw : 1 ≤ w)
    (missing : CorePublicationClass s width → ℕ) (gs : List (CorePublicationClass s width)) :
    replicaClassGroupsCost B w missing gs ≤
      B*(21*(gs.map (fun g => missing g*g.length*w)).sum+93*gs.length*(s*w))+
      gs.length*(37*s*w+35)+1 := by
  induction gs with
  | nil => simp [replicaClassGroupsCost]
  | cons g gs ih =>
    have hb := PreparedPublicationPlan.replica_cost_le B s (missing g) g.length w (NeZero.pos s) hw
    simp only [replicaClassGroupsCost,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    nlinarith only [hb,ih]

/-- The four bulk/seam length classes have a fixed linear movement allowance. -/
theorem replicaClassGroupsCost_four_le (w : ℕ) (hw : 1 ≤ w)
    (missing : CorePublicationClass s width → ℕ) (gs : List (CorePublicationClass s width))
    (hcount : gs.length ≤ 4) :
    replicaClassGroupsCost B w missing gs ≤
      B*(21*(gs.map (fun g => missing g*g.length*w)).sum+372*(s*w))+148*s*w+141 := by
  have hb := replicaClassGroupsCost_linear (B := B) w hw missing gs
  have hv := Nat.mul_le_mul_right (s*w) hcount
  have hm := Nat.mul_le_mul_left B (show
      21*(gs.map (fun g => missing g*g.length*w)).sum+93*gs.length*(s*w) ≤
      21*(gs.map (fun g => missing g*g.length*w)).sum+372*(s*w) by nlinarith only [hv])
  have hs := Nat.mul_le_mul_right (37*s*w+35) hcount
  nlinarith only [hb,hm,hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
