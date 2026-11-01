module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizeRecoveryOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryParameterQueue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryMagnitude

/-! Execute the existing final-rounding/publication program on cropped recovery
packets. Magnitude, common width and locality follow from the core job. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace RecoveryNormalizePlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def normalizationValues (r : PackedNormalizedJob A s) : Fin 8 → ℕ := ![r.p,r.u,r.l,r.targetOut,s,r.t,r.a,r.b]

def queueTimeCost (r : PackedNormalizedJob A s) : ℕ :=
  (List.ofFn (normalizationValues r)).sum*(4*r.Bcore+10)+8*(8*r.Bcore+12)+1

def fromUnaryProgram (plan : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue plan) : Pr P T Q A U :=
  .seq queue.program plan.finishedProgram

theorem fromUnary_exec (plan : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue plan) (hA : 4 ≤ A) (r : PackedNormalizedJob A s)
    (Ds : List (ZMod s → GaussianInt)) (oldTail tail : List (Fin (A+4)))
    (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (plan.scalar .wr) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.scalar i) = [])
    (hvalues : ∀ i, (S.R (queue.parameters i)).length = normalizationValues r i)
    (hqueueBlank : ∀ k ∈ [queue.word,queue.saved,queue.tmp], S.R k = [])
    (hp : (S.R plan.precision).length = r.p) (hW : (S.R plan.wide).length = r.W)
    (hrows : (S.R plan.rows).length = coreLength s r.coreWidth r.k)
    (hN : (S.R plan.replicas).length = Ds.length)
    (hblank : ∀ k ∈ [plan.count,plan.work,plan.saved,plan.tmp,plan.sp,plan.sg,plan.cy], S.R k = [])
    (hheaders : ∀ i, S.R (plan.ports i) = [])
    (hinputWidth : (S.R plan.inputWidth).length = coreLength s r.coreWidth r.k*(2*r.q+8))
    (hsrc : S.R plan.src = (Ds.map (fun D => cstream A (2*r.q+8)
      (ownedCoreWords r.coreWidth r.k D))).flatten++tail)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
      (packedIntervalRead r.q (2*r.q+8) (coreStart r.coreWidth r.k)
        (cstream A (2*r.q+8) (ownedCoreWords r.coreWidth r.k D)++oldTail)) z (1/(2 : ℝ)^r.targetOut))
      (r.Fs.map (componentSolution r.localSolution)).reverse Ds) :
    let Gs := Ds.map (fun D i => finalRoundWord (2*r.q+8) r.q r.p (inverseNormalizationShift r.p) (D i))
    Gs.length = Ds.length ∧
    ∃ v' n, v'.user = v.user ∧
      n ≤ queueTimeCost r+timeCost r Ds.length ∧
      Exec body (plan.fromUnaryProgram queue) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.inputWidth []) plan.src
          ((Gs.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++tail))}) ∧
      List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s r.coreWidth r.k)
        (packedIntervalRead r.p r.W (coreStart r.coreWidth r.k)
          (cstream A r.W (ownedCoreWords r.coreWidth r.k D)++tail)) (r.rowTarget F) r.rowError) r.Fs.reverse Gs ∧
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(8*(2*(4*r.Bcore+4))+13*timeCost r Ds.length))
        depth (plan.fromUnaryProgram queue) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R plan.inputWidth []) plan.src
          ((Gs.map (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++tail))}) := by
  dsimp only
  have hr := plan.regs
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := binaryHeaderQueue_exec (body := body) (plan.scalar .wr)
    queue.word queue.saved queue.tmp plan.header queue.carry (List.ofFn queue.parameters)
    (by intro k hk; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk; exact queue.regs i) v S hqueueBlank 0
  have hcost : binaryHeaderQueueCost S.R (S.R (plan.scalar .wr)).length (List.ofFn queue.parameters) = queueTimeCost r := by
    rw [binaryHeaderQueueCost_eq,hwidth,hwl]
    simp only [List.map_ofFn,Function.comp_def,hvalues,List.length_ofFn,queueTimeCost]
  rw [hcost] at hn₁
  have hpacket : (List.ofFn queue.parameters).flatMap
      (fun k => binSyms (A := A) (S.R (plan.scalar .wr)).length (S.R k).length) =
      (inverseParameterWords r.p r.u r.l r.targetOut s r.t r.a r.b).flatMap (fun i => binSyms r.Bcore i.2) := by
    rw [hwidth,hwl]
    simp only [List.flatMap,List.map_ofFn,Function.comp_def,hvalues]
    rfl
  rw [hpacket] at he₁
  simp only [List.length_ofFn,hwidth,hwl] at he₁
  change ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+8*(2*(4*r.Bcore+4)))
    0 _ _ _ _ at he₁
  let F : Stacks T A := {S with R := (Function.update S.R plan.header
    ((inverseParameterWords r.p r.u r.l r.targetOut s r.t r.a r.b).flatMap
      (fun i => binSyms r.Bcore i.2)++S.R plan.header))}
  have hF (k : Fin T) (hk : k ≠ plan.header) : F.R k = S.R k := Function.update_of_ne hk _ _
  obtain ⟨hlen,v₂,n₂,hu₂,hn₂,he₂,haccuracy,htrace₂⟩ := plan.exec hA r Ds oldTail tail (S.R plan.header) wl hwl v₁ F
    (by rw [hF _ (plan.header_off .wr)]; exact hwidth)
    (by intro i hi; rw [hF _ (plan.header_off i)]; exact hscalar i hi)
    (by simp only [F,Function.update_self])
    (by rw [hF _ ‹plan.header ≠ plan.precision›.symm]; exact hp)
    (by rw [hF _ ‹plan.header ≠ plan.wide›.symm]; exact hW)
    (by rw [hF _ ‹plan.header ≠ plan.rows›.symm]; exact hrows)
    (by rw [hF _ ‹plan.header ≠ plan.replicas›.symm]; exact hN)
    (by
      intro k hk
      have hoff : k ≠ plan.header := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)
      rw [hF k hoff]; exact hblank k hk)
    (by
      intro i
      have hoff : plan.ports i ≠ plan.header := by fin_cases i <;> exact Ne.symm (by assumption)
      rw [hF _ hoff]; exact hheaders i)
    (by rw [hF _ ‹plan.header ≠ plan.inputWidth›.symm]; exact hinputWidth)
    (by rw [hF _ ‹plan.header ≠ plan.src›.symm]; exact hsrc) hgood
  let output := ((Ds.map (fun D i => finalRoundWord (2*r.q+8) r.q r.p (inverseNormalizationShift r.p) (D i))).map
    (fun D => cstream A r.W (ownedCoreWords r.coreWidth r.k D))).flatten++tail
  have hfinal : {F with R := Function.update (Function.update (Function.update F.R plan.inputWidth [])
      plan.header (S.R plan.header)) plan.src output} =
      {S with R := Function.update (Function.update S.R plan.inputWidth []) plan.src output} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    funext k
    change Function.update (Function.update (Function.update F.R plan.inputWidth []) plan.header (S.R plan.header))
      plan.src output k = _
    by_cases hk : k = plan.src
    · subst k; simp only [Function.update_self]
    · by_cases hh : k = plan.header
      · subst k; simp [‹plan.header ≠ plan.src›,‹plan.header ≠ plan.inputWidth›]
      · simp [F,Function.update_apply,hk,hh]
  change Exec body plan.finishedProgram (Host.mk v₁ F) n₂
    (Host.mk v₂ {F with R := Function.update (Function.update (Function.update F.R plan.inputWidth [])
      plan.header (S.R plan.header)) plan.src output}) at he₂
  rw [hfinal] at he₂
  refine ⟨hlen,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁.toExec he₂,haccuracy,?_⟩
  intro depth
  have ht₂ := htrace₂ 0
  change ExecWithin body _ 0 _ _ n₂
    (Host.mk v₂ {F with R := Function.update (Function.update (Function.update F.R plan.inputWidth [])
      plan.header (S.R plan.header)) plan.src output}) at ht₂
  rw [hfinal] at ht₂
  have ht := mn_seq_within_add he₁ ht₂
  have hshift := ht.shift depth (J := fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
    (8*(2*(4*r.Bcore+4))+13*timeCost r Ds.length)) (by intro d z hz; omega)
  simpa only [fromUnaryProgram,RecoveryParameterQueue.program,Nat.zero_add,output] using hshift

end RecoveryNormalizePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
