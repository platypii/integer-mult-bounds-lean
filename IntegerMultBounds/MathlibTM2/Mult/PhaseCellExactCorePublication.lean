module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamPublicationPending

/-! Publish shared exact core rows with the existing restoring replica sweep.
The numerical invariant advances on the very lines written by that sweep. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s width : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem ExactCoreRows.publication_rows {p W k : ℕ}
    {Fs : List (ZMod s → GaussianInt)} {J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)}
    {rows : List (List GaussianInt)} (h : ExactCoreRows (A := A) p W width k Fs J rows) :
    List.Forall₂ (fun target row => row.length = coreLength s width k ∧
      (∀ i ∈ ownedCore s width k, ‖packedIntervalRead p W (coreStart width k) (cstream A W row) i‖ ≤ 1) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (packedIntervalRead p W (coreStart width k) (cstream A W row)) target (3/(2 : ℝ)^p))
      (inversePublicationTargets p Fs.reverse J) rows := by
  simp only [inversePublicationTargets,List.reverse_reverse,List.forall₂_map_left_iff]
  have hlen := h.2.1
  have hall := h.2.2
  clear h
  induction hall with
  | nil => exact .nil
  | @cons F row Fs rows hgood htail ih =>
    exact .cons ⟨hlen row (by simp),hgood⟩ (ih (fun xs hx => hlen xs (by simp [hx])))

theorem exactCorePublication_exec {src dst : Fin T}
    (plan : PreparedPublicationPlan T src dst) (clock lineRows : Fin T)
    (hports : (plan.support++[src,dst,clock,lineRows]).Nodup)
    (p W k : ℕ) (hW : 1 ≤ W) (hw : 0 < width) (hk : k ∈ coreIndices s width)
    (Fs : List (ZMod s → GaussianInt)) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (hrows : ExactCoreRows (A := A) p W width k Fs J rows)
    (gs : List (CorePublicationClass s width)) (ambient : List (List (Fin (A+4))))
    (hambient : ∀ line ∈ ambient, line.length = s*W)
    (hpending : PublicationBankPending (singletonCorePublication s width k hk::gs) p W
      (inversePublicationTargets p Fs.reverse J) (3/(2 : ℝ)^p) ambient)
    (sourceTail outputTail borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.Ready (singletonCoreWindows hw hk) W 0 borrowed S)
    (hsrc : S.R src = cstream A W rows.flatten++sourceTail)
    (hdst : S.R dst = ambient.flatten++outputTail)
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s) (depth : ℕ) :
    let lines := List.zipWith (fun row line =>
      (singletonCorePublication s width k hk).output W hw (fun _ => row) line) rows ambient
    ∃ v' F n, v'.user = v.user ∧
      n ≤ replicaPublicationCost Fs.length s 0 (coreLength s width k) W+37*s*W+6*Fs.length+31 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*(replicaPublicationCost Fs.length s 0 (coreLength s width k) W+37*s*W+6*Fs.length+31)) depth
        (plan.replicaProgram clock lineRows) (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = lines.flatten++outputTail ∧
      PublicationBankPending gs p W (inversePublicationTargets p Fs.reverse J) (3/(2 : ℝ)^p) lines ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ src → r ≠ dst → F.R r = S.R r := by
  dsimp only
  have hlen : rows.length = ambient.length := by
    have h := hpending.length_eq
    simpa only [inversePublicationTargets,List.length_map,List.length_reverse,hrows.1] using h
  obtain ⟨hn,ha,hinput,hpairs,hvalid⟩ := singletonPublicationReplicas_spec
    (singletonCoreWindows hw hk) (by rw [singletonCoreWindows_origins]; rfl) W rows ambient
    hlen hrows.2.1 hambient
  let replicas := singletonPublicationReplicas rows ambient
  have hreplicas : replicas.length = Fs.length := hn.trans hrows.1
  obtain ⟨v',F,n,huser,htime,he,hs,hd,hi,ho,hl,hframe⟩ := plan.replica_exec (body := body)
    clock lineRows hports (singletonCoreWindows hw hk) W 0 hW replicas hvalid
    sourceTail outputTail borrowed v S hready (by rw [hinput]; exact hsrc)
    (by simpa only [replicas,List.flatMap,ha] using hdst)
    (by rw [hreplicas]; exact hclock) hline
  have ht : n ≤ replicaPublicationCost Fs.length s 0 (coreLength s width k) W+37*s*W+6*Fs.length+31 := by
    simpa only [hreplicas] using htime
  refine ⟨v',F,n,huser,ht,PreparedPublicationPlan.replica_within he ht depth,hs,?_,?_,hi,ho,hl,hframe⟩
  · simpa only [replicas,singletonPublicationReplicas_class_output] using hd
  · exact singletonPublication_bank_pending hw hk gs p W (3/(2 : ℝ)^p)
      _ rows ambient hrows.publication_rows hpending

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
