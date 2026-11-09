module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCorePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreRowsWiden
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedReplicaPublication
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
  IntegerMultBounds.MathlibTM2.LayerMachine
variable {T Q A s width : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem widenedExactCorePublication_exec {src dst : Fin T}
    (plan : PreparedPublicationPlan T src dst) (clock lineRows : Fin T)
    (hports : (plan.support++[src,dst,clock,lineRows]).Nodup)
    (wide word count work saved tmp extra : Fin T)
    (hreg : [wide,word,count,src,work,saved,tmp,extra].Nodup)
    (p w W k : ℕ) (hA : 4 ≤ A) (hwNarrow : 1 ≤ w) (hW : w ≤ W) (hw : 0 < width) (hk : k ∈ coreIndices s width)
    (Fs : List (ZMod s → GaussianInt)) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (hrows : ExactCoreRows (A := A) p w width k Fs J rows)
    (gs : List (CorePublicationClass s width)) (ambient : List (List (Fin (A+4))))
    (hambient : ∀ line ∈ ambient, line.length = s*W)
    (hpending : PublicationBankPending (singletonCorePublication s width k hk::gs) p W
      (inversePublicationTargets p Fs.reverse J) (3/(2 : ℝ)^p) ambient)
    (sourceTail outputTail borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.Ready (singletonCoreWindows hw hk) W 0 borrowed S)
    (hsrc : S.R src = cstream A w rows.flatten++sourceTail)
    (hdst : S.R dst = ambient.flatten++outputTail)
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s)
    (hwide : (S.R wide).length = W) (hword : (S.R word).length = w)
    (hcount : (S.R count).length = rows.flatten.length*w)
    (hblank : ∀ r ∈ [work,saved,tmp,extra], S.R r = []) (depth : ℕ) :
    let lines := List.zipWith (fun row line =>
      (singletonCorePublication s width k hk).output W hw (fun _ => row) line) (rows.map (List.map (symZ w))) ambient
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (widenPackedPrefixCost w W rows.flatten.length+(replicaPublicationCost Fs.length s 0 (coreLength s width k) W+37*s*W+6*Fs.length+31)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        13*((widenPackedPrefixCost w W rows.flatten.length+(replicaPublicationCost Fs.length s 0 (coreLength s width k) W+37*s*W+6*Fs.length+31)))) depth
        (.seq (widenPackedPrefix wide word count src work saved tmp extra)
          (plan.replicaProgram clock lineRows)) (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = lines.flatten++outputTail ∧
      PublicationBankPending gs p W (inversePublicationTargets p Fs.reverse J) (3/(2 : ℝ)^p) lines ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ src → r ≠ dst → F.R r = S.R r := by
  dsimp only
  let wideRows := rows.map (List.map (symZ w))
  have hwideRows := hrows.widen hA hwNarrow hW
  have hlen : wideRows.length = ambient.length := by
    have h := hpending.length_eq
    simpa only [inversePublicationTargets,wideRows,List.length_map,List.length_reverse,hrows.1] using h
  obtain ⟨hn,ha,hinput,hpairs,hvalid⟩ := singletonPublicationReplicas_spec
    (singletonCoreWindows hw hk) (by rw [singletonCoreWindows_origins]; rfl) W wideRows ambient
    hlen hwideRows.2.1 hambient
  let replicas := singletonPublicationReplicas wideRows ambient
  have hreplicas : replicas.length = Fs.length := hn.trans hwideRows.1
  obtain ⟨v',F,n,huser,htime,he,hs,hd,hi,ho,hl,hframe⟩ := widenedReplicaPublication_exec body
    plan clock lineRows hports wide word count work saved tmp extra hreg
    (singletonCoreWindows hw hk) w W hwNarrow hW rows.flatten replicas hvalid
    (by simpa only [wideRows,List.map_flatten] using hinput)
    sourceTail outputTail borrowed v S hready hwide hword hcount hsrc
    (by simpa only [replicas,List.flatMap,ha] using hdst)
    (by rw [hreplicas]; exact hclock) hline hblank
  have ht : n ≤ widenPackedPrefixCost w W rows.flatten.length+
      (replicaPublicationCost Fs.length s 0 (coreLength s width k) W+37*s*W+6*Fs.length+31) := by
    simpa only [hreplicas] using htime
  refine ⟨v',F,n,huser,ht,?_,hs,?_,?_,hi,ho,hl,hframe⟩
  · exact widenedReplicaPublication_within body plan clock lineRows wide word count work saved tmp extra
      v v' S F n _ depth he ht
  · simpa only [replicas,wideRows,singletonPublicationReplicas_class_output] using hd
  · exact singletonPublication_bank_pending hw hk gs p W (3/(2 : ℝ)^p)
      _ wideRows ambient hwideRows.publication_rows hpending

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
