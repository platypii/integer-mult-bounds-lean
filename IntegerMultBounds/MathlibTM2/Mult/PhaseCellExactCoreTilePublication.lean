module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreTileRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaPublication

/-! Publish the actual padded transpose result as one grouped core class.
Padding and replica validity come from the result, never separate row premises. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s width : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem exactCoreTilePublication_exec {src dst : Fin T}
    (plan : PreparedPublicationPlan T src dst) (clock lineRows : Fin T)
    (hports : (plan.support++[src,dst,clock,lineRows]).Nodup)
    (p W : ℕ) (hW : 1 ≤ W) (g : CorePublicationClass s width) (hw : 0 < width)
    (Fs : List (ZMod s → GaussianInt)) (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (values : Fin g.indices.length → Fin Fs.length → List GaussianInt)
    (hrows : ∀ i : Fin g.indices.length,
      ExactCoreRows (A := A) p W width g.indices[i] Fs J (List.ofFn (values i)))
    (tile : ArchiveTilePlan.Result g.length values)
    (ambient : Fin Fs.length → List (Fin (A+4)))
    (hambient : ∀ j, (ambient j).length = s*W)
    (sourceTail outputTail borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W (tile.capacity-g.indices.length) borrowed S)
    (hsrc : S.R src = (List.ofFn fun j => cstream A W
      (List.ofFn fun i => tile.padded i j).flatten).flatten++sourceTail)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s) (depth : ℕ) :
    let lines := List.ofFn fun j => g.output W hw (indexedCoreRows g.indices rfl values j) (ambient j)
    let bill := replicaPublicationCost Fs.length s (tile.capacity-g.indices.length) g.length W+
      37*s*W+6*Fs.length+31
    ∃ v' F n, v'.user = v.user ∧ n ≤ bill ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*bill) depth
        (plan.replicaProgram clock lineRows) (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ src → r ≠ dst → F.R r = S.R r := by
  dsimp only
  let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
  let replicas := List.ofFn fun j => tile.publicationReplica rfl (ambient j) j
  have hvalid : ∀ r ∈ replicas, r.Valid windows W (tile.capacity-g.indices.length) := by
    intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact tile.publicationReplica_valid rfl W hw (ambient j) (hambient j) j
  have hinput := tile.publicationReplica_inputs (A := A) rfl W ambient
  have hn : replicas.length = Fs.length := by simp [replicas]
  obtain ⟨v',F,n,huser,htime,he,hs,hd,hi,ho,hl,hframe⟩ := plan.replica_exec (body := body)
    clock lineRows hports windows W (tile.capacity-g.indices.length) hW replicas hvalid
    sourceTail outputTail borrowed v S hready (by rw [hinput]; exact hsrc)
    (by simpa only [replicas,List.flatMap,List.map_ofFn,Function.comp_def,ArchiveTilePlan.Result.publicationReplica] using hdst)
    (by rw [hn]; exact hclock) hline
  have ht : n ≤ replicaPublicationCost Fs.length s (tile.capacity-g.indices.length) g.length W+
      37*s*W+6*Fs.length+31 := by simpa only [hn] using htime
  refine ⟨v',F,n,huser,ht,PreparedPublicationPlan.replica_within he ht depth,hs,?_,
    exactCoreClass_output_bank g hw Fs J values hrows ambient hambient,hi,ho,hl,hframe⟩
  simpa only [replicas,List.flatMap,List.map_ofFn,Function.comp_def,
    PublicationReplica.output,PublicationReplica.words,ArchiveTilePlan.Result.publicationReplica,
    ArchiveTilePlan.Result.coreRows,CorePublicationClass.output,windows] using hd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
