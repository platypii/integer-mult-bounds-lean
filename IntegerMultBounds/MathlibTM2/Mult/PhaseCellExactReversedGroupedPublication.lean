module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactGroupedArchivePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreArchiveCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileSourceFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTilePlanStock
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! Transpose and publish one exact core class in a single physical trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q K c d s width : ℕ} [NeZero s] {P U : Type}

theorem exactReversedGroupedPublication_exec (body : P → Pr P T Q (prime+K) U)
    (p W : ℕ) (hW : 1 ≤ W) (g : CorePublicationClass s width) (hw : 0 < width)
    (hpacket : 0 < g.length*W) (hA : 4 ≤ prime+K)
    (route : ArchiveTilePlan t₀ T Q c d (g.length*W))
    (dst : Fin T) (pub : PreparedPublicationPlan T route.src dst) (clock lineRows : Fin T)
    (hports : (pub.support++[route.src,dst,clock,lineRows]).Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^d)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (batches : List (List (List GaussianInt)))
    (hrows : List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows)
      g.indices batches)
    (hcapacity : g.indices.length ≤ (2^d)^c)
    (ambient : Fin Fs.length → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*W)
    (outputTail borrowed : List (Fin (prime+K+4))) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (count savedCount rowWidth source archive saved tmp : Fin T)
    (hcopyReg : [count,savedCount,rowWidth,source,archive,route.src,saved,tmp].Nodup)
    (hcount : (S.R count).length = g.indices.length)
    (hrowWidth : (S.R rowWidth).length = Fs.length*(g.length*W))
    (sourceTail : List (Fin (prime+K+4)))
    (hfresh : ∀ r ∈ [savedCount,archive,saved,tmp], S.R r = [])
    (hrouteBlank : S.R route.src = [])
    (routeReady : route.BankReady S)
    (hsource : S.R source = (batches.map (fun rows => cstream (prime+K) W rows.flatten)).reverse.flatten++sourceTail)
    (pubReady : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W ((2^d)^c-g.indices.length) borrowed S)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s) (depth : ℕ) :
    let bill := replicaPublicationCost Fs.length s ((2^d)^c-g.indices.length) g.length W+
      37*s*W+6*Fs.length+31
    let copyBill := reverseCopyRowsCost g.indices.length (Fs.length*(g.length*W))
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' F n, v'.user = v.user ∧ n ≤ copyBill+(route.cost S+bill) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (2*copyBill+(route.stockAllowance+2*bill))) depth
        (.seq (reverseCopyRows count savedCount rowWidth source archive route.src saved tmp)
          (.seq route.program (pub.replicaProgram clock lineRows))) (mk v S) n (mk v' F) ∧
      F.R route.src = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ dst → F.R r = S.R r := by
  dsimp only
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := exactCoreArchive_copy_exec (body := body)
    g.indices Fs J batches hrows
    (fun k hk => ((mem_corePublicationIndices s width g.length k).mp (g.sublist.subset hk)).2)
    count savedCount rowWidth source archive route.src saved tmp hcopyReg sourceTail v S hcount hrowWidth
    hsource hfresh depth
  let ordered := (batches.map (fun rows => cstream (prime+K) W rows.flatten)).flatten
  let M : Stacks T (prime+K) := {S with R := Function.update S.R route.src ordered}
  have heCopy : ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
      2*reverseCopyRowsCost g.indices.length (Fs.length*(g.length*W))) depth
      (reverseCopyRows count savedCount rowWidth source archive route.src saved tmp) (mk v S) n₁ (mk v₁ M) := by
    simpa only [hrouteBlank,List.append_nil] using he₁
  have hroute : route.BankReady M := routeReady.with_source ordered
  have hpub := pubReady.of_frame (F := M) (by
    intro r hr
    exact Function.update_of_ne (pub.support_off hr).1 _ _)
  have htail : [route.src,dst,clock,lineRows].Nodup := (List.nodup_append.mp hports).2.1
  have hclockOff : clock ≠ route.src := by
    intro heq
    exact (List.nodup_cons.mp htail).1 (heq ▸ (by simp : clock ∈ [dst,clock,lineRows]))
  have hlineOff : lineRows ≠ route.src := by
    intro heq
    exact (List.nodup_cons.mp htail).1 (heq ▸ (by simp : lineRows ∈ [dst,clock,lineRows]))
  obtain ⟨lines,v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,hgood,hi,ho,hl,hframe⟩ := exactGroupedArchivePublication_exec
    body p W hW g hw hpacket hA route dst pub clock lineRows hports Fs hFs J batches hrows hcapacity
    ambient hambient outputTail borrowed v₁ M hroute (by simp [M,ordered]) hpub
    (by simpa only [M,Function.update_of_ne pub.src_ne_dst.symm] using hdst)
    (by simpa only [M,Function.update_of_ne hclockOff] using hclock)
    (by simpa only [M,Function.update_of_ne hlineOff] using hline) depth
  have hcost : route.cost M = route.cost S := by
    have hstable (j) : M.R (route.ι j) = S.R (route.ι j) :=
      Function.update_of_ne (route.hsourceOff j) _ _
    simp only [ArchiveTilePlan.cost,hstable]
  rw [hcost] at hn₂
  refine ⟨lines,v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ heCopy he₂,hs,hd,hgood,hi,ho,hl,?_⟩
  intro r hrd
  by_cases hr : r = route.src
  · subst r
    exact hs.trans hrouteBlank.symm
  · exact (hframe r hr hrd).trans (Function.update_of_ne hr _ _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
