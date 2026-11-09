module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactGroupedPublication
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

theorem exactGroupedArchivePublication_exec (body : P → Pr P T Q (prime+K) U)
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
    (routeReady : route.BankReady S)
    (hsource : S.R route.src = (batches.map (fun rows => cstream (prime+K) W rows.flatten)).flatten)
    (pubReady : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W ((2^d)^c-g.indices.length) borrowed S)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s) (depth : ℕ) :
    let bill := replicaPublicationCost Fs.length s ((2^d)^c-g.indices.length) g.length W+
      37*s*W+6*Fs.length+31
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' F n, v'.user = v.user ∧ n ≤ route.cost S+bill ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (route.stockAllowance+2*bill)) depth
        (.seq route.program (pub.replicaProgram clock lineRows)) (mk v S) n (mk v' F) ∧
      F.R route.src = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ route.src → r ≠ dst → F.R r = S.R r := by
  dsimp only
  obtain ⟨values,hlen,hbatches,hbytes,hcert⟩ := exactCoreTileRows g.indices Fs J batches hrows
    (fun k hk => ((mem_corePublicationIndices s width g.length k).mp (g.sublist.subset hk)).2)
  have hcast (i : Fin g.indices.length) := congrArg List.flatten
    (List.ofFn_congr hFs (fun j => cstream (prime+K) W (values i j)))
  have ready : route.Ready W (fun i j => values i (Fin.cast hFs.symm j)) S := by
    refine ⟨routeReady,?_⟩
    rw [hsource,hbytes]
    simp_rw [←hcast]
  obtain ⟨v',F,n,hu,hn,he,hs,hd,hgood,hi,ho,hl,hframe⟩ := exactGroupedPublication_exec
    body p W hW g hw hpacket hA route dst pub clock lineRows hports Fs hFs J values hcert hcapacity
    ambient hambient outputTail borrowed v S ready pubReady hdst hclock hline depth
  exact ⟨_,v',F,n,hu,hn,he,hs,hd,hgood,hi,ho,hl,hframe⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
