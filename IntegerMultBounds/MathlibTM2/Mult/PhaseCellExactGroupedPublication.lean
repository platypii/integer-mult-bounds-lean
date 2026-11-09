module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreTilePublication
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

theorem exactGroupedPublication_exec (body : P → Pr P T Q (prime+K) U)
    (p W : ℕ) (hW : 1 ≤ W) (g : CorePublicationClass s width) (hw : 0 < width)
    (hpacket : 0 < g.length*W) (hA : 4 ≤ prime+K)
    (route : ArchiveTilePlan t₀ T Q c d (g.length*W))
    (dst : Fin T) (pub : PreparedPublicationPlan T route.src dst) (clock lineRows : Fin T)
    (hports : (pub.support++[route.src,dst,clock,lineRows]).Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^d)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (values : Fin g.indices.length → Fin Fs.length → List GaussianInt)
    (hrows : ∀ i : Fin g.indices.length,
      ExactCoreRows (A := (prime+K)) p W width g.indices[i] Fs J (List.ofFn (values i)))
    (hcapacity : g.indices.length ≤ (2^d)^c)
    (ambient : Fin Fs.length → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*W)
    (outputTail borrowed : List (Fin (prime+K+4))) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (routeReady : route.Ready W (fun i j => values i (Fin.cast hFs.symm j)) S)
    (pubReady : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W ((2^d)^c-g.indices.length) borrowed S)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s) (depth : ℕ) :
    let lines := List.ofFn fun j => g.output W hw (indexedCoreRows g.indices rfl values j) (ambient j)
    let bill := replicaPublicationCost Fs.length s ((2^d)^c-g.indices.length) g.length W+
      37*s*W+6*Fs.length+31
    ∃ v' F n, v'.user = v.user ∧ n ≤ route.cost S+bill ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (route.stockAllowance+2*bill)) depth
        (.seq route.program (pub.replicaProgram clock lineRows)) (mk v S) n (mk v' F) ∧
      F.R route.src = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ route.src → r ≠ dst → F.R r = S.R r := by
  dsimp only
  have hlength : ∀ i j, (values i j).length = g.length := by
    intro i j
    have hlen := (hrows i).2.1 _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    have hcore := (mem_corePublicationIndices s width g.length _).mp
      (g.sublist.subset (List.getElem_mem i.isLt))
    exact hlen.trans hcore.2
  obtain ⟨padded,hp,hreal,v₁,n₁,hu₁,hn₁,he₁⟩ := route.exec_within body hA hpacket g.length W rfl
    hcapacity (fun i j => values i (Fin.cast hFs.symm j)) (fun i j => hlength i _) v S routeReady depth
  let tile : ArchiveTilePlan.Result g.length values :=
    ⟨(2^d)^c,hcapacity,(fun i j => padded i (Fin.cast hFs j)),
      (fun i j => hp i _),(by intro i j; simpa using hreal i (Fin.cast hFs j))⟩
  let M : Stacks T (prime+K) := {S with L := fun _ => [], R := (Function.update S.R route.src
    ((List.ofFn fun j => cstream (prime+K) W (List.ofFn fun i => padded i j).flatten).flatten))}
  have hsource : M.R route.src = (List.ofFn fun j => cstream (prime+K) W
      (List.ofFn fun i => tile.padded i j).flatten).flatten++[] := by
    simp only [M,Function.update_self,List.append_nil]
    congr 1
    exact List.ofFn_congr hFs.symm _
  have hpubReady : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W (tile.capacity-g.indices.length) borrowed M :=
    pubReady.of_frame (by intro r hr; exact Function.update_of_ne (pub.support_off hr).1 _ _)
  have hdstOff : dst ≠ route.src := pub.src_ne_dst.symm
  have hclockOff : clock ≠ route.src := by
    have := (List.nodup_append.mp hports).2.1
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false] at this
    tauto
  have hlineOff : lineRows ≠ route.src := by
    have := (List.nodup_append.mp hports).2.1
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false] at this
    tauto
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,hgood,hi,ho,hl,hframe⟩ := exactCoreTilePublication_exec
    (body := body) pub clock lineRows hports p W hW g hw Fs J values hrows tile ambient hambient
    [] outputTail borrowed v₁ M hpubReady hsource
    (by simpa only [M,Function.update_of_ne hdstOff] using hdst)
    (by simpa only [M,Function.update_of_ne hclockOff] using hclock)
    (by simpa only [M,Function.update_of_ne hlineOff] using hline) depth
  refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ he₁ he₂,hs,hd,hgood,hi,ho,?_,?_⟩
  · exact hl.trans (funext fun i => (routeReady.hL i).symm)
  · intro r hrs hrd
    exact (hframe r hrs hrd).trans (Function.update_of_ne hrs _ _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
