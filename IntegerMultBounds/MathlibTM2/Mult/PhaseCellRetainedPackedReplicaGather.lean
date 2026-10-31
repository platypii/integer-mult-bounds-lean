module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRowGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaGatherData

/-! Every packed RHS uses the same local sweep controls. Physical replica order
is explicit, and neither control decoding nor ambient movement repeats per RHS. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem retainedPackedReplicaGather_exec
    {replicas saved count source archive dst control savedControl advance window src acc current savedSource buf tmp
      initialControl initialSource rowCount wordR : Fin T}
    (hreg : [replicas,saved,source,archive,dst,count,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    {s : ℕ} (origin span L w : ℕ) (offsets : List ℕ) (Fs : List (ZMod s → GaussianInt))
    (hne : offsets ≠ []) (hspan : origin+span ≤ s) (hordered : offsets.Pairwise (· ≤ ·))
    (hfit : ∀ j ∈ offsets, j+L ≤ span)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = match offsets.map (·*w) with
      | [] => [] | p::ps => gatherControls A (p::windowAdvances p ps))
    (hs : S.R source = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++borrowed)
    (harchive : S.R archive = []) (hreplicas : (S.R replicas).length = Fs.length) (hsaved : S.R saved = [])
    (hcount : (S.R count).length = span*w) (hrow : (S.R rowCount).length = L) (hw : (S.R wordR).length = w)
    (hsrc : S.R src = [])
    (hclean : ∀ k ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ Fs.length*(retainedRowGatherStepCost (span*w) offsets.length L w+5)+4+2*(Fs.length*(span*w))+2 ∧
      Exec body (retainedRowGather replicas saved count source archive dst control savedControl advance window src acc current
        savedSource buf tmp initialControl initialSource rowCount wordR) (mk v S) n
        (mk v' {S with R := (Function.update S.R dst
          (Fs.reverse.flatMap (fun F => cstream A w (offsets.flatMap
            (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => F) 0)))++S.R dst))}) := by
  let row := fun F : ZMod s → GaussianInt => cstream A w (packedInterval origin span F)
  have hfitSymbols : ∀ p ∈ offsets.map (·*w), p+L*w ≤ span*w := by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right w (hfit j hj)
  have hpayload (F : ZMod s → GaussianInt) :
      (offsets.map (·*w)).flatMap (fun p => ((row F).drop p).take (L*w)) =
      cstream A w (offsets.flatMap (fun j =>
        cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => F) 0)) := by
    have hh := packedReplicaGatherRows_eq (A := A) w origin span 1 L offsets (fun _ => F) hspan hfit
    simpa only [packedReplicaSymbolOrigins,packedReplicaWords,List.range_one,List.flatMap_cons,
      List.flatMap_nil,List.map_cons,List.map_nil,List.nil_append,List.append_nil,Nat.zero_mul,Nat.zero_add,row] using hh
  obtain ⟨v',n,huser,hcost,he⟩ := retainedRowGather_exec (body := body) hreg (span*w) L w
    (offsets.map (·*w)) (Fs.map row) (by
      intro E hE
      obtain ⟨F,_,rfl⟩ := List.mem_map.mp hE
      simp [row,packedInterval_length _ hspan])
    (by simpa using hne) (List.pairwise_map.mpr (hordered.imp (fun h => Nat.mul_le_mul_right w h)))
    hfitSymbols borrowed v S hc (by simpa only [List.flatMap_def] using hs)
    harchive (by simpa only [List.length_map] using hreplicas) hsaved hcount hrow hw hsrc hclean
  refine ⟨v',n,huser,?_,?_⟩
  · simpa only [List.length_map] using hcost
  · rw [←List.map_reverse,List.flatMap_map] at he
    simpa only [hpayload] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
