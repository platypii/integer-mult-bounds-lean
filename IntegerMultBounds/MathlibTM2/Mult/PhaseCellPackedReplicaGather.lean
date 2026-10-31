module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaGatherData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedGather

/-! One restoring sweep gathers every cell from already exposed packed replicas.
The movement charge depends on packed volume, not ambient period. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem packedReplicaGather_exec {dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR : Fin T}
    (hreg : [dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    {s : ℕ} (N origin span L w : ℕ) (offsets : List ℕ) (C : ℕ → ZMod s → GaussianInt)
    (hN : 0 < N) (hne : offsets ≠ []) (hspan : origin+span ≤ s)
    (hordered : offsets.Pairwise (· ≤ ·)) (hfit : ∀ j ∈ offsets, j+L ≤ span)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = match packedReplicaSymbolOrigins N span w offsets with
      | [] => [] | p::ps => gatherControls A (p::windowAdvances p ps))
    (hs : S.R src = cstream A w (packedReplicaWords origin span N C))
    (hrow : (S.R rowCount).length = L) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (N*offsets.length)*(14*L*w+25)+12*(N*span*w)+6*L*w+9*L+29 ∧
      Exec body (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource rowCount wordR) (mk v S) n
        (mk v' {S with R := (Function.update S.R dst
          (cstream A w ((List.range N).flatMap (fun r => offsets.flatMap
            (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) C r)))++S.R dst))}) := by
  have hlength : (cstream A w (packedReplicaWords origin span N C)).length = N*span*w := by
    simp [packedReplicaWords_length origin span N C hspan]
  have hnonempty : packedReplicaSymbolOrigins N span w offsets ≠ [] := by
    have ho : 0 < offsets.length := List.length_pos_iff.mpr hne
    have hh : 0 < (packedReplicaSymbolOrigins N span w offsets).length := by
      simpa only [packedReplicaSymbolOrigins_length] using Nat.mul_pos hN ho
    exact List.ne_nil_of_length_pos hh
  obtain ⟨v',n,huser,hcost,he⟩ := orderedGather_exec (body := body) hreg L w
    (packedReplicaSymbolOrigins N span w offsets) (cstream A w (packedReplicaWords origin span N C))
    hnonempty (packedReplicaSymbolOrigins_ordered N span L w offsets hordered hfit)
    (by simpa only [hlength] using packedReplicaSymbolOrigins_fit N span L w offsets hfit)
    v S hc hs hrow hw hclean
  refine ⟨v',n,huser,?_,?_⟩
  · simpa only [packedReplicaSymbolOrigins_length,hlength] using hcost
  · simpa only [packedReplicaGatherRows_eq w origin span N L offsets C hspan hfit] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
