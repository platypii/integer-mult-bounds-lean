module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRibbonMask

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem gatherCouplingRibbons_exec {dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR : Fin T}
    (hreg : [dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    {s : ℕ} [NeZero s] (band N w : ℕ) (origins : List ℕ)
    (C : ZMod s → GaussianInt) (hne : origins ≠ []) (hordered : origins.Pairwise (· ≤ ·))
    (hfit : ∀ origin ∈ origins, origin+N ≤ s)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = (match origins.map (·*w) with
      | [] => [] | a::as => gatherControls A (a::windowAdvances a as)))
    (hs : S.R src = cstream A w (cyclicPaddedLine C band))
    (hrow : (S.R rowCount).length = N+2*band) (hw : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ origins.length*(14*(N+2*band)*w+25)+12*((s+2*band)*w)+
        6*(N+2*band)*w+9*(N+2*band)+29 ∧
      Exec body (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource rowCount wordR) (mk v S) n
        (mk v' {S with R := (Function.update S.R dst
          (origins.flatMap (fun origin => cstream A w (rawCouplingRibbon band origin N C))++S.R dst))}) := by
  have hordered' : (origins.map (·*w)).Pairwise (· ≤ ·) := by
    apply List.pairwise_map.mpr
    exact hordered.imp (fun h => Nat.mul_le_mul_right w h)
  have hfit' : ∀ a ∈ origins.map (·*w), a+(N+2*band)*w ≤ (cstream A w (cyclicPaddedLine C band)).length := by
    intro a ha
    obtain ⟨origin,ho,rfl⟩ := List.mem_map.mp ha
    have hh := hfit origin ho
    have hm := Nat.mul_le_mul_right w (show origin+(N+2*band) ≤ s+2*band by omega)
    simpa [length_cstream,cyclicPaddedLine,List.length_map,List.length_range,Nat.add_mul] using hm
  obtain ⟨v',n,hu,hn,he⟩ := orderedGather_exec (body := body) hreg (N+2*band) w
    (origins.map (·*w)) (cstream A w (cyclicPaddedLine C band)) (by simpa using hne)
    hordered' hfit' v S hc hs hrow hw hclean
  refine ⟨v',n,hu,?_,he.cast rfl ?_⟩
  · simpa [length_cstream,cyclicPaddedLine,List.length_map,List.length_range] using hn
  · apply congrArg (mk v')
    simp only [List.flatMap_map,cstream_drop,cstream_take,rawCouplingRibbon]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
