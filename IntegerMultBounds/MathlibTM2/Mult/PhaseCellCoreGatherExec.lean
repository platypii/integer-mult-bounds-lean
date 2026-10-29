module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrderedGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.NLogN.PhaseCellCoreGather

/-! # One restoring sweep for a generated halo group

The executed source traversal is charged once per length group, rather than
once per halo. Delimited controls are explicit here; their generation and the
connection of packed outputs to S3 remain caller obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- The executed gather's output consists exactly of packed ambient halos. -/
theorem coreGather_packed {s : ℕ} (width radius L wordWidth : ℕ)
    (F : ZMod s → GaussianInt) :
    (coreGatherOrigins s width radius L wordWidth).flatMap
      (fun a => ((cstream A wordWidth (chirpLine s F)).drop a).take (L*wordWidth)) =
    (coreGatherIndices s width radius L).flatMap (fun k =>
      cstream A wordWidth (packedInterval (coreStart width k-radius) L F)) := by
  simp only [coreGatherOrigins,List.flatMap_map,packedInterval_symbols]

theorem coreGather_exec {dst control savedControl advance window src acc current savedSource buf tmp
    initialControl initialSource rowCount wordR : Fin T}
    (hreg : [dst,control,savedControl,advance,window,src,acc,current,savedSource,buf,tmp,
      initialControl,initialSource,rowCount,wordR].Nodup)
    (s width radius L wordWidth : ℕ) (E : List (Fin (A+4)))
    (hlen : E.length = s*wordWidth)
    (hne : coreGatherOrigins s width radius L wordWidth ≠ [])
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = (match coreGatherOrigins s width radius L wordWidth with
      | [] => [] | a::as => gatherControls A (a::windowAdvances a as)))
    (hs : S.R src = E) (hrow : (S.R rowCount).length = L)
    (hw : (S.R wordR).length = wordWidth)
    (hclean : ∀ k ∈ [savedControl,advance,window,acc,current,savedSource,buf,tmp,
      initialControl,initialSource], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (coreGatherIndices s width radius L).length*(14*L*wordWidth+25)+
        12*s*wordWidth+6*L*wordWidth+9*L+29 ∧
      Exec body (naturalGather dst control savedControl advance window src acc current savedSource buf tmp
        initialControl initialSource rowCount wordR) (mk v S) n
        (mk v' {S with R := (Function.update S.R dst
          ((coreGatherOrigins s width radius L wordWidth).flatMap
            (fun a => (E.drop a).take (L*wordWidth))++S.R dst))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := orderedGather_exec (body := body) hreg L wordWidth
    (coreGatherOrigins s width radius L wordWidth) E hne
    (coreGatherOrigins_ordered s width radius L wordWidth)
    (by rw [hlen]; exact coreGatherOrigins_fit s width radius L wordWidth)
    v S hc hs hrow hw hclean
  refine ⟨v',n,hu,?_,he⟩
  simpa only [coreGatherOrigins,List.length_map,hlen,Nat.mul_assoc] using hn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
