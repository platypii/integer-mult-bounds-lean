module

public import IntegerMultBounds.MathlibTM2.Host.SpreadRecords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryMask

/-! Address-generic masked boundary publication. Only the seven participating
tapes must be distinct; the surrounding factor bank needs no reindexing. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def placedPackedBoundaryPublish (src mask width saved word zero dst : Fin T) : Pr P T Q A U :=
  spreadRecords src mask width saved word zero dst pairRe (pairSym A false false)

theorem placedPackedBoundaryPublish_exec {s t origin N : ℕ} [NeZero s]
    (src mask width saved word zero dst : Fin T)
    (hregs : ([src,mask,width,saved,word,zero,dst] : List (Fin T)).Nodup)
    (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ) (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (G : ZMod s → GaussianInt) (hoff : ∀ i, origin ≤ i.val → i.val < origin+N → i ∉ haloBoundary s t band a b → G i = 0)
    (w : ℕ) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w ((bOrder s (haloBoundary s t band a b)).map G)++tail)
    (hmask : S.R mask = couplingSourceIntervalMaskSymbols true A s t band a b origin N)
    (hw : (S.R width).length = w)
    (hfresh : ∀ k ∈ ([saved,word,zero] : List (Fin T)), S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ N*(6*w+10)+6 ∧
      Exec body (placedPackedBoundaryPublish src mask width saved word zero dst) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst
          (cstream A w (packedInterval origin N G)++S.R dst))}) := by
  let B := haloBoundary s t band a b
  let ms := couplingSourceIntervalMaskSymbols true A s t band a b origin N
  let words := (packedInterval origin N G).map (csyms A w)
  have hflags : ms.map pairRe = packedBoundaryRhsFlags origin N B :=
    packedBoundaryRhsMask_flags hst hA band a b hb hfit
  have hlenMs : ms.length = N := couplingSourceIntervalMaskSymbols_length _ _ _ _ _ _ _ _ _
  have hlen : words.length = ms.length := by simp [words,hlenMs,packedInterval_length G hfit]
  have hwidth : ∀ x ∈ words, x.length = w := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    simp
  have hzero : ∀ j (hj : j < ms.length), pairRe ms[j] = false →
      words[j]'(by omega) = List.replicate w (pairSym A false false) := by
    intro j hj hf
    have hjN : j < N := by omega
    have hjflags : j < (packedBoundaryRhsFlags origin N B).length := by
      rw [packedBoundaryRhsFlags_length B hfit]; exact hjN
    have hflag : (packedBoundaryRhsFlags origin N B)[j] = false := by
      have hh := congrArg (fun xs : List Bool => xs.getD j false) hflags
      rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map,
        List.getD_eq_getElem _ _ hjflags] at hh
      exact hh.symm.trans hf
    have hn : ((origin+j : ℕ) : ZMod s) ∉ B := by
      simpa [packedBoundaryRhsFlags,physOrder] using hflag
    have hval : ((origin+j : ℕ) : ZMod s).val = origin+j := ZMod.val_natCast_of_lt (by omega)
    have hz := hoff ((origin+j : ℕ) : ZMod s) (by rw [hval]; omega) (by rw [hval]; omega) hn
    simp only [words,List.getElem_map,packedInterval_get G hfit hjN,hz,ShortConv.csyms_zero]
  have hsem : (gatherSymbols words (ms.map pairRe)).flatten =
      cstream A w ((bOrder s B).map G) := by
    rw [hflags]
    change (gatherSymbols ((packedInterval origin N G).map (csyms A w))
      (packedBoundaryRhsFlags origin N B)).flatten = _
    rw [gatherSymbols_map,packedBoundaryRhs_select_ordered B G hB]
    rfl
  obtain ⟨v',n,hu,hn,he⟩ := spreadRecords_exec src mask width saved word zero dst hregs
    ms words w pairRe (pairSym A false false) hlen hwidth hzero tail v S
    (by simpa only [hsem] using hsrc) hmask hw hfresh
  exact ⟨v',n,hu,by simpa only [hlenMs] using hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
