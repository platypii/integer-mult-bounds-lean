module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFoldReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealBoundaryRhsTransfer

/-! One archive row reaches the solver's real folded RHS format in one trace.
The boundary mask, counters and borrowed banks are shared across replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareReplicaBoundaryRhs (bank : Fin 168 → Fin T)
    (volume archive rhsVolume dst symbols ts tm acc cs saved tmp : Fin T) : Pr P T Q A U :=
  .seq (foldReplicaBoundaryRhs bank volume archive symbols ts tm acc cs saved tmp)
    (realBoundaryRhsTransfer rhsVolume (bank 6) dst saved tmp)

theorem prepareReplicaBoundaryRhs_exec (bank : Fin 168 → Fin T) (hinj : Function.Injective bank)
    (volume archive rhsVolume dst symbols ts tm acc cs saved tmp : Fin T)
    (hroute : [rhsVolume,bank 6,dst,saved,tmp].Nodup)
    (hrhsOff : rhsVolume ≠ archive) (hdstOff : dst ≠ archive)
    (hoff : ∀ i, bank i ≠ archive)
    (hreg : [volume,archive,bank 110,bank 167,bank 130,symbols,ts,tm,acc,bank 143,saved,tmp].Nodup)
    {s t origin N : ℕ} [NeZero s] (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ)
    (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (D : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hrhsVolume : (S.R rhsVolume).length = (haloBoundary s t band a b).card*w)
    (hvolume : (S.R volume).length = N*w)
    (harchive : S.R archive = cstream A w (packedInterval origin N D)++tail)
    (hmask : S.R (bank 167) = couplingSourceIntervalMaskSymbols true A s t band a b origin N)
    (hw : (S.R (bank 130)).length = w) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hfresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = [])
    (h143 : S.R (bank 143) = [])
    (hcount : (S.R (bank 116)).length = (haloBoundary s t band a b).card)
    (hfloor : (S.R (bank 0)).length = (haloBoundary s t band a b).card/2)
    (hparity : (S.R (bank 2)).length = ((haloBoundary s t band a b).card+1)/2-(haloBoundary s t band a b).card/2)
    (hbytes : (S.R (bank 3)).length = ((haloBoundary s t band a b).card+1)/2*w)
    (hblank : ∀ i : Fin 168, 6 ≤ i.val → i.val < 77 → S.R (bank i) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ stageReplicaBoundaryRhsCost N w+60*((haloBoundary s t band a b).card+1)*w+60*(haloBoundary s t band a b).card+60+6*((haloBoundary s t band a b).card*w)+6 ∧
      Exec body (prepareReplicaBoundaryRhs bank volume archive rhsVolume dst symbols ts tm acc cs saved tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R archive tail) dst
          (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map (fun i => realPartWord (D i)))++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  have hr' := hroute
  regs_ne hr'
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := foldReplicaBoundaryRhs_exec (body := body) bank hinj
    volume archive symbols ts tm acc cs saved tmp hoff hreg hst hA band a b hb hfit hB D w tail v S
    hvolume harchive hmask hw hsaved htmp hfresh h143 hcount hfloor hparity hbytes hblank
  let xs := (bFoldOrder s (haloBoundary s t band a b)).map D
  let J : Stacks T A := {S with R := (Function.update (Function.update S.R archive tail) (bank 6) (cstream A w xs))}
  have hframe (k : Fin T) (ha : k ≠ archive) (h6 : k ≠ bank 6) : J.R k = S.R k := by
    simp [J,ha,h6]
  obtain ⟨v₂,hu₂,he₂⟩ := realBoundaryRhsTransfer_exec (body := body)
    rhsVolume (bank 6) dst saved tmp hroute hA w xs [] v₁ J
    (by rw [hframe rhsVolume hrhsOff ‹rhsVolume ≠ bank 6›]; simpa [xs,bFoldOrder_length] using hrhsVolume)
    (by simp [J])
    (by rw [hframe saved (Ne.symm ‹archive ≠ saved›) (Ne.symm ‹bank 6 ≠ saved›)]; exact hsaved)
    (by rw [hframe tmp (Ne.symm ‹archive ≠ tmp›) (Ne.symm ‹bank 6 ≠ tmp›)]; exact htmp)
  refine ⟨v₂,_,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · have hlen : xs.length = (haloBoundary s t band a b).card := by simp [xs,bFoldOrder_length]
    rw [hlen]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have h6 := hblank 6 (by decide) (by decide)
    have hd6 : dst ≠ bank 6 := Ne.symm ‹bank 6 ≠ dst›
    by_cases hk : k = bank 6
    · subst k
      simp [J,‹bank 6 ≠ dst›,hoff 6,h6]
    · simp [J,Function.update_apply,hk,hd6,hdstOff,xs,List.map_map,Function.comp_def]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
