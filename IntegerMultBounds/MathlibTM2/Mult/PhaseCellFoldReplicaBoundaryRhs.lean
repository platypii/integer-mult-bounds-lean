module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRhsFold
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Physical archive extraction followed by the existing boundary permutation.
The staging bank is restored; only the archive and folded RHS change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def foldReplicaBoundaryRhs (bank : Fin 168 → Fin T)
    (volume archive symbols ts tm acc cs saved tmp : Fin T) : Pr P T Q A U :=
  .seq (stageReplicaBoundaryRhs volume archive (bank 110) (bank 167) (bank 130)
    symbols ts tm acc (bank 143) cs saved tmp)
    (embProg bank Empty.elim (packedBoundaryRhsFold (P := Empty)))

theorem foldReplicaBoundaryRhs_exec (bank : Fin 168 → Fin T) (hinj : Function.Injective bank)
    (volume archive symbols ts tm acc cs saved tmp : Fin T)
    (hoff : ∀ i, bank i ≠ archive)
    (hreg : [volume,archive,bank 110,bank 167,bank 130,symbols,ts,tm,acc,bank 143,saved,tmp].Nodup)
    {s t origin N : ℕ} [NeZero s] (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ)
    (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (D : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
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
      m ≤ stageReplicaBoundaryRhsCost N w+60*((haloBoundary s t band a b).card+1)*w+60*(haloBoundary s t band a b).card+60 ∧
      Exec body (foldReplicaBoundaryRhs bank volume archive symbols ts tm acc cs saved tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R archive tail) (bank 6)
          (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map D)))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := stageReplicaBoundaryRhs_exec (body := body)
    volume archive (bank 110) (bank 167) (bank 130) symbols ts tm acc (bank 143) cs saved tmp hreg
    hst hA band a b hb hfit hB D w tail v S hvolume harchive hmask hw hsaved htmp hfresh
  let J : Stacks T A := {S with R := (Function.update (Function.update S.R archive tail) (bank 143)
    (cstream A w ((bOrder s (haloBoundary s t band a b)).map D)++S.R (bank 143)))}
  have hne (i : Fin 168) (hi : i ≠ 143) : bank i ≠ bank 143 := fun h => hi (hinj h)
  have hframe (i : Fin 168) (hi : i ≠ 143) : J.R (bank i) = S.R (bank i) := by
    simp [J,hne i hi,hoff i]
  obtain ⟨vi,m₂,hui,hm₂,hei⟩ := packedBoundaryRhsFold_exec (body := fun z : Empty => nomatch z)
    s (haloBoundary s t band a b) D w (embDn bank v₁) (embStk bank J)
    (by change J.R (bank 143) = _; simp [J,h143]) (by change (J.R (bank 130)).length = w; rw [hframe 130 (by decide)]; exact hw)
    (by change (J.R (bank 116)).length = _; rw [hframe 116 (by decide)]; exact hcount)
    (by change (J.R (bank 0)).length = _; rw [hframe 0 (by decide)]; exact hfloor)
    (by change (J.R (bank 2)).length = _; rw [hframe 2 (by decide)]; exact hparity)
    (by change (J.R (bank 3)).length = _; rw [hframe 3 (by decide)]; exact hbytes) (by
      intro i hi6 hi77
      change J.R (bank i) = []
      rw [hframe i (by intro h; subst i; norm_num at hi77)]
      exact hblank i hi6 hi77)
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun z => nomatch z) hei v₁ rfl J rfl
  have hresult : embOvr bank
      ({embStk bank J with R := (Function.update (Function.update (embStk bank J).R 143 []) 6
        (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map D)))}).get J =
      {S with R := (Function.update (Function.update S.R archive tail) (bank 6)
        (cstream A w ((bFoldOrder s (haloBoundary s t band a b)).map D)))} := by
    rw [embOvr_updateR_updateR hinj]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have h6143 := hne 6 (by decide)
    by_cases hk : k = bank 143
    · subst k
      simp [J,h6143.symm,hoff 143,h143]
    · simp [J,Function.update_apply,hk]
  exact ⟨v₂,m₁+m₂,hu₂.trans (hui.trans hu₁),by omega,
    (Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) hresult)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
