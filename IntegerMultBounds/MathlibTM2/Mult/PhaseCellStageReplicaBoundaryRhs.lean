module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix

/-! Consume one physical residual-archive row and select its boundary RHS.
The common mask and staging bank are restored, ready for the next replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def stageReplicaBoundaryRhs (volume archive src mask width symbols ts tm acc out cs saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix volume archive src saved tmp)
    (.seq (gatherRecords src mask width symbols ts tm acc out cs pairRe)
      (discardPrefix volume src saved tmp))

def stageReplicaBoundaryRhsCost (N w : ℕ) := 12*(N*w)+12+(N*(16*w+10)+16)

theorem stageReplicaBoundaryRhs_exec (volume archive src mask width symbols ts tm acc out cs saved tmp : Fin T)
    (hreg : [volume,archive,src,mask,width,symbols,ts,tm,acc,out,saved,tmp].Nodup)
    {s t origin N : ℕ} [NeZero s] (hst : s < t) (hA : 4 ≤ A) (band a b : ℕ)
    (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (D : ZMod s → GaussianInt) (w : ℕ) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hvolume : (S.R volume).length = N*w)
    (harchive : S.R archive = cstream A w (packedInterval origin N D)++tail)
    (hmask : S.R mask = couplingSourceIntervalMaskSymbols true A s t band a b origin N)
    (hw : (S.R width).length = w) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hfresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ stageReplicaBoundaryRhsCost N w ∧
      Exec body (stageReplicaBoundaryRhs volume archive src mask width symbols ts tm acc out cs saved tmp)
        (mk v S) m (mk v' {S with R := (Function.update (Function.update S.R archive tail) out
          (cstream A w ((bOrder s (haloBoundary s t band a b)).map D)++S.R out))}) := by
  have hr := hreg
  regs_ne hr
  let words := cstream A w (packedInterval origin N D)
  have hlen : words.length = N*w := by
    simp [words,packedInterval]
    omega
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body) (count := volume) (src := archive) (dst := src)
    (buf := saved) (tmp := tmp) (by regs_nodup) v S words tail harchive (by rw [hvolume,hlen]) hsaved htmp
  let J : Stacks T A := {S with R := (Function.update (Function.update S.R archive tail) src (words++S.R src))}
  have hframe (k : Fin T) (ha : k ≠ archive) (hs : k ≠ src) : J.R k = S.R k := by
    simp [J,ha,hs]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packedBoundaryRhsHaloGather_exec (body := body)
    (src := src) (mask := mask) (width := width) (symbols := symbols) (ts := ts) (tm := tm)
    (acc := acc) (out := out) (cs := cs) (by regs_nodup) hst hA band a b hb hfit hB D w (S.R src) v₁ J
    (by simp [J,words]) (by rw [hframe mask (Ne.symm ‹archive ≠ mask›) (Ne.symm ‹src ≠ mask›)]; exact hmask)
    (by rw [hframe width (Ne.symm ‹archive ≠ width›) (Ne.symm ‹src ≠ width›)]; exact hw) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      all_goals rw [hframe _ (Ne.symm (by assumption)) (Ne.symm (by assumption))]; exact hfresh _ (by simp))
  let K : Stacks T A := {J with R := (Function.update J.R out
    (cstream A w ((bOrder s (haloBoundary s t band a b)).map D)++J.R out))}
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body) (count := volume) (src := src)
    (trash := saved) (tmp := tmp) (by regs_nodup) words (S.R src) v₂ K
    (by simp [K,J,‹src ≠ out›])
    (by simpa [K,‹volume ≠ out›,hframe volume ‹volume ≠ archive› ‹volume ≠ src›,hlen] using hvolume)
    (by simpa [K,(Ne.symm ‹out ≠ saved›),hframe saved (Ne.symm ‹archive ≠ saved›) (Ne.symm ‹src ≠ saved›)] using hsaved)
    (by simpa [K,(Ne.symm ‹out ≠ tmp›),hframe tmp (Ne.symm ‹archive ≠ tmp›) (Ne.symm ‹src ≠ tmp›)] using htmp)
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · unfold stageReplicaBoundaryRhsCost
    rw [hlen]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = src
    · subst k; simp [K,J,‹src ≠ out›,(Ne.symm ‹archive ≠ src›)]
    · simp [K,J,Function.update_apply,hk,(Ne.symm ‹src ≠ out›),(Ne.symm ‹archive ≠ out›)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
