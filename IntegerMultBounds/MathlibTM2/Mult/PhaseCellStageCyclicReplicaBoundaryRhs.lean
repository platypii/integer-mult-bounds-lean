module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageReplicaBoundaryRhs
public import IntegerMultBounds.NLogN.PhaseCellCyclicBoundaryOrder

/-! Consume one row of each packed residual archive using the retained masks.
Left staging followed by right staging produces the joint natural boundary order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def stageCyclicReplicaBoundaryRhs
    (leftVolume leftArchive leftMask rightVolume rightArchive rightMask
      src width symbols ts tm acc out cs saved tmp : Fin T) : Pr P T Q A U :=
  .seq (stageReplicaBoundaryRhs leftVolume leftArchive src leftMask width symbols ts tm acc out cs saved tmp)
    (stageReplicaBoundaryRhs rightVolume rightArchive src rightMask width symbols ts tm acc out cs saved tmp)

theorem stageCyclicReplicaBoundaryRhs_exec
    (leftVolume leftArchive leftMask rightVolume rightArchive rightMask
      src width symbols ts tm acc out cs saved tmp : Fin T)
    (hreg : [leftVolume,leftArchive,leftMask,rightVolume,rightArchive,rightMask,
      src,width,symbols,ts,tm,acc,out,saved,tmp].Nodup)
    {s t : ℕ} [NeZero s] (hst : s < t) (hA : 4 ≤ A)
    (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (C D : ZMod s → GaussianInt) (w : ℕ)
    (leftTail rightTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hleftVolume : (S.R leftVolume).length = min n (s-a)*w)
    (hrightVolume : (S.R rightVolume).length = (n-min n (s-a))*w)
    (hleftArchive : S.R leftArchive = cstream A w (packedInterval a (min n (s-a)) C)++leftTail)
    (hrightArchive : S.R rightArchive = cstream A w (packedInterval 0 (n-min n (s-a)) D)++rightTail)
    (hleftMask : S.R leftMask = couplingSourceIntervalMaskSymbols true A s t band
      a (a+min n (s-a)) a (min n (s-a)))
    (hrightMask : S.R rightMask = couplingSourceIntervalMaskSymbols true A s t band
      0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hw : (S.R width).length = w) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hfresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ stageReplicaBoundaryRhsCost (min n (s-a)) w+
        stageReplicaBoundaryRhsCost (n-min n (s-a)) w ∧
      Exec body (stageCyclicReplicaBoundaryRhs leftVolume leftArchive leftMask
        rightVolume rightArchive rightMask src width symbols ts tm acc out cs saved tmp)
        (mk v S) m (mk v' {S with R := (Function.update
          (Function.update (Function.update S.R leftArchive leftTail) rightArchive rightTail) out
          (cstream A w ((bOrder s (cyclicPrincipalBoundary s t band a n)).map
            (fun i => if i ∈ haloVertices s a (a+min n (s-a)) then C i else D i))++S.R out))}) := by
  have hr := hreg
  regs_ne hr
  have hleftFit : a+min n (s-a) ≤ s := by omega
  have hrightFit : 0+(n-min n (s-a)) ≤ s := by omega
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := stageReplicaBoundaryRhs_exec (body := body)
    leftVolume leftArchive src leftMask width symbols ts tm acc out cs saved tmp
    (by regs_nodup) hst hA band a (a+min n (s-a)) hleftFit hleftFit
    (by intro i hi; exact (mem_haloVertices _ _ i).mp (Finset.mem_sdiff.mp hi).1)
    C w leftTail v S hleftVolume hleftArchive hleftMask hw hsaved htmp hfresh
  let leftRows := (bOrder s (haloBoundary s t band a (a+min n (s-a)))).map C
  let J : Stacks T A := {S with R := (Function.update (Function.update S.R leftArchive leftTail) out
    (cstream A w leftRows++S.R out))}
  have hframe (k : Fin T) (ha : k ≠ leftArchive) (ho : k ≠ out) : J.R k = S.R k := by
    simp only [J,Function.update_of_ne ho,Function.update_of_ne ha]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := stageReplicaBoundaryRhs_exec (body := body)
    rightVolume rightArchive src rightMask width symbols ts tm acc out cs saved tmp
    (by regs_nodup) hst hA band 0 (n-min n (s-a)) (by omega) hrightFit
    (by intro i hi; simpa only [Nat.zero_add] using
      (mem_haloVertices _ _ i).mp (Finset.mem_sdiff.mp hi).1)
    D w rightTail v₁ J
    (by rw [hframe rightVolume (Ne.symm ‹leftArchive ≠ rightVolume›) ‹rightVolume ≠ out›]; exact hrightVolume)
    (by rw [hframe rightArchive (Ne.symm ‹leftArchive ≠ rightArchive›) ‹rightArchive ≠ out›]; exact hrightArchive)
    (by rw [hframe rightMask (Ne.symm ‹leftArchive ≠ rightMask›) ‹rightMask ≠ out›]; exact hrightMask)
    (by rw [hframe width (Ne.symm ‹leftArchive ≠ width›) ‹width ≠ out›]; exact hw)
    (by rw [hframe saved (Ne.symm ‹leftArchive ≠ saved›) (Ne.symm ‹out ≠ saved›)]; exact hsaved)
    (by rw [hframe tmp (Ne.symm ‹leftArchive ≠ tmp›) (Ne.symm ‹out ≠ tmp›)]; exact htmp)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with hk | hk | hk | hk <;> subst k
        all_goals rw [hframe _ (Ne.symm (by assumption)) (by assumption)]; exact hfresh _ (by simp))
  have hrows :
      (bOrder s (cyclicPrincipalBoundary s t band a n)).map
          (fun i => if i ∈ haloVertices s a (a+min n (s-a)) then C i else D i) =
        (bOrder s (haloBoundary s t band 0 (n-min n (s-a)))).map D++leftRows := by
    rw [cyclicPrincipalBoundary_order t band a n ha hn,List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      have hiB : i ∈ haloBoundary s t band 0 (n-min n (s-a)) := by
        rw [← List.mem_toFinset,bOrder_toFinset] at hi
        exact hi
      exact ite_eq_right (fun h => Finset.disjoint_left.mp (cyclicPrincipalPieces_disjoint a n ha hn)
        h (Finset.mem_sdiff.mp hiB).1)
    · apply List.map_congr_left
      intro i hi
      have hiB : i ∈ haloBoundary s t band a (a+min n (s-a)) := by
        rw [← List.mem_toFinset,bOrder_toFinset] at hi
        exact hi
      exact ite_eq_left (Finset.mem_sdiff.mp hiB).1
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k = out
  · subst k
    simp [J,hrows,cstream_append,List.append_assoc]
  · by_cases hr : k = rightArchive
    · subst k; simp [J,hk]
    · simp [J,hk,hr]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
