module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageCyclicReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPackedBoundaryRhsFold
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Turn two cached packed residual rows into one real folded cyclic Schur RHS.
Only the two archive prefixes are consumed; all retained headers and masks survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 176 Q A U}

def foldCyclicReplicaBoundaryRhs : Pr P 176 Q A U :=
  .seq (stageCyclicReplicaBoundaryRhs 168 169 170 171 172 173 110 130 134 135 136 137 143 138 174 175)
    (embProg (Fin.castLE (by decide : 168 ≤ 176)) Empty.elim (realPackedBoundaryRhsFold (P := Empty)))

def foldCyclicReplicaBoundaryRhsCost (n N w : ℕ) :=
  stageReplicaBoundaryRhsCost n w+28+realPackedBoundaryRhsFoldCost N w

theorem foldCyclicReplicaBoundaryRhs_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (C D : ZMod s → GaussianInt) (w : ℕ)
    (leftTail rightTail : List (Fin (A+4))) (v : HS 176 Q A U) (S : Stacks 176 A)
    (hleftVolume : (S.R 168).length = min n (s-a)*w)
    (hrightVolume : (S.R 171).length = (n-min n (s-a))*w)
    (hleftArchive : S.R 169 = cstream A w (packedInterval a (min n (s-a)) C)++leftTail)
    (hrightArchive : S.R 172 = cstream A w (packedInterval 0 (n-min n (s-a)) D)++rightTail)
    (hleftMask : S.R 170 = couplingSourceIntervalMaskSymbols true A s t band
      a (a+min n (s-a)) a (min n (s-a)))
    (hrightMask : S.R 173 = couplingSourceIntervalMaskSymbols true A s t band
      0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hw : (S.R 130).length = w)
    (hcount : (S.R 116).length = (cyclicPrincipalBoundary s t band a n).card)
    (hfloor : (S.R 0).length = (cyclicPrincipalBoundary s t band a n).card/2)
    (hparity : (S.R 2).length = ((cyclicPrincipalBoundary s t band a n).card+1)/2-
      (cyclicPrincipalBoundary s t band a n).card/2)
    (hbytes : (S.R 3).length = (((cyclicPrincipalBoundary s t band a n).card+1)/2)*w)
    (hblank : ∀ r : Fin 176, 6 ≤ r.val → r.val < 80 → S.R r = [])
    (hfresh : ∀ r ∈ [(134 : Fin 176),135,136,137,143,174,175], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ foldCyclicReplicaBoundaryRhsCost n (cyclicPrincipalBoundary s t band a n).card w ∧
      Exec body foldCyclicReplicaBoundaryRhs (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 6
          (cstream A w ((bFoldOrder s (cyclicPrincipalBoundary s t band a n)).map
            (fun i => realPartWord (if i ∈ haloVertices s a (a+min n (s-a)) then C i else D i)))))}) := by
  let B := cyclicPrincipalBoundary s t band a n
  let F := fun i => if i ∈ haloVertices s a (a+min n (s-a)) then C i else D i
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := stageCyclicReplicaBoundaryRhs_exec (body := body)
    168 169 170 171 172 173 110 130 134 135 136 137 143 138 174 175 (by decide)
    hst hA band a n ha hn C D w leftTail rightTail v S hleftVolume hrightVolume
    hleftArchive hrightArchive hleftMask hrightMask hw (hfresh _ (by simp)) (hfresh _ (by simp))
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let J : Stacks 176 A := {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail)
    143 (cstream A w ((bOrder s B).map F)))}
  have he₁' : Exec body
      (stageCyclicReplicaBoundaryRhs 168 169 170 171 172 173 110 130 134 135 136 137 143 138 174 175)
      (mk v S) m₁ (mk v₁ J) := by
    simpa only [J,B,F,hfresh 143 (by simp),List.append_nil] using he₁
  let e : Fin 168 → Fin 176 := Fin.castLE (by decide)
  have hinj : Function.Injective e := Fin.castLE_injective (by decide)
  obtain ⟨vi,m₂,hui,hm₂,hei⟩ := realPackedBoundaryRhsFold_exec
    (body := fun z : Empty => nomatch z) s B F w hA (embDn e v₁) (embStk e J)
    (by simp [embStk,e,J]) (by simpa [embStk,e,J] using hw)
    (by simpa [embStk,e,J,B] using hcount)
    (by simpa [embStk,e,J,B] using hfloor)
    (by simpa [embStk,e,J,B] using hparity)
    (by simpa [embStk,e,J,B] using hbytes)
    (by intro r hr6 hr80
        have h143 : e r ≠ 143 := by intro h; have := congrArg Fin.val h; change r.val = 143 at this; omega
        have h169 : e r ≠ 169 := by intro h; have := congrArg Fin.val h; change r.val = 169 at this; omega
        have h172 : e r ≠ 172 := by intro h; have := congrArg Fin.val h; change r.val = 172 at this; omega
        simpa [embStk,J,h143,h169,h172] using hblank (e r) hr6 hr80)
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun z => nomatch z) hei v₁ rfl J rfl
  have hfinal : embOvr e
      ({embStk e J with R := (Function.update (Function.update (embStk e J).R 143 []) 6
        (cstream A w ((bFoldOrder s B).map (fun i => realPartWord (F i)))))}).get J =
      {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 6
        (cstream A w ((bFoldOrder s B).map (fun i => realPartWord (F i)))))} := by
    rw [embOvr_updateR_updateR hinj]
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk143 : k = 143 <;> by_cases hk6 : k = 6 <;>
      simp [J,e,hk143,hk6,Function.update_apply,hfresh 143 (by simp)]
  refine ⟨v₂,m₁+m₂,hu₂.trans (hui.trans hu₁),?_,
    (Exec.seq he₁' he₂).cast rfl (congrArg (mk v₂) hfinal)⟩
  have hsplit : min n (s-a)+(n-min n (s-a)) = n := Nat.add_sub_of_le (Nat.min_le_left n (s-a))
  unfold foldCyclicReplicaBoundaryRhsCost realPackedBoundaryRhsFoldCost stageReplicaBoundaryRhsCost at *
  nlinarith only [hm₁,hm₂,congrArg (fun k => k*w) hsplit,congrArg (fun k => k*(16*w+10)) hsplit]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
