module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPackedBoundaryPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundaryStreams

/-! Consume one natural-order boundary row at the native batch inverse-fold
endpoint. The retained factor bank and solved-row archive remain in place. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def nativeCyclicBoundaryPieces : Pr P 240 Q A U :=
  .seq (placedPackedBoundaryPublish 237 238 160 234 235 236 132)
    (placedPackedBoundaryPublish 237 239 160 234 235 236 132)

theorem nativeCyclicBoundaryPieces_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (solution : List GaussianInt) (w : ℕ) :
    let G := boundarySolutionField (cyclicPrincipalBoundary s t band a n) solution
    ∀ (tail : List (Fin (A+4))) (v : HS 240 Q A U) (S : Stacks 240 A),
    S.R 237 = cstream A w ((bOrder s (cyclicPrincipalBoundary s t band a n)).map G)++tail →
    S.R 238 = couplingSourceIntervalMaskSymbols true A s t band 0 (n-min n (s-a)) 0 (n-min n (s-a)) →
    S.R 239 = couplingSourceIntervalMaskSymbols true A s t band a (a+min n (s-a)) a (min n (s-a)) →
    (S.R 160).length = w →
    (∀ k ∈ ([234,235,236] : List (Fin 240)), S.R k = []) →
    ∃ vf m, vf.user = v.user ∧ m ≤ n*(6*w+10)+12 ∧
      Exec body nativeCyclicBoundaryPieces (mk v S) m
        (mk vf {S with R := (Function.update (Function.update S.R 237 tail) 132
          (cstream A w (packedInterval a (min n (s-a)) G)++
            (cstream A w (packedInterval 0 (n-min n (s-a)) G)++S.R 132)))}) := by
  dsimp only
  let G := boundarySolutionField (cyclicPrincipalBoundary s t band a n) solution
  intro tail v S hsrc hmaskR hmaskL hw hfresh
  have hzero := cyclicBoundaryField_piece_zero t band a n ha hn solution
  have hsource : S.R 237 =
      cstream A w ((bOrder s (haloBoundary s t band 0 (n-min n (s-a)))).map G)++
        (cstream A w ((bOrder s (haloBoundary s t band a (a+min n (s-a)))).map G)++tail) := by
    rw [hsrc,cyclicBoundaryStream_split A w t band a n ha hn G,List.append_assoc]
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := placedPackedBoundaryPublish_exec (body := body) (origin := 0) (N := n-min n (s-a))
    237 238 160 234 235 236 132 (by decide) hst hA band 0 (n-min n (s-a))
    (by omega) (by omega)
    (by intro i hi; simpa only [Nat.zero_add] using (mem_haloVertices _ _ i).mp (Finset.mem_sdiff.mp hi).1)
    G (by intro i _ hi hoff; exact hzero.2 i (by simpa only [Nat.zero_add] using hi) hoff)
    w (cstream A w ((bOrder s (haloBoundary s t band a (a+min n (s-a)))).map G)++tail)
    v S hsource hmaskR hw hfresh
  let S₁ : Stacks 240 A := {S with R := (Function.update (Function.update S.R 237
    (cstream A w ((bOrder s (haloBoundary s t band a (a+min n (s-a)))).map G)++tail)) 132
    (cstream A w (packedInterval 0 (n-min n (s-a)) G)++S.R 132))}
  obtain ⟨vf,m₂,hu₂,hm₂,he₂⟩ := placedPackedBoundaryPublish_exec (body := body) (origin := a) (N := min n (s-a))
    237 239 160 234 235 236 132 (by decide) hst hA band a (a+min n (s-a))
    (by omega) (by omega)
    (by intro i hi; exact (mem_haloVertices _ _ i).mp (Finset.mem_sdiff.mp hi).1)
    G (by intro i hi _ hoff; exact hzero.1 i hi hoff) w tail v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hmaskL) (by simpa [S₁] using hw)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  have hfinal : {S₁ with R := (Function.update (Function.update S₁.R 237 tail) 132
      (cstream A w (packedInterval a (min n (s-a)) G)++S₁.R 132))} =
      {S with R := (Function.update (Function.update S.R 237 tail) 132
        (cstream A w (packedInterval a (min n (s-a)) G)++
          (cstream A w (packedInterval 0 (n-min n (s-a)) G)++S.R 132)))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk237 : k = 237 <;> by_cases hk132 : k = 132 <;> simp [S₁,hk237,hk132]
  refine ⟨vf,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ (he₂.cast rfl (congrArg (mk vf) hfinal))⟩
  have hsplit := Nat.sub_add_cancel (Nat.min_le_left n (s-a))
  have hcost : (n-min n (s-a))*(6*w+10)+6+(min n (s-a)*(6*w+10)+6) = n*(6*w+10)+12 := by
    nlinarith only [congrArg (fun k => k*(6*w+10)) hsplit]
  exact (Nat.add_le_add hm₁ hm₂).trans (le_of_eq hcost)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
