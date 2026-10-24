module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingProductionSetup
public import IntegerMultBounds.MathlibTM2.Routing.MatchingPrefixCountFromWidth

/-! The actual full-table profile compiler borrows a count generated from compact
binary dimensions. Its readiness frame contains no supplied count word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def MatchingProductionFrame.with_count {p : Par} {mate : Fin p.wy → Fin p.wy}
    {Li Lk Lc : ℕ} {dst : Fin T} {S : Stacks T A}
    (frame : MatchingProductionFrame p mate Li Lk Lc dst S)
    (hg : ∀ j, frame.extract 0 ≠ frame.gather j)
    (hp : ∀ j, frame.extract 0 ≠ frame.generate j)
    (hf : (p.n * p.K) * (2 * (Li + Lk) + 2) < 2 ^ Lc) :
    MatchingProductionSetup p mate Li Lk Lc dst
      { S with R := (Function.update S.R (frame.extract 0)
        (binSyms Lc ((p.n * p.K) * (2 * (Li + Lk) + 2)))) } := by
  have keep (x : Fin T) (hx : x ≠ frame.extract 0) :
      Function.update S.R (frame.extract 0) (binSyms Lc ((p.n * p.K) * (2 * (Li + Lk) + 2))) x = S.R x :=
    Function.update_of_ne hx _ _
  refine {
    extract := frame.extract, hprefix := frame.hprefix
    gather := frame.gather, hgather := frame.hgather
    generate := frame.generate, hgenerate := frame.hgenerate
    hseparate := frame.hseparate, hdst := frame.hdst, hjoin := frame.hjoin
    hgenerateSource := frame.hgenerateSource, hdstBulk := frame.hdstBulk
    hK := frame.hK, hρ := frame.hρ, hinv := frame.hinv, reverse := frame.reverse
    hwidth := frame.hwidth, hk := frame.hk, hcountFit := hf
    hinput := (keep _ (frame.hprefix.ne (by decide))).trans frame.hinput
    hcount := by simp
    hblankPrefix := ?_
    hbulkBlank := (keep _ (hg 14).symm).trans frame.hbulkBlank
    hblankGather := fun j hj => (keep _ (hg j).symm).trans (frame.hblankGather j hj)
    hstride := (keep _ (hg 1).symm).trans frame.hstride
    hresidue := (keep _ (hg 11).symm).trans frame.hresidue
    htmpGather := (keep _ (hg 16).symm).trans frame.htmpGather
    hsavedGather := (keep _ (hg 15).symm).trans frame.hsavedGather
    haccumGather := (keep _ (hg 17).symm).trans frame.haccumGather
    hblankGenerate := fun j hj hj5 => (keep _ (hp j).symm).trans (frame.hblankGenerate j hj hj5)
    htmpGenerate := (keep _ (hp 9).symm).trans frame.htmpGenerate
    hsavedGenerate := (keep _ (hp 8).symm).trans frame.hsavedGenerate
    haccumGenerate := (keep _ (hp 10).symm).trans frame.haccumGenerate
    hsourceBlank := (keep _ (hp 7).symm).trans frame.hsourceBlank }
  intro j hj
  exact (keep _ (frame.hprefix.ne (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide))).trans
    (frame.hblankPrefix j hj)

theorem matchingProfileGeneratedCount_exec (body : P → Pr P T Q A U)
    (p : Par) (mate : Fin p.wy → Fin p.wy) (Li Lk Ln Le : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (dst : Fin T)
    (frame : MatchingProductionFrame p mate Li Lk (Ln + Lk + Le) dst S)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg)
    (hjoin : frame.extract 0 = rg 4) (hdst : dst ≠ rg 4)
    (hg : ∀ j, frame.extract 0 ≠ frame.gather j) (hp : ∀ j, frame.extract 0 ≠ frame.generate j)
    (hn : p.n < 2 ^ Ln) (he : 2 * (Li + Lk) + 2 < 2 ^ Le)
    (hrows : S.R (rg 0) = binSyms Ln p.n) (hstride : S.R (rg 1) = binSyms Lk p.K)
    (hwidth : S.R (rg 11) = binSyms Le (Li + Lk))
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 10 → j ≠ 11 → S.R (rg j) = []) :
    let output := sourceCoordinateInputWords Li Lk
      (profileCoordinateInputs p frame.hK (matchingDirectionTargets mate frame.reverse) mate) ++ S.R dst
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ matchingPrefixCountCost Ln Lk Le + 24 * Le + 29 +
        matchingFullProfileProductionCost p (Li + Lk) Lk (Ln + Lk + Le) + 2 * (Ln + Lk + Le) + 2 ∧
      Exec body (matchingPrefixCountScope rg
        (matchingFullProfileProductionProgram frame.extract frame.gather frame.generate frame.reverse dst))
        (mk v S) m (mk v' { S with R := Function.update S.R dst output }) := by
  dsimp only
  apply matchingPrefixCountScope_exec body rg hrg Ln Lk Le p.n p.K (Li + Lk)
    hn frame.hk he v S hrows hstride hwidth hblank dst hdst _ _ _
  intro u
  have hslots : p.n * p.K < 2 ^ (Ln + Lk) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt hn frame.hk
  have hfit : (p.n * p.K) * (2 * (Li + Lk) + 2) < 2 ^ (Ln + Lk + Le) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt hslots he
  let ready := frame.with_count hg hp hfit
  obtain ⟨u', m, hu, hm, hex⟩ := ready.exec body u
  dsimp only [ready, MatchingProductionFrame.with_count] at hex
  simp only [hjoin] at hex
  have hkeep : Function.update S.R (rg 4)
      (binSyms (Ln + Lk + Le) ((p.n * p.K) * (2 * (Li + Lk) + 2))) dst = S.R dst :=
    Function.update_of_ne hdst _ _
  rw [hkeep] at hex
  exact ⟨u', m, hu, hm, hex⟩

end
end IntegerMultBounds.MathlibTM2.Routing
