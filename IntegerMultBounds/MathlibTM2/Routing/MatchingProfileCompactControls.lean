module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingControlScope
public import IntegerMultBounds.MathlibTM2.Routing.MatchingProfileGeneratedCount

/-! Actual profile compilation with installed compact stride/residue controls
and a generated prefix count. All installed controls and arithmetic scratch restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

theorem matchingProfileCompactControls_exec (body : P → Pr P T Q A U)
    (p : Par) (mate : Fin p.wy → Fin p.wy) (Li Lk Ln Le : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (dst : Fin T)
    (control : Fin 7 → Fin T) (hcontrol : Function.Injective control)
    (hstride : S.R (control 0) = binSyms Lk p.K) (hresidue : S.R (control 1) = binSyms Lk p.ρ)
    (hcontrolBlank : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → S.R (control j) = [])
    (hdst : dst ≠ control 2 ∧ dst ≠ control 3)
    (frame : MatchingProductionFrame p mate Li Lk (Ln + Lk + Le) dst
      { S with R := matchingControlBank S.R control Lk p.K p.ρ })
    (hstrideJoin : frame.gather 1 = control 2) (hresidueJoin : frame.gather 11 = control 3)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg)
    (hoff : ∀ j, rg j ≠ control 2 ∧ rg j ≠ control 3)
    (hjoin : frame.extract 0 = rg 4) (hcountDst : dst ≠ rg 4)
    (hg : ∀ j, frame.extract 0 ≠ frame.gather j) (hp : ∀ j, frame.extract 0 ≠ frame.generate j)
    (hn : p.n < 2 ^ Ln) (he : 2 * (Li + Lk) + 2 < 2 ^ Le)
    (hrows : S.R (rg 0) = binSyms Ln p.n) (hcountStride : S.R (rg 1) = binSyms Lk p.K)
    (hwidth : S.R (rg 11) = binSyms Le (Li + Lk))
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 10 → j ≠ 11 → S.R (rg j) = []) :
    let output := sourceCoordinateInputWords Li Lk
      (profileCoordinateInputs p frame.hK (matchingDirectionTargets mate frame.reverse) mate) ++ S.R dst
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ matchingPrefixCountCost Ln Lk Le + 24 * Le + 29 +
        matchingFullProfileProductionCost p (Li + Lk) Lk (Ln + Lk + Le) + 2 * (Ln + Lk + Le) + 2 + 16 * Lk + 20 ∧
      Exec body (matchingControlScope control (matchingPrefixCountScope rg
        (matchingFullProfileProductionProgram frame.extract frame.gather frame.generate frame.reverse dst)))
        (mk v S) m (mk v' { S with R := Function.update S.R dst output }) := by
  dsimp only
  apply matchingControlScope_exec body control hcontrol Lk p.K p.ρ v S hstride hresidue hcontrolBlank dst hdst _ _ _
  intro u
  let C : Stacks T A := { S with R := matchingControlBank S.R control Lk p.K p.ρ }
  have keep (j : Fin 13) : C.R (rg j) = S.R (rg j) := by
    simp [C, matchingControlBank, (hoff j).1, (hoff j).2]
  have strideReady : C.R (frame.gather 1) = binSyms Lk p.K := by
    rw [hstrideJoin]
    simp [C, matchingControlBank]
  have residueReady : C.R (frame.gather 11) = binSyms Lk p.ρ := by
    rw [hresidueJoin]
    simp [C, matchingControlBank, hcontrol.eq_iff]
  let ready : MatchingProductionFrame p mate Li Lk (Ln + Lk + Le) dst C :=
    { frame with hstride := strideReady, hresidue := residueReady }
  obtain ⟨u', m, hu, hm, hex⟩ := matchingProfileGeneratedCount_exec body p mate Li Lk Ln Le u C dst ready
    rg hrg hjoin hcountDst hg hp hn he ((keep 0).trans hrows) ((keep 1).trans hcountStride)
    ((keep 11).trans hwidth) (fun j hj0 hj1 hj10 hj11 => (keep j).trans (hblank j hj0 hj1 hj10 hj11))
  have hdstC : C.R dst = S.R dst := by simp [C, matchingControlBank, hdst.1, hdst.2]
  change Exec body _ (mk u C) m (mk u' { C with R := (Function.update C.R dst
    (sourceCoordinateInputWords Li Lk
      (profileCoordinateInputs p frame.hK (matchingDirectionTargets mate frame.reverse) mate) ++ C.R dst)) }) at hex
  rw [hdstC] at hex
  exact ⟨u', m, hu, hm, hex⟩

end
end IntegerMultBounds.MathlibTM2.Routing
