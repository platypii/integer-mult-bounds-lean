module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingFullProfileProduction

/-! Pure layout and readiness data for the actual full-table input producer.
No field postulates an execution or a time bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

structure MatchingProductionSetup (p : Par) (mate : Fin p.wy → Fin p.wy)
    (Li Lk Lc : ℕ) (dst : Fin T) (S : Stacks T A) where
  extract : Fin 8 → Fin T
  hprefix : Function.Injective extract
  gather : Fin 18 → Fin T
  hgather : Function.Injective gather
  generate : Fin 11 → Fin T
  hgenerate : Function.Injective generate
  hseparate : ∀ j, generate 7 ≠ gather j
  hdst : ∀ j, dst ≠ generate j
  hjoin : extract 6 = gather 14
  hgenerateSource : ∀ j, generate j ≠ gather 14
  hdstBulk : dst ≠ gather 14
  hK : 0 < p.K
  hρ : p.ρ < p.K
  hinv : Function.Involutive mate
  reverse : Bool
  hwidth : p.wy < 2 ^ (Li + Lk)
  hk : p.K < 2 ^ Lk
  hcountFit : (p.n * p.K) * (2 * (Li + Lk) + 2) < 2 ^ Lc
  hinput : S.R (extract 5) = matchingEntryWords (Li + Lk) (matchingTableEntries p.wy (matchingMateCoordinate mate))
  hcount : S.R (extract 0) = binSyms Lc ((p.n * p.K) * (2 * (Li + Lk) + 2))
  hblankPrefix : ∀ j : Fin 8, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 7 → S.R (extract j) = []
  hbulkBlank : S.R (gather 14) = []
  hblankGather : ∀ j : Fin 18, j = 0 ∨ j = 12 ∨ j = 13 ∨ (2 ≤ j.val ∧ j.val < 10) → S.R (gather j) = []
  hstride : S.R (gather 1) = binSyms Lk p.K
  hresidue : S.R (gather 11) = binSyms Lk p.ρ
  htmpGather : S.R (gather 16) = []
  hsavedGather : S.R (gather 15) = []
  haccumGather : S.R (gather 17) = []
  hblankGenerate : ∀ j : Fin 11, j.val < 7 → j ≠ 5 → S.R (generate j) = []
  htmpGenerate : S.R (generate 9) = []
  hsavedGenerate : S.R (generate 8) = []
  haccumGenerate : S.R (generate 10) = []
  hsourceBlank : S.R (generate 7) = []

theorem MatchingProductionSetup.exec {p : Par} {mate : Fin p.wy → Fin p.wy}
    {Li Lk Lc : ℕ} {dst : Fin T} {S : Stacks T A}
    (setup : MatchingProductionSetup p mate Li Lk Lc dst S)
    (body : P → Pr P T Q A U) (v : HS T Q A U) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ matchingFullProfileProductionCost p (Li + Lk) Lk Lc ∧
      Exec body (matchingFullProfileProductionProgram setup.extract setup.gather setup.generate setup.reverse dst)
        (IntegerMultBounds.MathlibTM2.Host.mk v S) steps
        (IntegerMultBounds.MathlibTM2.Host.mk v' { S with R := Function.update S.R dst (sourceCoordinateInputWords Li Lk (profileCoordinateInputs p setup.hK (matchingDirectionTargets mate setup.reverse) mate) ++ S.R dst) }) := by
  exact matchingFullProfileProduction_exec body
    setup.extract setup.hprefix setup.gather setup.hgather setup.generate setup.hgenerate setup.hseparate dst setup.hdst setup.hjoin setup.hgenerateSource setup.hdstBulk p setup.hK setup.hρ mate setup.hinv setup.reverse Li Lk Lc setup.hwidth setup.hk setup.hcountFit v S setup.hinput setup.hcount setup.hblankPrefix setup.hbulkBlank setup.hblankGather setup.hstride setup.hresidue setup.htmpGather setup.hsavedGather setup.haccumGather setup.hblankGenerate setup.htmpGenerate setup.hsavedGenerate setup.haccumGenerate setup.hsourceBlank

end
end IntegerMultBounds.MathlibTM2.Routing
