import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceStages

/-! The complete prepared later-source physical schedule: early4, source load
through U/back, early4 using the updated U word, and source unload through
U/back. This contains twelve real swaps and ten real full-array rotations. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceRun
noncomputable section
open ActivePrefixDirtyControlSequenceData ActivePrefixDirtyControlSequenceStages
open ActivePrefixDirtyControlConjugationData (FullArray)
open CompactGadgetReservationShape (Shape)
open Networks.Shared50ModularControl (prime)

/-- Fixed four-stage sequencing keeps large finite-control counts abstract. -/
def four {t a c₀ c₁ c₂ c₃ : ℕ} (p₀ : Program t c₀ a) (p₁ : Program t c₁ a)
    (p₂ : Program t c₂ a) (p₃ : Program t c₃ a) := seq (seq (seq p₀ p₁) p₂) p₃

theorem four_runs {t a c₀ c₁ c₂ c₃ b₀ b₁ b₂ b₃ : ℕ}
    {p₀ : Program t c₀ a} {p₁ : Program t c₁ a} {p₂ : Program t c₂ a} {p₃ : Program t c₃ a}
    {P₀ P₁ P₂ P₃ P₄ : Tapes t a → Prop}
    (h₀ : HoareTime p₀ P₀ P₁ b₀) (h₁ : HoareTime p₁ P₁ P₂ b₁)
    (h₂ : HoareTime p₂ P₂ P₃ b₂) (h₃ : HoareTime p₃ P₃ P₄ b₃) :
    HoareTime (four p₀ p₁ p₂ p₃) P₀ P₄ (b₀+b₁+b₂+b₃+3) :=
  (((h₀.seq h₁).seq h₂).seq h₃).consequence (fun _ h => h) (fun _ h => h) (by omega)


def earlyProgramFor (a b : ActivePrefixDirtyControlConjugationData.Kind) :=
  four selectedProgram (tProgram a) correctionProgram (tProgram b)
def programFor (a b c d : ActivePrefixDirtyControlConjugationData.Kind) :=
  four (earlyProgramFor a b) (uProgram c) (earlyProgramFor a b) (uProgram d)
def earlyProgram := earlyProgramFor .tPure .tNegative
def program := programFor .tPure .tNegative .uPure .uNegative

def earlyCost (s : Shape) (g : Geometry s) := 2*targetCost s g.rows+pureCost s g+negativeCost s g+3
def cost (s : Shape) (g : Geometry s) := 2*earlyCost s g+loadCost s g+unloadCost s g+3

variable {s : Shape} {g : Geometry s}
def earlyFor (a b : ActivePrefixDirtyControlConjugationData.Kind) (g : Geometry s) (x : FullArray s g.rows) :=
  tResult b g (correction g (tResult a g (selected g x)))
def laterFor (a b c d : ActivePrefixDirtyControlConjugationData.Kind) (g : Geometry s) (x : FullArray s g.rows) :=
  uResult d g (earlyFor a b g (uResult c g (earlyFor a b g x)))
def earlyCostFor (a b : ActivePrefixDirtyControlConjugationData.Kind) (s : Shape) (g : Geometry s) :=
  2*targetCost s g.rows+tCost a s g+tCost b s g+3
def costFor (a b c d : ActivePrefixDirtyControlConjugationData.Kind) (s : Shape) (g : Geometry s) :=
  2*earlyCostFor a b s g+uCost c s g+uCost d s g+3

theorem early_runs_for (a b : ActivePrefixDirtyControlConjugationData.Kind) (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime (earlyProgramFor a b) (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (earlyFor a b g x))) (earlyCostFor a b s g) := by
  have h := four_runs (selected_runs d x) (t_runs a d (selected g x))
    (correction_runs d (tResult a g (selected g x))) (t_runs b d (correction g (tResult a g (selected g x))))
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold earlyCostFor; omega)

theorem runs_for (a b c e : ActivePrefixDirtyControlConjugationData.Kind) (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime (programFor a b c e) (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (laterFor a b c e g x))) (costFor a b c e s g) := by
  have h := four_runs (early_runs_for a b d x) (u_runs c d (earlyFor a b g x))
    (early_runs_for a b d (uResult c g (earlyFor a b g x)))
    (u_runs e d (earlyFor a b g (uResult c g (earlyFor a b g x))))
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold costFor; omega)

theorem early_runs (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime earlyProgram (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (early g x))) (earlyCost s g) := early_runs_for .tPure .tNegative d x

theorem runs (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime program (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (later g x))) (cost s g) := runs_for .tPure .tNegative .uPure .uNegative d x

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceRun
