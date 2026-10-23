module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateGenerate

/-! Execute bulk-profile source-record production from physical coordinates
and activity. The output is exactly the record stream used by profile repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def profileCoordinateInputs (p : Par) (hK : 0 < p.K) (targets : Finset (Fin p.wy))
    (source : Fin p.wy → Fin p.wy) : List (ℕ × Bool) :=
  List.ofFn (fun c => ((profileSourceCoordinate p hK targets source c).val, profileActive p hK targets c))

theorem profileCoordinateOutput_records (p : Par) (hK : 0 < p.K) (X Li Lk : ℕ)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy) :
    sourceCoordinateOutputWords (A := A) Li Lk p.ρ (p.ρ + p.n * p.K) p.K
      (profileCoordinateInputs p hK targets source) = profileSourceRecords p hK X targets source Li Lk := by
  unfold sourceCoordinateOutputWords profileCoordinateInputs profileSourceRecords
  rw [List.map_ofFn]
  apply congrArg (gatedSelectedSourceWords Li Lk)
  apply congrArg List.ofFn
  funext c
  exact sourceCoordinateChoice_profile p hK X targets source c

theorem profileCoordinateGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg) (src saved tmp accum out : Fin T)
    (hreg : [src, saved, tmp, accum, out].Nodup)
    (hsrc : ∀ j, src ≠ rg j) (hsaved : ∀ j, saved ≠ rg j) (htmp : ∀ j, tmp ≠ rg j)
    (hacc : ∀ j, accum ≠ rg j)
    (p : Par) (hK : 0 < p.K) (X Li Lk : ℕ)
    (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (hw : p.wy < 2 ^ (Li + Lk)) (hk : p.K < 2 ^ Lk)
    (v : HS T Q A U) (S : Stacks T A)
    (setup : SourceCoordinateSetup rg Li Lk p.ρ (p.ρ + p.n * p.K) p.K S)
    (hraw : S.R src = sourceCoordinateInputWords Li Lk (profileCoordinateInputs p hK targets source))
    (htmpBlank : S.R tmp = []) (houtput : S.R (rg 19) = [])
    (hsavedBlank : S.R saved = []) (haccum : S.R accum = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * sourceCoordinateIterationCost Li Lk +
        2 * (p.n * (Li + Lk + 3)) + 2 * (p.n * (Li + (Li + Lk) + 5)) + 6 ∧
      Exec body (sourceCoordinateGenerateProgram rg src saved tmp accum out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (profileSourceRecords p hK X targets source Li Lk ++ S.R out) }) := by
  have hy : p.wy = p.ρ + p.n * p.K + p.m := rfl
  have hfit : ∀ x ∈ profileCoordinateInputs p hK targets source, x.1 < 2 ^ (Li + Lk) := by
    intro x hx
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hx
    exact (profileSourceCoordinate p hK targets source c).isLt.trans hw
  obtain ⟨v', steps, hu, ht, hx⟩ := sourceCoordinateGenerate_exec body rg hrg src saved tmp accum out hreg
    hsrc hsaved htmp hacc Li Lk p.ρ (p.ρ + p.n * p.K) p.K (by omega) (by omega) hk hK
    (profileCoordinateInputs p hK targets source) hfit v S setup hraw htmpBlank houtput hsavedBlank haccum
  rw [profileCoordinateOutput_records p hK X Li Lk targets source] at hx
  exact ⟨v', steps, hu, by simpa [profileCoordinateInputs] using ht, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
