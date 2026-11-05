module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationCallerReady

/-! Publication readiness on the shared preparation endpoint. Owned publication
roles are retained by preparation and disjoint from every class setup output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section
variable {T A : ℕ}

theorem publicationOwnedRole (j : Fin 10) (hj : j ∈ [(0 : Fin 10),1,2,4,6,8,9]) :
    ∃ i : Fin 7, publicationRole j = .publication i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩

theorem output_ne_publication (T : ℕ) (j : Fin 10) : header T .output ≠ publication T j := by
  apply (header_injective T).ne
  intro h
  have hm : Role.output ∈ List.ofFn publicationRole :=
    h ▸ List.mem_ofFn.mpr ⟨j,rfl⟩
  simp [List.ofFn_succ,publicationRole] at hm

theorem publication_off_result (b : ComputedClassBank → Fin T) (j : Fin 10) :
    publication T j ≠ bank b (.recovery (.control .result)) :=
  header_ne_bank b (publicationRole j) _

theorem publicationOwned_off_class (T : ℕ) (j : Fin 10)
    (hj : j ∈ [(0 : Fin 10),1,2,4,6,8,9]) :
    classInputPortOff (masterSources T) (formats T) (classCallerRegister (publication T j)) := by
  obtain ⟨i,hi⟩ := publicationOwnedRole j hj
  change classInputPortOff (masterSources T) (formats T) (fullHeader T (publicationRole j))
  rw [hi]
  exact retained_off_class T (.publication i) rfl

/-- The publication placement needs only its two shared left stacks and the
private routing suffix. No global all-left-stacks-blank premise is required. -/
theorem publicationPlacement_leftBlank (b : ComputedClassBank → Fin T)
    (S : Stacks (MachineTapes T) A)
    (hresult : S.L (fullExposedClassBank (bank b) (.recovery (.control .result))) = [])
    (houtput : S.L (fullHeader T .output) = [])
    (hprivate : ∀ i, S.L (Fin.natAdd ((T+headerCount)+175) i) = []) :
    ∀ i, (embStk (selectedPublicationPlacement (bank b) (header T .output)) S).L i = [] := by
  intro i
  change S.L (selectedPublicationPlacement (bank b) (header T .output) i) = []
  by_cases hn : i = numericalPort
  · subst i
    rw [selectedPublicationPlacement,publicationPlacement_numerical]
    simpa only [fullExposedClassBank_apply,classCallerRegister,exposureIntoRouting] using hresult
  by_cases ho : i = ambientPort
  · subst i
    rw [selectedPublicationPlacement_ambient]
    exact houtput
  · rw [selectedPublicationPlacement_private (bank b) (header T .output) i hn ho]
    exact hprivate i

/-- Transport the seven fresh publication roles through the actual shared
preparation frame; reuse its left-stack restoration for publication placement. -/
theorem publicationReady_of_prepared (b : ComputedClassBank → Fin T)
    (S F : Stacks (MachineTapes T) A)
    (hblank : ∀ i : Fin 7, S.R (fullHeader T (.publication i)) = [])
    (hresult : S.L (fullExposedClassBank (bank b) (.recovery (.control .result))) = [])
    (houtput : S.L (fullHeader T .output) = [])
    (hprivate : ∀ i, S.L (Fin.natAdd ((T+headerCount)+175) i) = [])
    (hL : F.L = S.L)
    (hframe : ∀ k, k ≠ fullHeader T .word → k ≠ fullHeader T .replicas → k ≠ fullHeader T .volume →
      (∀ i, k ≠ globals T i) → (∀ f, k ≠ rulers T f) →
      (∀ f i, k ≠ fullHeader T (.geometry f i)) → F.R k = S.R k) :
    PublicationCallerReady (classCallerRegister ∘ publication T)
      (selectedPublicationPlacement (bank b) (header T .output)) F := by
  constructor
  · intro j hj
    obtain ⟨i,hi⟩ := publicationOwnedRole j hj
    change F.R (fullHeader T (publicationRole j)) = []
    rw [hi,hframe]
    · exact hblank i
    all_goals first
      | exact (fullHeader_injective T).ne (by intro h; cases h)
      | intro k; exact (fullHeader_injective T).ne (by intro h; cases h)
      | intro f k; exact (fullHeader_injective T).ne (by intro h; cases h)
  · intro i
    change F.L (selectedPublicationPlacement (bank b) (header T .output) i) = []
    rw [hL]
    exact publicationPlacement_leftBlank b S hresult houtput hprivate i

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
