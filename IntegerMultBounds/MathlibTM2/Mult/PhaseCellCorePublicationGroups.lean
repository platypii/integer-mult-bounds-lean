module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreSubsetPublication

/-! A finite list of publication classes can mix packed bulk rows and full-line
seam rows. Every selected row has the same target/error contract, so even
repeated selections do not accumulate numerical error. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

structure CorePublicationClass (s width : ℕ) where
  length : ℕ
  indices : List ℕ
  sublist : indices.Sublist (corePublicationIndices s width length)

namespace CorePublicationClass
variable {A s width : ℕ}

def output (g : CorePublicationClass s width) (w : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt) (E : List (Fin (A+4))) :=
  scatterRows (g.length*w) E (cstream A w (g.indices.map rows).flatten)
    ((coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).gaps w)

theorem source_length (g : CorePublicationClass s width) (w : ℕ)
    (rows : ℕ → List GaussianInt) (hrows : ∀ k ∈ g.indices, (rows k).length = g.length) :
    (cstream A w (g.indices.map rows).flatten).length = g.indices.length*(g.length*w) := by
  have hl : ∀ row ∈ g.indices.map rows, row.length = g.length := by
    intro row hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    exact hrows k hk
  simp only [length_cstream,length_flatten_const _ hl,List.length_map,Nat.mul_assoc]

theorem output_length (g : CorePublicationClass s width) (w : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt) (hrows : ∀ k ∈ g.indices, (rows k).length = g.length)
    (E : List (Fin (A+4))) (hE : E.length = s*w) : (g.output w hw rows E).length = s*w := by
  rw [output,length_scatterRows,hE]
  · exact PublicationWindows.gaps_fits _ w E hE.ge
  · simp only [PublicationWindows.gaps_length,coreSubsetPublicationWindows,
      PublicationWindows.restrict,List.length_map,g.source_length w rows hrows]
    exact le_rfl

variable [NeZero s]

theorem output_errorOn (g : CorePublicationClass s width) (q w : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt) (hrows : ∀ k ∈ g.indices, (rows k).length = g.length)
    (E : List (Fin (A+4))) (hE : E.length = s*w) (target : ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ k ∈ g.indices, PhaseCellInterface.ErrorOn (ownedCore s width k)
      (packedIntervalRead q w (coreStart width k) (cstream A w (rows k))) target error)
    (k : ℕ) (hk : k ∈ g.indices) :
    PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead q w (g.output w hw rows E)) target error :=
  coreSubsetPublication_errorOn width g.length q w hw g.indices g.sublist rows hrows E hE.ge target error hgood k hk

theorem output_preserves (g : CorePublicationClass s width) (q w : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt) (hrows : ∀ k ∈ g.indices, (rows k).length = g.length)
    (E : List (Fin (A+4))) (hE : E.length = s*w) (target : ZMod s → ℂ) (error : ℝ)
    (k : ℕ) (hk : k ∉ g.indices)
    (hgood : PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead q w E) target error) :
    PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead q w (g.output w hw rows E)) target error := by
  exact coreSubsetPublication_errorOn_preserves width g.length q w hw g.indices g.sublist E _ hE.ge
    (by rw [g.source_length w rows hrows]) k hk target error hgood
end CorePublicationClass

variable {A s width : ℕ}

def corePublicationGroupsOutput (w : ℕ) (hw : 0 < width)
    (rows : CorePublicationClass s width → ℕ → List GaussianInt) :
    List (CorePublicationClass s width) → List (Fin (A+4)) → List (Fin (A+4))
  | [], E => E
  | g::gs, E => corePublicationGroupsOutput w hw rows gs (g.output w hw (rows g) E)

theorem corePublicationGroupsOutput_length (w : ℕ) (hw : 0 < width)
    (rows : CorePublicationClass s width → ℕ → List GaussianInt)
    (gs : List (CorePublicationClass s width))
    (hrows : ∀ g ∈ gs, ∀ k ∈ g.indices, (rows g k).length = g.length)
    (E : List (Fin (A+4))) (hE : E.length = s*w) :
    (corePublicationGroupsOutput w hw rows gs E).length = s*w := by
  induction gs generalizing E with
  | nil => exact hE
  | cons g gs ih =>
    exact ih (fun g hg => hrows g (by simp [hg])) _
      (g.output_length w hw (rows g) (hrows g (by simp)) E hE)

/-- A core that was accurate or is selected by a later sweep finishes accurate.
Every overwrite uses a certified row; intervening sweeps preserve full words. -/
theorem corePublicationGroupsOutput_errorOn [NeZero s] (q w : ℕ) (hw : 0 < width)
    (rows : CorePublicationClass s width → ℕ → List GaussianInt)
    (gs : List (CorePublicationClass s width))
    (hrows : ∀ g ∈ gs, ∀ k ∈ g.indices, (rows g k).length = g.length)
    (target : ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ g ∈ gs, ∀ k ∈ g.indices, PhaseCellInterface.ErrorOn (ownedCore s width k)
      (packedIntervalRead q w (coreStart width k) (cstream A w (rows g k))) target error)
    (E : List (Fin (A+4))) (hE : E.length = s*w) (k : ℕ)
    (hstart : PhaseCellInterface.ErrorOn (ownedCore s width k) (pairedCellRead q w E) target error ∨
      ∃ g ∈ gs, k ∈ g.indices) :
    PhaseCellInterface.ErrorOn (ownedCore s width k)
      (pairedCellRead q w (corePublicationGroupsOutput w hw rows gs E)) target error := by
  induction gs generalizing E with
  | nil => simpa [corePublicationGroupsOutput] using hstart
  | cons g gs ih =>
    have hl := hrows g (by simp)
    have he := g.output_length w hw (rows g) hl E hE
    apply ih (fun g hg => hrows g (by simp [hg])) (fun g hg => hgood g (by simp [hg])) _ he
    by_cases hk : k ∈ g.indices
    · exact Or.inl (g.output_errorOn q w hw (rows g) hl E hE target error (hgood g (by simp)) k hk)
    · rcases hstart with hs | ⟨g',hg',hk'⟩
      · exact Or.inl (g.output_preserves q w hw (rows g) hl E hE target error k hk hs)
      · right
        refine ⟨g',?_,hk'⟩
        rcases List.mem_cons.mp hg' with rfl | hg'
        · exact False.elim (hk hk')
        · exact hg'

/-- Any finite collection of certified classes covering the cores gives one
uniform global error bound, independent of the number of publication sweeps. -/
theorem corePublicationGroupsOutput_error [NeZero s] (q w : ℕ) (hw : 0 < width)
    (rows : CorePublicationClass s width → ℕ → List GaussianInt)
    (gs : List (CorePublicationClass s width))
    (hrows : ∀ g ∈ gs, ∀ k ∈ g.indices, (rows g k).length = g.length)
    (hcover : ∀ k ∈ coreIndices s width, ∃ g ∈ gs, k ∈ g.indices)
    (target : ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ g ∈ gs, ∀ k ∈ g.indices, PhaseCellInterface.ErrorOn (ownedCore s width k)
      (packedIntervalRead q w (coreStart width k) (cstream A w (rows g k))) target error)
    (E : List (Fin (A+4))) (hE : E.length = s*w) :
    ∀ i, ‖pairedCellRead q w (corePublicationGroupsOutput w hw rows gs E) i-target i‖ ≤ error := by
  intro i
  obtain ⟨k,hk,hi⟩ := ownedCore_cover width hw i
  exact corePublicationGroupsOutput_errorOn q w hw rows gs hrows target error hgood E hE k
    (Or.inr (hcover k hk)) i hi

def corePublicationGroupsCost {s width : ℕ} (w : ℕ) (hw : 0 < width)
    (gs : List (CorePublicationClass s width)) : ℕ :=
  (gs.map (fun g => (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist).cost w)).sum

theorem corePublicationGroupsCost_le {s width : ℕ} (w : ℕ) (hw : 0 < width)
    (gs : List (CorePublicationClass s width)) (hw1 : 1 ≤ w) :
    corePublicationGroupsCost w hw gs ≤ gs.length*(35*s*w+6) := by
  induction gs with
  | nil => simp [corePublicationGroupsCost]
  | cons g gs ih =>
    have hg := coreSubsetPublication_cost_le s width g.length w hw g.indices g.sublist hw1
    simp only [corePublicationGroupsCost,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    omega

/-- Splitting both core lengths by any bulk/seam selector gives four classes.
The selector describes geometry; this definition asserts no setup-key reuse. -/
def splitCorePublicationClasses (s width : ℕ) (bulk : ℕ → Bool) : List (CorePublicationClass s width) :=
  let part := fun L keep => (⟨L,(corePublicationIndices s width L).filter keep,List.filter_sublist⟩ : CorePublicationClass s width)
  [part width bulk,part (s%width) bulk,part width (fun k => !(bulk k)),part (s%width) (fun k => !(bulk k))]

theorem splitCorePublicationClasses_cover (s width : ℕ) (hw : 0 < width) (bulk : ℕ → Bool) :
    ∀ k ∈ coreIndices s width, ∃ g ∈ splitCorePublicationClasses s width bulk, k ∈ g.indices := by
  intro k hk
  have hm (L : ℕ) (he : coreLength s width k = L) : k ∈ corePublicationIndices s width L :=
    (mem_corePublicationIndices ..).mpr ⟨hk,he⟩
  rcases coreLength_cases s width k hw hk with he | he
  all_goals
    by_cases hb : bulk k = true
    · simp only [splitCorePublicationClasses,List.mem_cons,List.not_mem_nil,or_false]
      first
      | exact ⟨_,Or.inl rfl,List.mem_filter.mpr ⟨hm _ he,hb⟩⟩
      | exact ⟨_,Or.inr (Or.inl rfl),List.mem_filter.mpr ⟨hm _ he,hb⟩⟩
    · have hn : (!(bulk k)) = true := by cases h : bulk k <;> simp_all
      simp only [splitCorePublicationClasses,List.mem_cons,List.not_mem_nil,or_false]
      first
      | exact ⟨_,Or.inr (Or.inr (Or.inl rfl)),List.mem_filter.mpr ⟨hm _ he,hn⟩⟩
      | exact ⟨_,Or.inr (Or.inr (Or.inr rfl)),List.mem_filter.mpr ⟨hm _ he,hn⟩⟩

theorem splitCorePublicationClasses_cost_le (s width w : ℕ) (hw : 0 < width)
    (bulk : ℕ → Bool) (hw1 : 1 ≤ w) :
    corePublicationGroupsCost w hw (splitCorePublicationClasses s width bulk) ≤ 4*(35*s*w+6) := by
  simpa only [splitCorePublicationClasses,List.length_cons,List.length_nil] using
    corePublicationGroupsCost_le w hw (splitCorePublicationClasses s width bulk) hw1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
