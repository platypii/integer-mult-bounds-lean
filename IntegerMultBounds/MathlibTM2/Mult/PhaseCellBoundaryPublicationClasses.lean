module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringPublicationClasses
public import IntegerMultBounds.NLogN.PhaseCellBoundaryCropSchedule

/-! Boundary slots supply singleton publication classes. The restoring fold
allows these classes to overlap the proper sweep without accumulating error. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellMatrix

/-- A singleton retains the actual length of its owned core, including clipping. -/
def singletonCorePublication (s width k : ℕ) (hk : k ∈ coreIndices s width) :
    CorePublicationClass s width where
  length := coreLength s width k
  indices := [k]
  sublist := List.singleton_sublist.mpr ((mem_corePublicationIndices ..).mpr ⟨hk,rfl⟩)

def boundaryPublicationClasses (s width : ℕ) (hw : 0 < width) (hroom : 3*width < s) :
    List (CorePublicationClass s width) :=
  (boundaryCropSchedule s width).reverse.attach.map (fun k =>
    singletonCorePublication s width k.val
      ((boundaryCropSchedule_spec s width hw hroom).2.2 k.val (List.mem_reverse.mp k.property)).1)

theorem boundaryPublicationClasses_cover (s width k : ℕ) (hw : 0 < width)
    (hroom : 3*width < s) (hk : k ∈ boundaryCropSchedule s width) :
    ∃ g ∈ boundaryPublicationClasses s width hw hroom, k ∈ g.indices := by
  let x : {k // k ∈ (boundaryCropSchedule s width).reverse} := ⟨k,List.mem_reverse.mpr hk⟩
  refine ⟨_,List.mem_map.mpr ⟨x,List.mem_attach _ _,rfl⟩,?_⟩
  exact List.mem_singleton.mpr rfl

/-- This is exactly the coverage premise of restoringPublicationClasses_exec_within.
No disjointness between the proper class and boundary classes is needed. -/
theorem proper_boundaryPublicationClasses_cover (s width band n : ℕ)
    (hw : 0 < width) (hr : 0 < n*band) (hrw : n*band ≤ width) (hroom : 3*width < s)
    (proper : CorePublicationClass s width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band))) :
    ∀ k ∈ coreIndices s width,
      ∃ g ∈ proper::boundaryPublicationClasses s width hw hroom, k ∈ g.indices := by
  intro k hk
  rcases fullGather_or_boundaryCropSchedule s width band n k hw hr hrw hroom hk with hp | hb
  · exact ⟨proper,by simp,by rwa [hproper]⟩
  · obtain ⟨g,hg,hk⟩ := boundaryPublicationClasses_cover s width k hw hroom hb
    exact ⟨g,List.mem_cons_of_mem _ hg,hk⟩

/-- Proper publication initializes the remaining boundary accuracy invariant. -/
theorem boundaryPublication_pending_of_proper {A s : ℕ} [NeZero s]
    (width band n q W : ℕ) (hw : 0 < width) (hr : 0 < n*band)
    (hrw : n*band ≤ width) (hroom : 3*width < s)
    (proper : CorePublicationClass s width)
    (hproper : proper.indices = coreGatherIndices s width (n*band) (width+2*(n*band)))
    (ambient : List (Fin (A+4))) (target : ZMod s → ℂ) (error : ℝ)
    (hgood : ∀ k ∈ proper.indices,
      PhaseCellInterface.ErrorOn (ownedCore s width k)
        (pairedCellRead q W ambient) target error) :
    CorePublicationPending (boundaryPublicationClasses s width hw hroom) q W ambient target error :=
  CorePublicationPending.of_covered_class proper _ q W ambient target error
    (proper_boundaryPublicationClasses_cover s width band n hw hr hrw hroom proper hproper) hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
