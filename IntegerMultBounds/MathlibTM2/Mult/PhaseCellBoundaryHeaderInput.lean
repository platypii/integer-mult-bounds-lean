module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamLoadedReady
public import IntegerMultBounds.NLogN.PhaseCellBoundaryCropLengths

/-! Ordinary retained boundary scalars and blank destinations. The full crop
product is generated once, then shared by the first and penultimate slots. -/
@[expose] public section
set_option autoImplicit false
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ}

structure BoundaryUnaryScalars (p width W D N : ℕ) (words : Fin 11 → List (Fin (A+4))) : Prop where
  clock : (words 0).length = N
  line : (words 1).length = s
  wide : (words 2).length = W
  word : (words 3).length = 2*p+13
  ruler : (words 7).length = D
  core : (words 9).length = width

structure BoundaryHeaderScalars (p width W D N : ℕ) (seedValue : Fin 117 → ℕ)
    (words : Fin 11 → List (Fin (A+4))) : Prop extends
    BoundaryUnaryScalars (s := s) p width W D N words where
  seeds : ∀ j, words (boundarySeamSeedMaster j) = binSyms D (seedValue (boundarySeedGlobals j))

def boundaryWorkingMasters (masters : Fin 11 → Fin 117) (i : Fin 11) : Fin 117 :=
  if i = 9 then masters 8 else masters i

structure BoundaryHeaderLayout (masters : Fin 11 → Fin 117) : Prop where
  separated : ∀ i, ∀ k ∈ List.ofFn boundarySeamMasterRole++[27,28], masters i ≠ k
  dataOff : ∀ i, masters i ≠ 95 ∧ masters i ≠ 96
  productReg : [masters 9,masters 3,masters 8,27,28].Nodup
  fullOff : ∀ i, i ≠ 8 → i ≠ 9 → masters i ≠ masters 8
  mastersPrivate : ∀ i, 63 ≤ (masters i).val
  lastOff : ∀ i, i ≠ 10 → masters i ≠ masters 10

structure BoundaryHeaderCore (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S : Stacks 117 A) : Prop extends BoundaryHeaderLayout masters where
  scalars : BoundaryHeaderScalars (s := s) p width W D N seedValue (fun i => S.R (masters i))
  fullBlank : S.R (masters 8) = []
  blank : ∀ i, i.val < 63 → i ≠ 95 → i ≠ 96 → S.R i = []

structure BoundaryHeaderInput (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S : Stacks 117 A) : Prop extends
    BoundaryHeaderCore (s := s) p width W D N masters seedValue S where
  lastCrop : (S.R (masters 10)).length = coreLength s width (boundaryCropIndex s width 2)*(2*p+13)

structure BoundaryHeaderSource (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S : Stacks 117 A) : Prop extends
    BoundaryHeaderCore (s := s) p width W D N masters seedValue S where
  lastBlank : S.R (masters 10) = []

theorem BoundaryHeaderCore.of_frame (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S F : Stacks 117 A)
    (h : BoundaryHeaderCore (s := s) p width W D N masters seedValue S)
    (hread : ∀ i, i ≠ 95 → i ≠ 96 → F.R i = S.R i) :
    BoundaryHeaderCore (s := s) p width W D N masters seedValue F := by
  refine ⟨h.toBoundaryHeaderLayout,?_,?_,?_⟩
  · have hm : (fun i => F.R (masters i)) = (fun i => S.R (masters i)) :=
      funext (fun i => hread _ (h.dataOff i).1 (h.dataOff i).2)
    rw [hm]
    exact h.scalars
  · rw [hread _ (h.dataOff 8).1 (h.dataOff 8).2]
    exact h.fullBlank
  · intro i hi hs hd
    rw [hread i hs hd]
    exact h.blank i hi hs hd

theorem BoundaryHeaderInput.of_frame (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S F : Stacks 117 A)
    (h : BoundaryHeaderInput (s := s) p width W D N masters seedValue S)
    (hread : ∀ i, i ≠ 95 → i ≠ 96 → F.R i = S.R i) :
    BoundaryHeaderInput (s := s) p width W D N masters seedValue F := by
  refine ⟨h.toBoundaryHeaderCore.of_frame p width W D N masters seedValue S F hread,?_⟩
  rw [hread _ (h.dataOff 10).1 (h.dataOff 10).2]
  exact h.lastCrop

theorem BoundaryHeaderSource.of_frame (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (seedValue : Fin 117 → ℕ) (S F : Stacks 117 A)
    (h : BoundaryHeaderSource (s := s) p width W D N masters seedValue S)
    (hread : ∀ i, i ≠ 95 → i ≠ 96 → F.R i = S.R i) :
    BoundaryHeaderSource (s := s) p width W D N masters seedValue F := by
  refine ⟨h.toBoundaryHeaderCore.of_frame p width W D N masters seedValue S F hread,?_⟩
  rw [hread _ (h.dataOff 10).1 (h.dataOff 10).2]
  exact h.lastBlank

theorem BoundaryHeaderInput.words_of_full {p width W D N : ℕ} {masters : Fin 11 → Fin 117}
    {seedValue : Fin 117 → ℕ} {S F : Stacks 117 A}
    (h : BoundaryHeaderInput (s := s) p width W D N masters seedValue S)
    (hw : 0 < width) (hroom : 3*width < s)
    (hfull : (F.R (masters 8)).length = width*(2*p+13))
    (hframe : ∀ i, i ≠ masters 8 → F.R i = S.R i) :
    BoundarySeamHeaderWords (s := s) p width W D N seedValue
      (fun i => F.R (boundaryWorkingMasters masters i)) := by
  have hr (i : Fin 11) (hi : i ≠ 8) (hj : i ≠ 9) := hframe _ (h.fullOff i hi hj)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change (F.R (masters 0)).length = N
    rw [hr 0 (by decide) (by decide)]; exact h.scalars.clock
  · change (F.R (masters 1)).length = s
    rw [hr 1 (by decide) (by decide)]; exact h.scalars.line
  · change (F.R (masters 2)).length = W
    rw [hr 2 (by decide) (by decide)]; exact h.scalars.wide
  · change (F.R (masters 3)).length = 2*p+13
    rw [hr 3 (by decide) (by decide)]; exact h.scalars.word
  · intro j
    have hworking : boundaryWorkingMasters masters (boundarySeamSeedMaster j) = masters (boundarySeamSeedMaster j) := by
      fin_cases j <;> rfl
    rw [hworking,hr _ (by fin_cases j <;> decide) (by fin_cases j <;> decide)]
    exact h.scalars.seeds j
  · change (F.R (masters 7)).length = D
    rw [hr 7 (by decide) (by decide)]; exact h.scalars.ruler
  · intro slot
    fin_cases slot
    · change (F.R (masters 8)).length = coreLength s width (boundaryCropIndex s width 0)*(2*p+13)
      rw [boundaryCropLengths s width hw hroom 0]; exact hfull
    · change (F.R (masters 8)).length = coreLength s width (boundaryCropIndex s width 1)*(2*p+13)
      rw [boundaryCropLengths s width hw hroom 1]; exact hfull
    · change (F.R (masters 10)).length = coreLength s width (boundaryCropIndex s width 2)*(2*p+13)
      rw [hr 10 (by decide) (by decide)]; exact h.lastCrop

theorem BoundaryHeaderInput.blank_of_full_frame {p width W D N : ℕ} {masters : Fin 11 → Fin 117}
    {seedValue : Fin 117 → ℕ} {S F : Stacks 117 A}
    (h : BoundaryHeaderInput (s := s) p width W D N masters seedValue S)
    (hframe : ∀ i, i ≠ masters 8 → F.R i = S.R i) :
    ∀ i, i.val < 63 → i ≠ 95 → i ≠ 96 → F.R i = [] := by
  intro i hi hs hd
  have hoff : i ≠ masters 8 := by
    intro heq
    have := h.mastersPrivate 8
    subst i
    omega
  rw [hframe i hoff]
  exact h.blank i hi hs hd

theorem BoundaryUnaryScalars.of_frame {p width W D N : ℕ} {words next : Fin 11 → List (Fin (A+4))}
    (h : BoundaryUnaryScalars (s := s) p width W D N words)
    (hread : ∀ i ∈ [(0 : Fin 11),1,2,3,7,9], next i = words i) :
    BoundaryUnaryScalars (s := s) p width W D N next := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hread 0 (by simp)]; exact h.clock
  · rw [hread 1 (by simp)]; exact h.line
  · rw [hread 2 (by simp)]; exact h.wide
  · rw [hread 3 (by simp)]; exact h.word
  · rw [hread 7 (by simp)]; exact h.ruler
  · rw [hread 9 (by simp)]; exact h.core

theorem BoundaryHeaderScalars.of_frame {p width W D N : ℕ} {seedValue : Fin 117 → ℕ}
    {words next : Fin 11 → List (Fin (A+4))}
    (h : BoundaryHeaderScalars (s := s) p width W D N seedValue words)
    (hread : ∀ i, i ≠ 10 → next i = words i) :
    BoundaryHeaderScalars (s := s) p width W D N seedValue next := by
  refine ⟨h.toBoundaryUnaryScalars.of_frame (fun i hi => hread i ?_),?_⟩
  · have hoff : ∀ i ∈ [(0 : Fin 11),1,2,3,7,9], i ≠ 10 := by decide +kernel
    exact hoff i hi
  · intro j
    rw [hread _ (by fin_cases j <;> decide)]
    exact h.seeds j

theorem BoundaryHeaderSource.with_last {p width W D N : ℕ} {masters : Fin 11 → Fin 117}
    {seedValue : Fin 117 → ℕ} {S F : Stacks 117 A}
    (h : BoundaryHeaderSource (s := s) p width W D N masters seedValue S)
    (hcount : (F.R (masters 10)).length = coreLength s width (boundaryCropIndex s width 2)*(2*p+13))
    (hread : ∀ i, i ≠ masters 10 → F.R i = S.R i) :
    BoundaryHeaderInput (s := s) p width W D N masters seedValue F := by
  refine ⟨⟨h.toBoundaryHeaderLayout,?_,?_,?_⟩,hcount⟩
  · exact h.scalars.of_frame (fun i hi => hread _ (h.lastOff i hi))
  · rw [hread _ (h.lastOff 8 (by decide))]; exact h.fullBlank
  · intro i hi hs hd
    have hoff : i ≠ masters 10 := by intro he; have hp := h.mastersPrivate 10; subst i; omega
    rw [hread i hoff]
    exact h.blank i hi hs hd

def boundaryBinarySeedHeaders (masters : Fin 11 → Fin 117) :=
  List.ofFn (fun j => masters (boundarySeamSeedMaster j))

structure BoundaryUnarySource (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (S : Stacks 117 A) : Prop extends BoundaryHeaderLayout masters where
  scalars : BoundaryUnaryScalars (s := s) p width W D N (fun i => S.R (masters i))
  fullBlank : S.R (masters 8) = []
  lastBlank : S.R (masters 10) = []
  blank : ∀ i, i.val < 63 → i ≠ 95 → i ≠ 96 → S.R i = []
  seedsBlank : ∀ i ∈ boundaryBinarySeedHeaders masters, S.R i = []
  seedReg : [masters 1,masters 9,masters 2,masters 4,masters 5,masters 6,masters 7].Nodup
  seedsOff : ∀ i, i ∉ [(4 : Fin 11),5,6] → ∀ j ∈ [(4 : Fin 11),5,6], masters i ≠ masters j

theorem BoundaryUnarySource.of_frame (p width W D N : ℕ) (masters : Fin 11 → Fin 117)
    (S F : Stacks 117 A) (h : BoundaryUnarySource (s := s) p width W D N masters S)
    (hread : ∀ i, i ≠ 95 → i ≠ 96 → F.R i = S.R i) :
    BoundaryUnarySource (s := s) p width W D N masters F := by
  refine ⟨h.toBoundaryHeaderLayout,?_,?_,?_,?_,?_,h.seedReg,h.seedsOff⟩
  · exact h.scalars.of_frame (fun i _ => hread _ (h.dataOff i).1 (h.dataOff i).2)
  · rw [hread _ (h.dataOff 8).1 (h.dataOff 8).2]; exact h.fullBlank
  · rw [hread _ (h.dataOff 10).1 (h.dataOff 10).2]; exact h.lastBlank
  · intro i hi hs hd; rw [hread i hs hd]; exact h.blank i hi hs hd
  · intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    rw [hread _ (h.dataOff _).1 (h.dataOff _).2]
    exact h.seedsBlank _ (List.mem_ofFn.mpr ⟨j,rfl⟩)

theorem BoundaryUnarySource.with_seeds {p width W D N : ℕ} {masters : Fin 11 → Fin 117}
    {S F : Stacks 117 A} (h : BoundaryUnarySource (s := s) p width W D N masters S)
    (seedValue : Fin 117 → ℕ)
    (hseeds : ∀ j, F.R (masters (boundarySeamSeedMaster j)) = binSyms D (seedValue (boundarySeedGlobals j)))
    (hframe : ∀ i, i ∉ boundaryBinarySeedHeaders masters → F.R i = S.R i) :
    BoundaryHeaderSource (s := s) p width W D N masters seedValue F := by
  have hread (i : Fin 11) (hi : i ∉ [(4 : Fin 11),5,6]) : F.R (masters i) = S.R (masters i) := by
    apply hframe
    intro hm
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
    exact h.seedsOff i hi _ (by fin_cases j <;> simp [boundarySeamSeedMaster]) hj.symm
  refine ⟨⟨h.toBoundaryHeaderLayout,⟨?_,hseeds⟩,?_,?_⟩,?_⟩
  · exact h.scalars.of_frame (fun i hi => hread i (by
      have hoff : ∀ i ∈ [(0 : Fin 11),1,2,3,7,9], i ∉ [(4 : Fin 11),5,6] := by decide +kernel
      exact hoff i hi))
  · rw [hread 8 (by decide)]; exact h.fullBlank
  · intro i hi hs hd
    rw [hframe i (by
      intro hm
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
      have hp := h.mastersPrivate (boundarySeamSeedMaster j)
      have hv := congrArg Fin.val hj
      omega)]
    exact h.blank i hi hs hd
  · rw [hread 10 (by decide)]; exact h.lastBlank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
