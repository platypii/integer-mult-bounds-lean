module

public import IntegerMultBounds.MathlibTM2.Routing.ProfileSharedRegisters
public import IntegerMultBounds.MathlibTM2.Routing.CoordinateDescriptorCompile
public import Mathlib.Data.Fintype.EquivFin

/-! Live descriptor jobs share profile and compiler workspaces. Per-job profile,
dimension and row-count inputs occupy auxiliary tapes; descriptor outputs remain
in a disjoint core bank. All aliases are fixed independently of dimension values. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

instance : Fintype GroupedPositionReg := Fintype.ofList
  [.index, .group, .stride, .base, .quotient, .remainder, .divWide, .divRem, .divTmp,
    .offset, .product, .dst, .muls, .mult, .tx, .ty, .tz] (by intro r; cases r <;> simp)

instance : Fintype GroupedCoordinateReg := Fintype.ofList
  ((Finset.univ.toList.map GroupedCoordinateReg.arithmetic) ++ [.last, .wire, .one, .selector, .gap, .dst])
  (by intro r; cases r <;> simp)

instance : Fintype GroupedProfileReg := Fintype.ofList
  ((Finset.univ.toList.map GroupedProfileReg.coordinate) ++ [.src, .archive, .activity, .loadTmp])
  (by intro r; cases r <;> simp)

instance : Fintype SparseCoordinateReg := Fintype.ofList
  [.src, .archive, .target, .entry, .loadTmp, .cursor, .gap, .one, .dst, .tx, .ty, .tz]
  (by intro r; cases r <;> simp)

instance : Fintype BinaryZeroReg := Fintype.ofList
  ([.width, .unary, .dst] ++ Finset.univ.toList.map BinaryZeroReg.scratch)
  (by intro r; cases r <;> simp)

instance : Fintype SelectorRunReg := Fintype.ofList
  [.src, .archive, .gap, .entry, .loadTmp, .count, .saved, .block, .dst, .work, .tmp, .ctmp]
  (by intro r; cases r <;> simp)

instance : Fintype BinaryMaskReg := Fintype.ofList
  ([.width, .source, .low, .high, .dst] ++ Finset.univ.toList.map BinaryMaskReg.scratch)
  (by intro r; cases r <;> simp)

inductive LiveDescriptorRole (J : ℕ) where
  | input (j : Fin J) | stride (j : Fin J) | base (j : Fin J) | last (j : Fin J)
  | rows (j : Fin J) | sourceWidth (j : Fin J)
  | selectorBits | group
  | profile (r : GroupedProfileReg) | coordinate (r : SparseCoordinateReg)
  | zero (r : BinaryZeroReg) | runs (r : SelectorRunReg) | mask (r : BinaryMaskReg)
  | profileSaved | coordinateSaved | archive
  deriving DecidableEq, Fintype

def liveProfileRole {J : ℕ} (j : Fin J) : GroupedProfileReg → LiveDescriptorRole J
  | .src => .input j
  | .coordinate (.arithmetic .group) => .group
  | .coordinate (.arithmetic .stride) => .stride j
  | .coordinate (.arithmetic .base) => .base j
  | .coordinate .last => .last j
  | r => .profile r

def liveCoordinateRole {J : ℕ} : SparseCoordinateReg → LiveDescriptorRole J
  | .src => .profile (.coordinate .dst)
  | r => .coordinate r

def liveZeroRole {J : ℕ} : BinaryZeroReg → LiveDescriptorRole J
  | .width => .selectorBits
  | .dst => .runs .block
  | r => .zero r

def liveRunRole {J : ℕ} : SelectorRunReg → LiveDescriptorRole J
  | .src => .coordinate .dst
  | r => .runs r

def liveMaskRole {J : ℕ} (j : Fin J) : BinaryMaskReg → LiveDescriptorRole J
  | .width => .sourceWidth j
  | r => .mask r

private def profileDecode {J : ℕ} : LiveDescriptorRole J → Option GroupedProfileReg
  | .input _ => some .src
  | .group => some (.coordinate (.arithmetic .group))
  | .stride _ => some (.coordinate (.arithmetic .stride))
  | .base _ => some (.coordinate (.arithmetic .base))
  | .last _ => some (.coordinate .last)
  | .profile r => some r
  | _ => none

private theorem profileDecode_role {J : ℕ} (j : Fin J) (r : GroupedProfileReg) :
    profileDecode (liveProfileRole j r) = some r := by
  cases r <;> try rfl
  rename_i c
  cases c <;> try rfl
  rename_i a
  cases a <;> rfl

theorem liveProfileRole_injective {J : ℕ} (j : Fin J) : Function.Injective (liveProfileRole j) := by
  intro r s he
  simpa only [profileDecode_role, Option.some.injEq] using congrArg profileDecode he

private def coordinateDecode {J : ℕ} : LiveDescriptorRole J → Option SparseCoordinateReg
  | .profile (.coordinate .dst) => some .src
  | .coordinate r => some r
  | _ => none

private def zeroDecode {J : ℕ} : LiveDescriptorRole J → Option BinaryZeroReg
  | .selectorBits => some .width
  | .runs .block => some .dst
  | .zero r => some r
  | _ => none

private def runDecode {J : ℕ} : LiveDescriptorRole J → Option SelectorRunReg
  | .coordinate .dst => some .src
  | .runs r => some r
  | _ => none

private def maskDecode {J : ℕ} : LiveDescriptorRole J → Option BinaryMaskReg
  | .sourceWidth _ => some .width
  | .mask r => some r
  | _ => none

theorem liveCoordinateRole_injective {J : ℕ} : Function.Injective (liveCoordinateRole (J := J)) := by
  have hd (r : SparseCoordinateReg) : coordinateDecode (liveCoordinateRole (J := J) r) = some r := by cases r <;> rfl
  intro r s he
  simpa only [hd, Option.some.injEq] using congrArg coordinateDecode he

theorem liveZeroRole_injective {J : ℕ} : Function.Injective (liveZeroRole (J := J)) := by
  have hd (r : BinaryZeroReg) : zeroDecode (liveZeroRole (J := J) r) = some r := by cases r <;> rfl
  intro r s he
  simpa only [hd, Option.some.injEq] using congrArg zeroDecode he

theorem liveRunRole_injective {J : ℕ} : Function.Injective (liveRunRole (J := J)) := by
  have hd (r : SelectorRunReg) : runDecode (liveRunRole (J := J) r) = some r := by cases r <;> rfl
  intro r s he
  simpa only [hd, Option.some.injEq] using congrArg runDecode he

theorem liveMaskRole_injective {J : ℕ} (j : Fin J) : Function.Injective (liveMaskRole j) := by
  have hd (r : BinaryMaskReg) : maskDecode (liveMaskRole j r) = some r := by cases r <;> rfl
  intro r s he
  simpa only [hd, Option.some.injEq] using congrArg maskDecode he

abbrev liveDescriptorT (N J : ℕ) := N + Fintype.card (LiveDescriptorRole J)

def liveDescriptorCore {N J : ℕ} (i : Fin N) : Fin (liveDescriptorT N J) :=
  ⟨i.val, by have := i.isLt; unfold liveDescriptorT; omega⟩

def liveDescriptorAux {N J : ℕ} (r : LiveDescriptorRole J) : Fin (liveDescriptorT N J) :=
  ⟨N + (Fintype.equivFin (LiveDescriptorRole J) r).val, by
    have := (Fintype.equivFin (LiveDescriptorRole J) r).isLt; unfold liveDescriptorT; omega⟩

theorem liveDescriptorCore_injective {N J : ℕ} : Function.Injective (liveDescriptorCore (N := N) (J := J)) := by
  intro i j he
  exact Fin.ext (congrArg (fun x : Fin (liveDescriptorT N J) => x.val) he)

theorem liveDescriptorAux_injective {N J : ℕ} : Function.Injective (liveDescriptorAux (N := N) (J := J)) := by
  intro r s he
  apply (Fintype.equivFin (LiveDescriptorRole J)).injective
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [liveDescriptorAux] at hv
  omega

theorem liveDescriptorCore_aux {N J : ℕ} (i : Fin N) (r : LiveDescriptorRole J) :
    liveDescriptorCore i ≠ liveDescriptorAux r := by
  intro he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  simp only [liveDescriptorCore, liveDescriptorAux] at hv
  omega

def liveBankProfile {N J : ℕ} (j : Fin J) : GroupedProfileReg → Fin (liveDescriptorT N J) :=
  liveDescriptorAux ∘ liveProfileRole j

def liveBankCoordinate {N J : ℕ} : SparseCoordinateReg → Fin (liveDescriptorT N J) :=
  liveDescriptorAux ∘ liveCoordinateRole

def liveBankZero {N J : ℕ} : BinaryZeroReg → Fin (liveDescriptorT N J) := liveDescriptorAux ∘ liveZeroRole

def liveBankRuns {N J : ℕ} : SelectorRunReg → Fin (liveDescriptorT N J) := liveDescriptorAux ∘ liveRunRole

def liveBankMask {N J : ℕ} (j : Fin J) : BinaryMaskReg → Fin (liveDescriptorT N J) :=
  liveDescriptorAux ∘ liveMaskRole j

theorem liveBankProfile_injective {N J : ℕ} (j : Fin J) : Function.Injective (liveBankProfile (N := N) j) :=
  liveDescriptorAux_injective.comp (liveProfileRole_injective j)

theorem liveBankCoordinate_injective {N J : ℕ} : Function.Injective (liveBankCoordinate (N := N) (J := J)) :=
  liveDescriptorAux_injective.comp liveCoordinateRole_injective

theorem liveBankZero_injective {N J : ℕ} : Function.Injective (liveBankZero (N := N) (J := J)) :=
  liveDescriptorAux_injective.comp liveZeroRole_injective

theorem liveBankRuns_injective {N J : ℕ} : Function.Injective (liveBankRuns (N := N) (J := J)) :=
  liveDescriptorAux_injective.comp liveRunRole_injective

theorem liveBankMask_injective {N J : ℕ} (j : Fin J) : Function.Injective (liveBankMask (N := N) j) :=
  liveDescriptorAux_injective.comp (liveMaskRole_injective j)

end
end IntegerMultBounds.MathlibTM2.Routing
