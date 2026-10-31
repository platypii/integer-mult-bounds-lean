module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Core
public import IntegerMultBounds.Machine.HoareWithin

/-! Bounded phases mirror the existing exact phase language. Their intervals
are shared; the existing phase theorems retain the data semantics and runtime. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Core
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
noncomputable section
variable {t : ℕ}

def PhaseWithin {s : ℕ} (M : Program t s prime)
    (B : Descriptor → (ℕ → ZMod 2) → Tapes t prime) (u u' : Descriptor)
    (P : (ℕ → ZMod 2) → (ℕ → ZMod 2) → Prop) (c : ℕ) (H : TapePred t prime) : Prop :=
  ∀ X, HoareWithin M (· = B u X) (fun z => ∃ Y, P X Y ∧ z = B u' Y) c H

/-- Linear phases obtain prefix bounds from actual head travel, retaining
the original phase budget even when the caller reserves a larger allowance. -/
theorem Phase.within_heads {s c D : ℕ} {M : Program t s prime}
    {B : Descriptor → (ℕ → ZMod 2) → Tapes t prime} {u u' : Descriptor}
    {P : (ℕ → ZMod 2) → (ℕ → ZMod 2) → Prop} (h : Phase M B u u' P c)
    (hc : c ≤ D) (lo hi : ℤ)
    (hm : ∀ X j, lo+(D : ℕ) ≤ (B u X).head j ∧ (B u X).head j+(D : ℕ) ≤ hi) :
    PhaseWithin M B u u' P c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  intro X
  apply HoareWithin.of_time_heads (h X) lo hi
  rintro z rfl j
  have hb := hm X j
  omega

namespace PhaseWithin
variable {B B' : Descriptor → (ℕ → ZMod 2) → Tapes t prime}
  {H J : TapePred t prime} {s s' c c' : ℕ} {M : Program t s prime} {N : Program t s' prime}
  {u u' u'' : Descriptor} {P Q : (ℕ → ZMod 2) → (ℕ → ZMod 2) → Prop}

theorem time (h : PhaseWithin M B u u' P c H) : Phase M B u u' P c := fun X => (h X).time

theorem seq (hM : PhaseWithin M B u u' P c H) (hN : PhaseWithin N B u' u'' Q c' H) :
    PhaseWithin (Machine.seq M N) B u u'' (fun X Z => ∃ Y, P X Y ∧ Q Y Z) (c+1+c') H := by
  intro X
  refine (hM X).seq (middle := fun z => ∃ Y, P X Y ∧ z = B u' Y) ?_
  rintro z ⟨Y,hY,rfl⟩
  obtain ⟨n,hn,d,hr,hh,Z,hZ,hout⟩ := hN Y (B u' Y) rfl
  exact ⟨n,hn,d,hr,hh,Z,⟨Y,hY,hZ⟩,hout⟩

theorem mono (h : PhaseWithin M B u u' P c H) (hPQ : ∀ X Y, P X Y → Q X Y) (hc : c ≤ c')
    (hH : ∀ z, H z → J z) : PhaseWithin M B u u' Q c' J :=
  fun X => (h X).consequence (fun _ h => h) (fun _ ⟨Y,hY,hz⟩ => ⟨Y,hPQ X Y hY,hz⟩) hc hH

theorem congr (h : PhaseWithin M B u u' P c H) (hu : ∀ X, B u X = B' u X)
    (hu' : ∀ X, B u' X = B' u' X) : PhaseWithin M B' u u' P c H :=
  fun X => (h X).consequence (fun _ hz => hz.trans (hu X).symm)
    (fun _ ⟨Y,hY,hz⟩ => ⟨Y,hY,hz.trans (hu' Y)⟩) le_rfl (fun _ h => h)

end PhaseWithin

theorem core_hoare_within {B : Descriptor → (ℕ → ZMod 2) → Tapes t prime} {H : TapePred t prime}
    {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ : ℕ} {toTop : Program t s₁ prime}
    {shear₁ : Program t s₂ prime} {fam₁ : Program t s₃ prime} {shear₂ : Program t s₄ prime}
    {fam₂ : Program t s₅ prime} {shear₃ : Program t s₆ prime} {toLow : Program t s₇ prime}
    {leaf : Program t s₈ prime} {back : Program t s₉ prime}
    {v : Descriptor} {r w n : ℕ} [NeZero (prime ^ w)] (hr : r ≤ v.width)
    (hw : (Stage2Wrapper.top prime r v).width = n * w) {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ℕ}
    (h₁ : PhaseWithin toTop B v (Stage2Wrapper.top prime r v) Eq c₁ H)
    (h₂ : PhaseWithin shear₁ B (Stage2Wrapper.top prime r v) (Stage2Wrapper.top prime r v)
      (Stage2Wrapper.Moves prime (Stage2Wrapper.top prime r v) (Stage2Wrapper.shear (prime ^ w) n fun h d => d - h)) c₂ H)
    (h₃ : PhaseWithin fam₁ B (Stage2Wrapper.top prime r v) (Stage2Wrapper.top prime r v) (RevMachine.RevT prime w n (Stage2Wrapper.top prime r v)) c₃ H)
    (h₄ : PhaseWithin shear₂ B (Stage2Wrapper.top prime r v) (Stage2Wrapper.top prime r v)
      (Stage2Wrapper.Moves prime (Stage2Wrapper.top prime r v) (Stage2Wrapper.shear (prime ^ w) n fun h d => d + h)) c₄ H)
    (h₅ : PhaseWithin fam₂ B (Stage2Wrapper.top prime r v) (Stage2Wrapper.top prime r v) (RevMachine.RevT prime w n (Stage2Wrapper.top prime r v)) c₅ H)
    (h₆ : PhaseWithin shear₃ B (Stage2Wrapper.top prime r v) (Stage2Wrapper.top prime r v)
      (Stage2Wrapper.Moves prime (Stage2Wrapper.top prime r v) (Stage2Wrapper.shear (prime ^ w) n fun h d => h - d)) c₆ H)
    (h₇ : PhaseWithin toLow B (Stage2Wrapper.top prime r v) (Stage2Wrapper.low prime r v) Eq c₇ H)
    (h₈ : PhaseWithin leaf B (Stage2Wrapper.low prime r v) (Stage2Wrapper.low prime r v) (Stage2Wrapper.Moves prime (Stage2Wrapper.low prime r v) Prod.swap) c₈ H)
    (h₉ : PhaseWithin back B (Stage2Wrapper.low prime r v) v Eq c₉ H) :
    PhaseWithin (core toTop shear₁ fam₁ shear₂ fam₂ shear₃ toLow leaf back) B v v (Stage2Wrapper.Moves prime v Prod.swap)
      (c₁ + 1 + c₂ + 1 + c₃ + 1 + c₄ + 1 + c₅ + 1 + c₆ + 1 + c₇ + 1 + c₈ + 1 + c₉) H := by
  have hchain := ((((((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆).seq h₇).seq h₈).seq h₉)
  have htime := core_hoare hr hw h₁.time h₂.time h₃.time h₄.time h₅.time h₆.time h₇.time h₈.time h₉.time
  intro X
  apply HoareWithin.of_time_invariant (htime X)
  intro z hz
  exact (hchain X).invariant hz

theorem transpose_within {s c : ℕ} {M : Program t s prime}
    {B : Descriptor → (ℕ → ZMod 2) → Tapes t prime} {v : Descriptor} {H : TapePred t prime}
    (hB : Local B) (h : PhaseWithin M B v v (Stage2Wrapper.Moves prime v Prod.swap) c H)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareWithin M (· = B v (FamilyRoot.ext x))
      (· = B v (FamilyRoot.ext (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))) c H := by
  apply HoareWithin.of_time_invariant (transpose_hoare hB h.time x)
  intro z hz
  exact (h (FamilyRoot.ext x)).invariant hz

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Core
