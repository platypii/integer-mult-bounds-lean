module

public import IntegerMultBounds.Machine.BinaryDescriptorCompare
public import IntegerMultBounds.Machine.CompositionInvariant
public import IntegerMultBounds.Machine.DescriptorStackBounds

/-! Workspace invariant for the actual descriptor reset: scan to the unique
origin marker, then take the paid right step. Complete tapes are retained. -/
@[expose] public section
namespace IntegerMultBounds.Machine.BinaryDescriptorCompare
open DescriptorStackControl
variable {q : ℕ}

def ResetScan (focus : Fin 3) (v : Tapes 3 q) (c : Config 3 1 q) : Prop :=
  c.tape = v.tape ∧ (0 ≤ c.head focus ∧ c.head focus ≤ v.head focus) ∧
    ∀ i, i ≠ focus → c.head i = v.head i

def ResetMove (focus : Fin 3) (v : Tapes 3 q) (c : Config 3 2 q) : Prop :=
  c.tape = v.tape ∧ c.head focus = (if c.state = 0 then 0 else 1) ∧
    ∀ i, i ≠ focus → c.head i = v.head i

def ResetInvariant (focus : Fin 3) (v : Tapes 3 q) :=
  SeqInvariant (ResetScan focus v) (ResetMove focus v)

private theorem scan_step (focus : Fin 3) (v : Tapes 3 q)
    (horigin : v.tape focus 0 = separator) {c d : Config 3 1 q}
    (h : ResetScan focus v c) (hs : Machine.step (seek focus separator .left) c = some d) :
    ResetScan focus v d := by
  have hn : c.tape focus (c.head focus) ≠ separator := by
    intro he; simp [Machine.step,seek,he] at hs
  have hp : 0 < c.head focus := by
    have hz := h.2.1.1
    have hh : c.head focus ≠ 0 := by intro he; apply hn; rw [h.1,he]; exact horigin
    omega
  simp only [Machine.step,seek,ite_eq_right hn,Option.some.injEq] at hs
  subst d
  refine ⟨?_,?_,?_⟩
  · change (fun i z => if z = c.head i then c.tape i (c.head i) else c.tape i z) = v.tape
    rw [←h.1]
    funext i z; split_ifs with he
    · rw [he]
    · rfl
  · simpa only [ite_true,Move.offset] using
      (show 0 ≤ c.head focus+(-1) ∧ c.head focus+(-1) ≤ v.head focus by have := h.2.1; omega)
  · intro i hi
    simpa only [ite_eq_right hi,Move.offset,add_zero] using h.2.2 i hi

private theorem move_step (focus : Fin 3) (v : Tapes 3 q) {c d : Config 3 2 q}
    (h : ResetMove focus v c) (hs : Machine.step (moveProgram focus .right) c = some d) :
    ResetMove focus v d := by
  have hz : c.state = 0 := by
    by_contra hn; simp [Machine.step,moveProgram,once,hn] at hs
  simp only [Machine.step,moveProgram,once,ite_eq_left hz,Option.some.injEq] at hs
  subst d
  refine ⟨?_,?_,?_⟩
  · change (fun i z => if z = c.head i then c.tape i (c.head i) else c.tape i z) = v.tape
    rw [←h.1]
    funext i z; split_ifs with he
    · rw [he]
    · rfl
  · have hh := h.2.1
    simpa [hz,Move.offset] using congrArg (fun z : ℤ => z+1) hh
  · intro i hi
    simpa only [ite_eq_right hi,Move.offset,add_zero] using h.2.2 i hi

/-- The origin marker is the only marker in the nonnegative scan interval. -/
theorem ResetInvariant.step (focus : Fin 3) (v : Tapes 3 q)
    (horigin : v.tape focus 0 = separator)
    (hunique : ∀ z, 0 ≤ z → v.tape focus z = separator → z = 0)
    {c d : Config 3 3 q} (hc : ResetInvariant focus v c)
    (hs : Machine.step (reset focus) c = some d) : ResetInvariant focus v d := by
  apply SeqInvariant.step (fun _ _ h hs => scan_step focus v horigin h hs)
    (fun _ _ h hs => move_step focus v h hs) ?_ hc hs
  intro x hx hh
  have hmark : x.tape focus (x.head focus) = separator := by
    by_contra hn; simp [Machine.step,seek,hn] at hh
  have hz := hunique (x.head focus) hx.2.1.1 (by rw [←hx.1]; exact hmark)
  exact ⟨hx.1,by simpa only [Config.tapes,Tapes.start,moveProgram,once,ite_true] using hz,hx.2.2⟩

theorem ResetInvariant.initial (focus : Fin 3) (v : Tapes 3 q) (hp : 0 ≤ v.head focus) :
    ResetInvariant focus v (v.start (reset focus)) :=
  Or.inl ⟨v.start (seek focus separator .left),⟨rfl,⟨hp,le_rfl⟩,fun _ _ => rfl⟩,rfl⟩

theorem ResetInvariant.heads (focus : Fin 3) (v : Tapes 3 q) {c : Config 3 3 q}
    (hc : ResetInvariant focus v c) :
    ∀ i, (if i = focus then 0 else v.head i) ≤ c.head i ∧
      c.head i ≤ (if i = focus then max 1 (v.head i) else v.head i) := by
  intro i
  rcases hc with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
  · by_cases hi : i = focus
    · subst i; simpa only [ite_true,Config.mapState] using
        ⟨hx.2.1.1,hx.2.1.2.trans (le_max_right _ _)⟩
    · simp only [Config.mapState,ite_eq_right hi,hx.2.2 i hi,le_refl,and_self]
  · by_cases hi : i = focus
    · subst i
      simp only [Config.mapState,ite_true,hx.2.1]
      split_ifs <;> constructor <;> omega
    · simp only [Config.mapState,ite_eq_right hi,hx.2.2 i hi,le_refl,and_self]

/-- The encoding supplies the reset's marker hypothesis, including empty words. -/
theorem descriptor_marker_iff (xs : List Bool) (z : ℤ) (hz : 0 ≤ z) :
    BinaryDescriptorStack.descriptor (a := q) xs z = separator ↔ z = 0 := by
  by_cases he : z = 0
  · subst z
    rw [BinaryDescriptorStack.descriptor,putWord_outside _ _ _ _ (Or.inl (by omega))]
    simp [BinaryDescriptorStack.empty]
  · have hp : 0 < z := by omega
    have hn : BinaryDescriptorStack.descriptor (a := q) xs z ≠ separator := by
      by_cases hi : z < 1+xs.length
      · have hb : (z-1).toNat < (xs.map (bitSymbol (a := q))).length := by simp only [List.length_map]; omega
        have hv := WordSegments.get BinaryDescriptorStack.empty 1 (xs.map (bitSymbol (a := q))) (z-1).toNat hb
        have hpos : (1 : ℤ)+(z-1).toNat = z := by omega
        rw [hpos] at hv
        change putWord BinaryDescriptorStack.empty 1 (xs.map bitSymbol) z ≠ separator
        rw [hv,List.getElem_map]
        cases xs[(z-1).toNat] <;> simp [bitSymbol,separator,Fin.ext_iff]
      · rw [BinaryDescriptorStack.descriptor,putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map]; omega))]
        simp [BinaryDescriptorStack.empty,he,blank,separator,Fin.ext_iff]
    simp [hn,he]

theorem ResetInvariant.descriptor_step (focus : Fin 3) (v : Tapes 3 q) (xs : List Bool)
    (ht : v.tape focus = BinaryDescriptorStack.descriptor xs)
    {c d : Config 3 3 q} (hc : ResetInvariant focus v c)
    (hs : Machine.step (reset focus) c = some d) : ResetInvariant focus v d :=
  hc.step focus v (by rw [ht]; exact (descriptor_marker_iff xs 0 (by omega)).mpr rfl)
    (by intro z hz hm; rw [ht] at hm; exact (descriptor_marker_iff xs z hz).mp hm) hs

/-- All prefixes of the concrete encoded reset stay within its fixed interval. -/
theorem ResetInvariant.descriptor_run (focus : Fin 3) (v : Tapes 3 q) (xs : List Bool)
    (ht : v.tape focus = BinaryDescriptorStack.descriptor xs)
    {c d : Config 3 3 q} (hc : ResetInvariant focus v c) {k : ℕ}
    (hrun : Machine.run (reset focus) k c = some d) : ResetInvariant focus v d := by
  induction k generalizing c with
  | zero =>
    simp only [Machine.run,Option.some.injEq] at hrun
    subst d; exact hc
  | succ k ih =>
    simp only [Machine.run] at hrun
    cases hs : Machine.step (reset focus) c with
    | none => simp [hs] at hrun
    | some e =>
      rw [hs,Option.bind_some] at hrun
      exact ih (hc.descriptor_step focus v xs ht hs) hrun

end IntegerMultBounds.Machine.BinaryDescriptorCompare
