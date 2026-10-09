import IntegerMultBounds.Machine.CountedPackedLateRun
import IntegerMultBounds.Machine.PlacementBank

/-! Reusable early and late gadgets placed in arbitrary fixed injective tape
slots. Their literal word update, clean active workspace, original descriptor
retention, and the complete complementary frame are all tracked together. -/
namespace IntegerMultBounds.Machine.CountedPackedLatePlacement
noncomputable section
variable {a t s u : ℕ}
open WordBankCleanup (write)

/-- A literal one-tape update, the exact active output bank, and the retained
complete complementary frame, including every head. -/
def FramedResult (e : Fin (s+u) ≃ Fin t) (caller : Tapes t a) (i : Fin s)
    (f : ℤ → Fin (a+4)) (active : Tapes s a) (output : Tapes t a) : Prop :=
  output = write caller (e (Fin.castAdd u i)) f ∧
    Placement.active e output = active ∧ Placement.extra e output = Placement.extra e caller

theorem replace_write (e : Fin (s+u) ≃ Fin t) (caller : Tapes t a) (i : Fin s)
    (f : ℤ → Fin (a+4)) :
    Placement.replace e caller (write (Placement.active e caller) i f) =
      write caller (e (Fin.castAdd u i)) f := by
  apply Placement.Tapes.ext'
  · intro j
    obtain ⟨k,rfl⟩ := e.surjective j
    induction k using Fin.addCases with
    | left k =>
      rw [Placement.replace_head_active]
      rfl
    | right k =>
      change (Placement.combine e _ _).head (e (Fin.natAdd s k)) = _
      rw [Placement.combine_head_extra]
      rfl
  · intro j
    obtain ⟨k,rfl⟩ := e.surjective j
    induction k using Fin.addCases with
    | left k =>
      rw [Placement.replace_tape_active]
      change Function.update (Placement.active e caller).tape i f k =
        Function.update caller.tape (e (Fin.castAdd u i)) f (e (Fin.castAdd u k))
      by_cases hk : k = i
      · subst k; simp
      · rw [Function.update_of_ne hk,Function.update_of_ne]
        · rfl
        · intro he
          exact hk (Fin.castAdd_injective _ _ (e.injective he))
    | right k =>
      change (Placement.combine e _ _).tape (e (Fin.natAdd s k)) = _
      rw [Placement.combine_tape_extra]
      change caller.tape (e (Fin.natAdd s k)) =
        Function.update caller.tape (e (Fin.castAdd u i)) f (e (Fin.natAdd s k))
      rw [Function.update_of_ne]
      intro he
      have hh := congrArg Fin.val (e.injective he)
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
      have := i.isLt
      omega

private theorem lift_hoare {m c : ℕ} {M : Program s m a}
    (e : Fin (s+u) ≃ Fin t) (caller : Tapes t a) (X Y : Tapes s a) (i : Fin s)
    (f : ℤ → Fin (a+4))
    (h : HoareTime M (fun v => v = X) (fun v => v = Y) c)
    (ha : Placement.active e caller = X) (hy : Y = write X i f) :
    HoareTime (Placement.placed M e) (fun v => v = caller)
      (FramedResult e caller i f Y) c := by
  have hp := Placement.hoare_at h e caller ha
  refine hp.consequence (fun _ h => h) ?_ (le_refl _)
  rintro output ⟨small,rfl,rfl⟩
  refine ⟨?_,Placement.active_replace _ _ _,Placement.extra_replace _ _ _⟩
  rw [hy,← ha,replace_write]

/-- Outside the updated original word, every whole tape is retained; every
head is retained, including the updated word's head. -/
theorem framed_retains (caller output : Tapes t a)
    (j : Fin t) (f : ℤ → Fin (a+4)) (hout : output = write caller j f) :
    output.head = caller.head ∧ ∀ k, k ≠ j → output.tape k = caller.tape k := by
  subst output
  exact ⟨rfl,fun k hk => Function.update_of_ne hk _ _⟩

def earlyPlace (focus : Fin 26 → Fin t) (hi : Function.Injective focus) : Fin (26+(t-26)) ≃ Fin t :=
  InjectivePlacement.placement focus hi (by
    have h := Fintype.card_le_of_injective focus hi
    simp only [Fintype.card_fin] at h
    omega)
def latePlace (focus : Fin 28 → Fin t) (hi : Function.Injective focus) : Fin (28+(t-28)) ≃ Fin t :=
  InjectivePlacement.placement focus hi (by
    have h := Fintype.card_le_of_injective focus hi
    simp only [Fintype.card_fin] at h
    omega)
def earlyProgram (focus : Fin 26 → Fin t) (hi : Function.Injective focus) (a : ℕ) :=
  Placement.placed (CountedPackedReusable.forwardProgram a) (earlyPlace focus hi)
def lateProgram (focus : Fin 28 → Fin t) (hi : Function.Injective focus) (a : ℕ) :=
  Placement.placed (CountedPackedLateRun.program a) (latePlace focus hi)

theorem early_update (V W Z T : List Bool) (f g z : ℤ → Fin (a+4))
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) (hs : Fin 3 → List Bool) :
    CountedPackedArith.bank (PackedArith.input T W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs =
      write (CountedPackedArith.bank (PackedArith.input V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
        0 (putWord f p0 (T.map bitSymbol)) := by
  unfold CountedPackedArith.bank CountedPackedArith.tail PackedArith.input PackedArith.bank write Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem late_update (V W U X T : List Bool) (f g h k : ℤ → Fin (a+4))
    (pv pw pu px : ℤ) (hs : Fin 3 → List Bool) :
    CountedPackedLateRun.bank T W U X [] f g h k pv pw pu px hs =
      write (CountedPackedLateRun.bank V W U X [] f g h k pv pw pu px hs)
        0 (putWord f pv (T.map bitSymbol)) := by
  unfold CountedPackedLateRun.bank CountedPackedLateRun.payload write Tapes.append
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Exact guarded early semantics in an arbitrary larger caller bank. The
active output explicitly retains descriptors and returns every private tape blank. -/
theorem early_hoare (focus : Fin 26 → Fin t) (hi : Function.Injective focus) (caller : Tapes t a)
    (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (V W Z : List Bool) (f g z : ℤ → Fin (a+4))
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 : ℤ) (hs : Fin 3 → List Bool)
    (ha : Placement.active (earlyPlace focus hi) caller = CountedPackedArith.bank
      (PackedArith.input V W Z f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b)
    (hf : f (p0-1) = blank) (hf' : f (p0+V.length) = blank)
    (hg : g (p1-1) = blank) (hg' : g (p1+W.length) = blank) (hz : z (p2-1) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hgood : ∀ d ∈ CountedPackedGuarded.states q b V W Z,
      d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    HoareTime (earlyProgram focus hi a) (fun v => v = caller)
      (fun v => v = write caller (focus 0)
          (putWord f p0 ((List.zipWith xor V (Compact.PowerTwo.toggleMask q Z)).map bitSymbol)) ∧
        Placement.active (earlyPlace focus hi) v = CountedPackedArith.bank
          (PackedArith.input (List.zipWith xor V (Compact.PowerTwo.toggleMask q Z)) W Z
            f g z p0 p1 p2 p3 p4 p5 p6 p7 p8) hs ∧
        Placement.extra (earlyPlace focus hi) v = Placement.extra (earlyPlace focus hi) caller)
      (2720*((Z.length+1)*(q+b+1))) := by
  have hr := CountedPackedGuarded.guarded_reusable_hoare q b hb hbq V W Z f g z
    p0 p1 p2 p3 p4 p5 p6 p7 p8 hs hV hW hf hf' hg hg' hz hv hc hgood
  have hp := lift_hoare (earlyPlace focus hi) caller _ _ 0 _ hr ha
    (early_update V W Z (List.zipWith xor V (Compact.PowerTwo.toggleMask q Z)) f g z
      p0 p1 p2 p3 p4 p5 p6 p7 p8 hs)
  refine hp.consequence (fun _ h => h) ?_ (le_refl _)
  intro v hv
  rcases hv with ⟨hwrite,hactive,hframe⟩
  have hslot : earlyPlace focus hi (Fin.castAdd (t-26) (0 : Fin 26)) = focus 0 :=
    InjectivePlacement.active_slot _ _ _ _
  rw [hslot] at hwrite
  exact ⟨hwrite,hactive,hframe⟩

/-- Exact guarded late semantics in an arbitrary larger caller bank. The
control and both dirty words are restored, with full private and frame retention. -/
theorem late_hoare (focus : Fin 28 → Fin t) (hi : Function.Injective focus) (caller : Tapes t a)
    (q b : ℕ) (hb : 1 ≤ b) (hbq : b+1 ≤ q) (V W U X : List Bool) (f g h k : ℤ → Fin (a+4))
    (pv pw pu px : ℤ) (hs : Fin 3 → List Bool)
    (ha : Placement.active (latePlace focus hi) caller =
      CountedPackedLateRun.bank V W U X [] f g h k pv pw pu px hs)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hf : f (pv-1) = blank) (hf' : f (pv+V.length) = blank)
    (hg : g (pw-1) = blank) (hg' : g (pw+W.length) = blank)
    (hh : h (pu-1) = blank) (hh' : h (pu+U.length) = blank)
    (hk : k (px-1) = blank) (hk' : k (px+X.length) = blank)
    (hv : ∀ i, Counter.value (hs i) = CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hgood : ∀ d ∈ CountedPackedLateData.states q b V W U X,
      d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    HoareTime (lateProgram focus hi a) (fun v => v = caller)
      (fun v => v = write caller (focus 0)
          (putWord f pv ((List.zipWith xor V (Compact.PowerTwo.toggleMask q X)).map bitSymbol)) ∧
        Placement.active (latePlace focus hi) v = CountedPackedLateRun.bank
          (List.zipWith xor V (Compact.PowerTwo.toggleMask q X)) W U X [] f g h k pv pw pu px hs ∧
        Placement.extra (latePlace focus hi) v = Placement.extra (latePlace focus hi) caller)
      (7000*((X.length+1)*(q+b+1))) := by
  have hr := CountedPackedLateRun.runs_guarded q b hb hbq V W U X f g h k pv pw pu px hs
    hv hc hV hW hU hf hf' hg hg' hh hh' hk hk' hgood
  have hp := lift_hoare (latePlace focus hi) caller _ _ 0 _ hr ha
    (late_update V W U X (List.zipWith xor V (Compact.PowerTwo.toggleMask q X)) f g h k pv pw pu px hs)
  refine hp.consequence (fun _ h => h) ?_ (le_refl _)
  intro v hv
  rcases hv with ⟨hwrite,hactive,hframe⟩
  have hslot : latePlace focus hi (Fin.castAdd (t-28) (0 : Fin 28)) = focus 0 :=
    InjectivePlacement.active_slot _ _ _ _
  rw [hslot] at hwrite
  exact ⟨hwrite,hactive,hframe⟩

end
end IntegerMultBounds.Machine.CountedPackedLatePlacement
