import IntegerMultBounds.Machine.EqualWordReplace
import IntegerMultBounds.Machine.InjectivePlacement

/-! Fixed-slot word replacement and physical erasure on an arbitrary bank.
All complementary tape contents and all heads are retained exactly. -/
namespace IntegerMultBounds.Machine.WordBankCleanup
noncomputable section
variable {a t : ℕ}

def write (v : Tapes t a) (k : Fin t) (f : ℤ → Fin (a+4)) : Tapes t a :=
  ⟨v.head, Function.update v.tape k f⟩

def pairSlot (src dst : Fin t) : Fin 2 → Fin t := ![src,dst]
theorem pair_injective (src dst : Fin t) (hne : src ≠ dst) :
    Function.Injective (pairSlot src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [pairSlot]
def pairPlace (src dst : Fin t) (hne : src ≠ dst) (ht : 2 ≤ t) : Fin (2+(t-2)) ≃ Fin t :=
  InjectivePlacement.placement (pairSlot src dst) (pair_injective src dst hne) (by omega)

theorem pair_active (v : Tapes t a) (src dst : Fin t) (hne : src ≠ dst) (ht : 2 ≤ t) :
    Placement.active (pairPlace src dst hne ht) v =
      (CopyWord.cfg (v.tape src) (v.tape dst) (v.head src) (v.head dst)).tapes := by
  rw [pairPlace, InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem pair_replace (v : Tapes t a) (src dst : Fin t) (hne : src ≠ dst) (ht : 2 ≤ t)
    (f : ℤ → Fin (a+4)) :
    Placement.replace (pairPlace src dst hne ht) v
      (CopyWord.cfg (v.tape src) f (v.head src) (v.head dst)).tapes = write v dst f := by
  let e := pairPlace src dst hne ht
  have he (i : Fin 2) : e (Fin.castAdd (t-2) i) = pairSlot src dst i :=
    InjectivePlacement.active_slot _ _ _ i
  change Placement.replace e v _ = write v dst f
  apply congrArg₂ Tapes.mk
  · funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine e _ _).head (e (Fin.castAdd (t-2) i)) = _
      rw [Placement.combine_head_active]
      fin_cases i <;> simp [he,CopyWord.cfg,Config.tapes,pairSlot]
    | right i =>
      change (Placement.combine e _ _).head (e (Fin.natAdd 2 i)) = _
      rw [Placement.combine_head_extra]
      rfl
  · funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine e _ _).tape (e (Fin.castAdd (t-2) i)) = _
      rw [Placement.combine_tape_active]
      fin_cases i <;> simp [he,CopyWord.cfg,Config.tapes,pairSlot,hne]
    | right i =>
      have hneq : e (Fin.natAdd 2 i) ≠ dst := by
        rw [← show e (Fin.castAdd (t-2) (1 : Fin 2)) = dst by simpa [pairSlot] using he 1]
        intro h
        have hh := congrArg Fin.val (e.injective h)
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
        omega
      change (Placement.combine e _ _).tape (e (Fin.natAdd 2 i)) = _
      rw [Placement.combine_tape_extra]
      simp [Placement.extra,hneq]

def replaceProgram (src dst : Fin t) (hne : src ≠ dst) (ht : 2 ≤ t) (a : ℕ) :=
  Placement.placed (EqualWordReplace.program a) (pairPlace src dst hne ht)

theorem replace_hoare (v : Tapes t a) (src dst : Fin t) (hne : src ≠ dst) (ht : 2 ≤ t)
    (f g : ℤ → Fin (a+4)) (xs ys : List (Fin (a+4))) (hlen : xs.length = ys.length)
    (hs : v.tape src = putWord f (v.head src) xs)
    (hd : v.tape dst = putWord g (v.head dst) ys)
    (hx : ∀ x ∈ xs, x ≠ blank) (hf : f (v.head src-1) = blank)
    (hf' : f (v.head src+xs.length) = blank) (hg : g (v.head dst-1) = blank) :
    HoareTime (replaceProgram src dst hne ht a) (fun w => w = v)
      (fun w => w = write v dst (putWord g (v.head dst) xs)) (3*xs.length+6) := by
  have h := Placement.hoare_at
    (EqualWordReplace.replace_hoare f g (v.head src) (v.head dst) xs ys hlen hx hf hf' hg)
    (pairPlace src dst hne ht) v (by rw [pair_active,hs,hd])
  refine h.consequence (fun _ h => h) ?_ (le_refl _)
  rintro w ⟨small,rfl,rfl⟩
  rw [← hs,pair_replace]

/-- Scan to the real word end and erase backwards, with fixed finite control. -/
def eraseProgram (a : ℕ) : Program 1 4 a := seq ScanEnd.program EraseBack.program

theorem erase_hoare (p : ℤ) (xs : List (Fin (a+4))) (hx : ∀ x ∈ xs, x ≠ blank) :
    HoareTime (eraseProgram a)
      (fun v => v = (ScanEnd.cfg (putWord (fun _ => blank) p xs) p).tapes)
      (fun v => v = (ScanEnd.cfg (fun _ => blank) p).tapes) (2*xs.length+3) := by
  have h1 := ScanEnd.scan_hoare (fun _ => blank) p xs hx rfl
  have h2 := EraseBack.erase_hoare (fun _ => blank) p xs hx rfl (by intros; rfl)
  exact (h1.seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

def singleSlot (k : Fin t) : Fin 1 → Fin t := fun _ => k
theorem single_injective (k : Fin t) : Function.Injective (singleSlot k) :=
  fun _ _ _ => Subsingleton.elim _ _
def singlePlace (k : Fin t) (ht : 1 ≤ t) : Fin (1+(t-1)) ≃ Fin t :=
  InjectivePlacement.placement (singleSlot k) (single_injective k) (by omega)

theorem single_active (v : Tapes t a) (k : Fin t) (ht : 1 ≤ t) :
    Placement.active (singlePlace k ht) v = (ScanEnd.cfg (v.tape k) (v.head k)).tapes := by
  rw [singlePlace,InjectivePlacement.active_bank]
  rfl

private theorem single_replace (v : Tapes t a) (k : Fin t) (ht : 1 ≤ t)
    (f : ℤ → Fin (a+4)) :
    Placement.replace (singlePlace k ht) v (ScanEnd.cfg f (v.head k)).tapes = write v k f := by
  let e := singlePlace k ht
  have he (i : Fin 1) : e (Fin.castAdd (t-1) i) = k :=
    InjectivePlacement.active_slot _ _ _ i
  change Placement.replace e v _ = write v k f
  apply congrArg₂ Tapes.mk
  · funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine e _ _).head (e (Fin.castAdd (t-1) i)) = _
      rw [Placement.combine_head_active]
      simp [he,ScanEnd.cfg,Config.tapes]
    | right i =>
      change (Placement.combine e _ _).head (e (Fin.natAdd 1 i)) = _
      rw [Placement.combine_head_extra]
      rfl
  · funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    induction i using Fin.addCases with
    | left i =>
      change (Placement.combine e _ _).tape (e (Fin.castAdd (t-1) i)) = _
      rw [Placement.combine_tape_active]
      simp [he,ScanEnd.cfg,Config.tapes]
    | right i =>
      have hneq : e (Fin.natAdd 1 i) ≠ k := by
        rw [← he 0]
        intro h
        have hh := congrArg Fin.val (e.injective h)
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
        omega
      change (Placement.combine e _ _).tape (e (Fin.natAdd 1 i)) = _
      rw [Placement.combine_tape_extra]
      simp [Placement.extra,hneq]

def clearProgram (k : Fin t) (ht : 1 ≤ t) (a : ℕ) :=
  Placement.placed (eraseProgram a) (singlePlace k ht)

theorem clear_hoare (v : Tapes t a) (k : Fin t) (ht : 1 ≤ t)
    (xs : List (Fin (a+4))) (hx : ∀ x ∈ xs, x ≠ blank)
    (hk : v.tape k = putWord (fun _ => blank) (v.head k) xs) :
    HoareTime (clearProgram k ht a) (fun w => w = v)
      (fun w => w = write v k (fun _ => blank)) (2*xs.length+3) := by
  have h := Placement.hoare_at (erase_hoare (v.head k) xs hx) (singlePlace k ht) v
    (by rw [single_active,hk])
  refine h.consequence (fun _ h => h) ?_ (le_refl _)
  rintro w ⟨small,rfl,rfl⟩
  rw [single_replace]


end
end IntegerMultBounds.Machine.WordBankCleanup
