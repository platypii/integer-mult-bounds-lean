import IntegerMultBounds.Machine.Placement

/-! Alphabet-polymorphic placement sharing one physical tape. -/
namespace IntegerMultBounds.Machine.SharedPlacementAlphabet
variable {a : ℕ}

/-- Replace a complete tape and its head, without moving any other tape. -/
def setTape {t : ℕ} (v : Tapes t a) (i : Fin t) (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes t a :=
  ⟨Function.update v.head i p,Function.update v.tape i f⟩

@[simp] theorem setTape_self {t : ℕ} (v : Tapes t a) (i : Fin t) :
    setTape v i (v.tape i) (v.head i) = v := by
  cases v
  simp [setTape]

@[simp] theorem setTape_setTape {t : ℕ} (v : Tapes t a) (i : Fin t)
    (f g : ℤ → Fin (a+4)) (p q : ℤ) : setTape (setTape v i f p) i g q = setTape v i g q := by
  simp [setTape,Function.update_idem]

theorem setTape_append_left {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin l)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.castAdd r i) f p = (setTape v i f p).append w := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; have hi := i.isLt; omega

/-- Run a right-hand bank while sharing its selected slot with a left-hand
payload slot. The right-hand bank's original slot becomes stationary frame. -/
def sharedPlacement {l r : ℕ} (i : Fin l) (j : Fin r) : Fin (r+l) ≃ Fin (l+r) :=
  (finAddFlip : Fin (r+l) ≃ Fin (l+r)).trans (Equiv.swap (Fin.castAdd r i) (Fin.natAdd l j))

private theorem cross_ne {l r : ℕ} (i : Fin l) (j : Fin r) :
    Fin.castAdd r i ≠ Fin.natAdd l j := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at he
  have hi := i.isLt
  omega

private theorem shared_active_index {l r : ℕ} (i : Fin l) (j k : Fin r) :
    sharedPlacement i j (Fin.castAdd l k) = if k = j then Fin.castAdd r i else Fin.natAdd l k := by
  simp only [sharedPlacement,Equiv.trans_apply,finAddFlip_apply_castAdd]
  by_cases hk : k = j
  · subst k; simp
  · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm (cross_ne i k)) (by simpa using hk)]
    simp [hk]

private theorem shared_extra_index {l r : ℕ} (i k : Fin l) (j : Fin r) :
    sharedPlacement i j (Fin.natAdd r k) = if k = i then Fin.natAdd l j else Fin.castAdd r k := by
  simp only [sharedPlacement,Equiv.trans_apply,finAddFlip_apply_natAdd]
  by_cases hk : k = i
  · subst k; simp
  · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hk) (cross_ne k j)]
    simp [hk]

theorem active_shared {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin l) (j : Fin r) :
    Placement.active (sharedPlacement i j) (v.append w) = setTape w j (v.tape i) (v.head i) := by
  unfold Placement.active setTape
  congr 1 <;> funext k <;> rw [shared_active_index] <;>
    by_cases hk : k = j <;> simp [hk,Tapes.append]

theorem extra_shared {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin l) (j : Fin r) :
    Placement.extra (sharedPlacement i j) (v.append w) = setTape v i (w.tape j) (w.head j) := by
  unfold Placement.extra setTape
  congr 1 <;> funext k <;> rw [shared_extra_index] <;>
    by_cases hk : k = i <;> simp [hk,Tapes.append]

theorem replace_shared {l r : ℕ} (v : Tapes l a) (w w' : Tapes r a) (i : Fin l) (j : Fin r) :
    Placement.replace (sharedPlacement i j) (v.append w) w' =
      (setTape v i (w'.tape j) (w'.head j)).append (setTape w' j (w.tape j) (w.head j)) := by
  rw [Placement.replace,extra_shared]
  have ha : Placement.active (sharedPlacement i j)
      ((setTape v i (w'.tape j) (w'.head j)).append (setTape w' j (w.tape j) (w.head j))) = w' := by
    rw [active_shared]
    simp [setTape]
  have he : Placement.extra (sharedPlacement i j)
      ((setTape v i (w'.tape j) (w'.head j)).append (setTape w' j (w.tape j) (w.head j))) =
        setTape v i (w.tape j) (w.head j) := by
    rw [extra_shared]
    simp [setTape]
  simpa only [ha,he] using Placement.view (sharedPlacement i j)
    ((setTape v i (w'.tape j) (w'.head j)).append (setTape w' j (w.tape j) (w.head j)))

/-- Hoare placement with one physically shared tape and an idle original slot. -/
theorem shared_hoare {l r states : ℕ} {M : Program r states a} {w w' : Tapes r a} {cost : ℕ}
    (h : HoareTime M (fun x => x = w) (fun x => x = w') cost)
    (v : Tapes l a) (i : Fin l) (j : Fin r) (spare : ℤ → Fin (a+4)) (spareHead : ℤ)
    (hf : v.tape i = w.tape j) (hp : v.head i = w.head j) :
    HoareTime (Placement.placed M (sharedPlacement i j))
      (fun x => x = v.append (setTape w j spare spareHead))
      (fun x => x = (setTape v i (w'.tape j) (w'.head j)).append (setTape w' j spare spareHead)) cost := by
  have ha : Placement.active (sharedPlacement i j) (v.append (setTape w j spare spareHead)) = w := by
    rw [active_shared,hf,hp,setTape_setTape,setTape_self]
  have hh := Placement.hoare_at h (sharedPlacement i j) _ ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [replace_shared]
  simp only [setTape,Function.update_self]


end IntegerMultBounds.Machine.SharedPlacementAlphabet
