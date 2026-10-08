import IntegerMultBounds.Machine.Placement

/-! Static composition of independent tape-bank placements. These equivalences
wire finite transition tables; they do not perform or assume payload transfers. -/
namespace IntegerMultBounds.Machine.FamilyPlacement

/-- Pair two active banks and their separate frames. -/
def pair {s u t r v q : ℕ} (e : Fin (s+u) ≃ Fin t) (f : Fin (r+v) ≃ Fin q) :
    Fin ((s+r)+(u+v)) ≃ Fin (t+q) where
  toFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd q (e (Fin.castAdd u i)))
      (fun i => Fin.natAdd t (f (Fin.castAdd v i))))
    (Fin.addCases (fun i => Fin.castAdd q (e (Fin.natAdd s i)))
      (fun i => Fin.natAdd t (f (Fin.natAdd r i))))
  invFun := Fin.addCases
    (fun i => Fin.addCases (fun j => Fin.castAdd (u+v) (Fin.castAdd r j))
      (fun j => Fin.natAdd (s+r) (Fin.castAdd v j)) (e.symm i))
    (fun i => Fin.addCases (fun j => Fin.castAdd (u+v) (Fin.natAdd s j))
      (fun j => Fin.natAdd (s+r) (Fin.natAdd u j)) (f.symm i))
  left_inv := by
    intro i
    induction i using Fin.addCases <;> rename_i i <;> induction i using Fin.addCases <;> simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      obtain ⟨j,rfl⟩ := e.surjective i
      induction j using Fin.addCases <;> simp
    | right i =>
      obtain ⟨j,rfl⟩ := f.surjective i
      induction j using Fin.addCases <;> simp

/-- Add an active frame on the right, retaining the original placement's extras. -/
def withFrame {s u t r : ℕ} (e : Fin (s+u) ≃ Fin t) :
    Fin ((s+r)+u) ≃ Fin (t+r) where
  toFun := Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd r (e (Fin.castAdd u i))) (Fin.natAdd t))
    (fun i => Fin.castAdd r (e (Fin.natAdd s i)))
  invFun := Fin.addCases
    (fun i => Fin.addCases (fun j => Fin.castAdd u (Fin.castAdd r j)) (Fin.natAdd (s+r)) (e.symm i))
    (fun i => Fin.castAdd u (Fin.natAdd s i))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      obtain ⟨j,rfl⟩ := e.surjective i
      induction j using Fin.addCases <;> simp
    | right i => simp

theorem active_pair {s u t r v q : ℕ} (e : Fin (s+u) ≃ Fin t) (f : Fin (r+v) ≃ Fin q)
    (x : Tapes t 0) (y : Tapes q 0) :
    Placement.active (pair e f) (x.append y) = (Placement.active e x).append (Placement.active f y) := by
  unfold Placement.active pair Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem extra_pair {s u t r v q : ℕ} (e : Fin (s+u) ≃ Fin t) (f : Fin (r+v) ≃ Fin q)
    (x : Tapes t 0) (y : Tapes q 0) :
    Placement.extra (pair e f) (x.append y) = (Placement.extra e x).append (Placement.extra f y) := by
  unfold Placement.extra pair Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem combine_pair {s u t r v q : ℕ} (e : Fin (s+u) ≃ Fin t) (f : Fin (r+v) ≃ Fin q)
    (x : Tapes s 0) (y : Tapes r 0) (a : Tapes u 0) (b : Tapes v 0) :
    Placement.combine (pair e f) (x.append y) (a.append b) =
      (Placement.combine e x a).append (Placement.combine f y b) := by
  simpa only [active_pair,extra_pair,Placement.active_combine,Placement.extra_combine] using
    Placement.view (pair e f) ((Placement.combine e x a).append (Placement.combine f y b))

theorem active_withFrame {s u t r : ℕ} (e : Fin (s+u) ≃ Fin t) (x : Tapes t 0) (y : Tapes r 0) :
    Placement.active (withFrame e) (x.append y) = (Placement.active e x).append y := by
  unfold Placement.active withFrame Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem extra_withFrame {s u t r : ℕ} (e : Fin (s+u) ≃ Fin t) (x : Tapes t 0) (y : Tapes r 0) :
    Placement.extra (withFrame e) (x.append y) = Placement.extra e x := by
  unfold Placement.extra withFrame Tapes.append
  congr 1 <;> funext i <;> simp

theorem combine_withFrame {s u t r : ℕ} (e : Fin (s+u) ≃ Fin t)
    (x : Tapes s 0) (y : Tapes r 0) (a : Tapes u 0) :
    Placement.combine (withFrame e) (x.append y) a = (Placement.combine e x a).append y := by
  simpa only [active_withFrame,extra_withFrame,Placement.active_combine,Placement.extra_combine] using
    Placement.view (withFrame e) ((Placement.combine e x a).append y)


/-- Exact-bank form of ordinary right framing. -/
theorem extend_hoare {s q r : ℕ} {M : Program s q 0} {v w : Tapes s 0} {cost : ℕ}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) (frame : Tapes r 0) :
    HoareTime (extend M r) (fun x => x = v.append frame) (fun x => x = w.append frame) cost := by
  apply (h.extend frame).consequence _ _ le_rfl
  · rintro x rfl; exact ⟨_,rfl,rfl⟩
  · rintro x ⟨y,rfl,rfl⟩; rfl

def sequence {s t q r : ℕ} (M : Program s q 0) (N : Program t r 0) : Program (s+t) (q+r) 0 :=
  seq (extend M t) (Placement.placed N (finAddFlip : Fin (t+s) ≃ Fin (s+t)))

/-- Execute two independent banks in sequence, charging the actual join. -/
theorem sequence_hoare {s t q r : ℕ} {M : Program s q 0} {N : Program t r 0}
    {v w : Tapes s 0} {x y : Tapes t 0} {a b : ℕ}
    (hM : HoareTime M (fun z => z = v) (fun z => z = w) a)
    (hN : HoareTime N (fun z => z = x) (fun z => z = y) b) :
    HoareTime (sequence M N) (fun z => z = v.append x) (fun z => z = w.append y) (a+b+1) := by
  let e : Fin (t+s) ≃ Fin (s+t) := finAddFlip
  have ha : Placement.active e (w.append x) = x := by
    cases x; simp [Placement.active,e,Tapes.append,finAddFlip_apply_castAdd]
  have hh := Placement.hoare_at hN e (w.append x) ha
  have hn : HoareTime (Placement.placed N e) (fun z => z = w.append x) (fun z => z = w.append y) b := by
    apply hh.consequence (fun _ h => h) _ le_rfl
    rintro z ⟨small,hsmall,rfl⟩
    subst small
    have he : Placement.extra e (w.append x) = w := by
      cases w; simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
    rw [Placement.replace,he]
    have ha' : Placement.active e (w.append y) = y := by
      cases y; simp [Placement.active,e,Tapes.append,finAddFlip_apply_castAdd]
    have he' : Placement.extra e (w.append y) = w := by
      cases w; simp [Placement.extra,e,Tapes.append,finAddFlip_apply_natAdd]
    simpa only [ha',he'] using Placement.view e (w.append y)
  exact ((extend_hoare hM x).seq hn).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.FamilyPlacement
