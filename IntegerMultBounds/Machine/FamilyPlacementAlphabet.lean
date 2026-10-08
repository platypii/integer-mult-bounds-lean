import IntegerMultBounds.Machine.FamilyPlacement

/-! Alphabet-polymorphic tape-family wiring contracts. Each placement acts on
complete tapes, preserving every finite-alphabet symbol on framed banks. -/
namespace IntegerMultBounds.Machine.FamilyPlacementAlphabet
open FamilyPlacement (pair withFrame)
variable {alphabet : ℕ}

theorem active_pair {s u t r v q : ℕ} (e : Fin (s+u) ≃ Fin t) (f : Fin (r+v) ≃ Fin q)
    (x : Tapes t alphabet) (y : Tapes q alphabet) :
    Placement.active (pair e f) (x.append y) = (Placement.active e x).append (Placement.active f y) := by
  unfold Placement.active pair Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem extra_pair {s u t r v q : ℕ} (e : Fin (s+u) ≃ Fin t) (f : Fin (r+v) ≃ Fin q)
    (x : Tapes t alphabet) (y : Tapes q alphabet) :
    Placement.extra (pair e f) (x.append y) = (Placement.extra e x).append (Placement.extra f y) := by
  unfold Placement.extra pair Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem combine_pair {s u t r v q : ℕ} (e : Fin (s+u) ≃ Fin t) (f : Fin (r+v) ≃ Fin q)
    (x : Tapes s alphabet) (y : Tapes r alphabet) (a : Tapes u alphabet) (b : Tapes v alphabet) :
    Placement.combine (pair e f) (x.append y) (a.append b) =
      (Placement.combine e x a).append (Placement.combine f y b) := by
  simpa only [active_pair,extra_pair,Placement.active_combine,Placement.extra_combine] using
    Placement.view (pair e f) ((Placement.combine e x a).append (Placement.combine f y b))

theorem active_withFrame {s u t r : ℕ} (e : Fin (s+u) ≃ Fin t) (x : Tapes t alphabet) (y : Tapes r alphabet) :
    Placement.active (withFrame e) (x.append y) = (Placement.active e x).append y := by
  unfold Placement.active withFrame Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

theorem extra_withFrame {s u t r : ℕ} (e : Fin (s+u) ≃ Fin t) (x : Tapes t alphabet) (y : Tapes r alphabet) :
    Placement.extra (withFrame e) (x.append y) = Placement.extra e x := by
  unfold Placement.extra withFrame Tapes.append
  congr 1 <;> funext i <;> simp

theorem combine_withFrame {s u t r : ℕ} (e : Fin (s+u) ≃ Fin t)
    (x : Tapes s alphabet) (y : Tapes r alphabet) (a : Tapes u alphabet) :
    Placement.combine (withFrame e) (x.append y) a = (Placement.combine e x a).append y := by
  simpa only [active_withFrame,extra_withFrame,Placement.active_combine,Placement.extra_combine] using
    Placement.view (withFrame e) ((Placement.combine e x a).append y)


/-- Exact-bank form of ordinary right framing. -/
theorem extend_hoare {s q r : ℕ} {M : Program s q alphabet} {v w : Tapes s alphabet} {cost : ℕ}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost) (frame : Tapes r alphabet) :
    HoareTime (extend M r) (fun x => x = v.append frame) (fun x => x = w.append frame) cost := by
  apply (h.extend frame).consequence _ _ le_rfl
  · rintro x rfl; exact ⟨_,rfl,rfl⟩
  · rintro x ⟨y,rfl,rfl⟩; rfl

def sequence {s t q r : ℕ} (M : Program s q alphabet) (N : Program t r alphabet) : Program (s+t) (q+r) alphabet :=
  seq (extend M t) (Placement.placed N (finAddFlip : Fin (t+s) ≃ Fin (s+t)))

/-- Execute two independent banks in sequence, charging the actual join. -/
theorem sequence_hoare {s t q r : ℕ} {M : Program s q alphabet} {N : Program t r alphabet}
    {v w : Tapes s alphabet} {x y : Tapes t alphabet} {a b : ℕ}
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

end IntegerMultBounds.Machine.FamilyPlacementAlphabet
