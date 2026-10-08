import IntegerMultBounds.Machine.TrackedInit

/-! Initialized tracking for actual Hoare contracts. Only blank tracker tapes
are supplied; their marked intervals and finite support are physically built. -/
namespace IntegerMultBounds.Machine.TrackedHoare
variable {t s a : ℕ}

def bank (v : Tapes t a) (lo hi : Fin t → ℤ) : Tapes (t+t) a :=
  v.append ⟨v.head,fun i => TrackedCleanup.tracker (lo i) (hi i)⟩

def Intervals (v : Tapes t a) (lo hi : Fin t → ℤ) (B : ℕ) (work : Fin t → Prop) : Prop :=
  (∀ i, -(B : ℤ) ≤ lo i ∧ lo i ≤ 0 ∧ 0 ≤ hi i ∧ hi i ≤ B ∧ lo i ≤ v.head i ∧ v.head i ≤ hi i) ∧
  (∀ i, work i → ∀ z, z < lo i ∨ hi i < z → v.tape i z = blank)

theorem tracked_hoare (M : Program t s a) (right : Fin t → Bool) (v w : Tapes t a)
    (bound : ℕ) (work : Fin t → Prop)
    (hh : v.head = TrackedInit.position right) (hw : ∀ i, work i → v.tape i = fun _ => blank)
    (h : HoareTime M (fun x => x = v) (fun x => x = w) bound) :
    HoareTime (TrackedExecution.program M)
      (fun x => x = v.append (TrackedInit.trackers right))
      (fun x => ∃ lo hi, Intervals w lo hi (bound+1) work ∧ x = bank w lo hi) (2*bound) := by
  have hshape : TrackedExecution.Shape (v.start M) (fun _ => 0) (TrackedInit.position right) := by
    intro i
    simp only [Tapes.start,hh,TrackedInit.position]
    cases right i <;> simp
  have hsupport : TrackedExecution.Supported work (v.start M) (fun _ => 0) (TrackedInit.position right) := by
    intro i hi z _
    exact congrFun (hw i hi) z
  have hbounds : ∀ i, -(1 : ℤ) ≤ (0 : ℤ) ∧ TrackedInit.position right i ≤ 1 := by
    intro i
    simp only [TrackedInit.position]
    cases right i <;> simp
  intro x hx
  subst x
  obtain ⟨n,c,hn,hr,hhalt,hpost⟩ := h v rfl
  obtain ⟨lo,hi,hs,hs',hw',hb⟩ := TrackedExecution.run_tracked M n 1 (v.start M) c
    (fun _ => 0) (TrackedInit.position right) hshape work hsupport hbounds hr
  refine ⟨2*n,TrackedExecution.lift c lo hi,by omega,?_,TrackedExecution.halt M c lo hi hhalt,lo,hi,?_,?_⟩
  · rw [TrackedInit.start_lift M right v hh]
    exact hs
  · have hehead := congrArg Tapes.head hpost
    have hetape := congrArg Tapes.tape hpost
    constructor
    · intro i
      have hsi := hs' i
      have hbi := hb i
      have he := congrFun hehead i
      change c.head i = w.head i at he
      rw [he] at hsi
      exact ⟨by omega,hsi.1,hsi.2.1,by omega,hsi.2.2⟩
    · intro i hwi z hz
      have he := congrFun (congrFun hetape i) z
      change c.tape i z = w.tape i z at he
      rw [← he]
      exact hw' i hwi z hz
  · change bank c.tapes lo hi = bank w lo hi
    rw [hpost]

def program (M : Program t s a) (right : Fin t → Bool) : Program (t+t) (3+(s+s)) a :=
  seq (TrackedInit.program right M.tapes_pos) (TrackedExecution.program M)

/-- The complete simulation starts with only blank extra tapes and has constant
factor runtime overhead. The original final tapes are exact and untouched by
tracking; no runtime descriptor or prebuilt marked interval is assumed. -/
theorem initialized_hoare (M : Program t s a) (right : Fin t → Bool) (v w : Tapes t a)
    (bound : ℕ) (work : Fin t → Prop)
    (hh : v.head = TrackedInit.position right) (hw : ∀ i, work i → v.tape i = fun _ => blank)
    (h : HoareTime M (fun x => x = v) (fun x => x = w) bound) :
    HoareTime (program M right) (fun x => x = v.append (SharedBank.empty t a))
      (fun x => ∃ lo hi, Intervals w lo hi (bound+1) work ∧ x = bank w lo hi) (2*bound+3) := by
  exact ((TrackedInit.initialize_hoare right M.tapes_pos v).seq
    (tracked_hoare M right v w bound work hh hw h)).consequence
      (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.TrackedHoare
