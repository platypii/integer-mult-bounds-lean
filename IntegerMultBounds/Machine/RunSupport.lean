import IntegerMultBounds.Machine.Hoare

/-! Concrete visited-interval bounds from the literal transition semantics.
A run cannot change a cell farther from its original head than its transition
count; initially blank work tapes therefore have explicitly bounded support. -/
namespace IntegerMultBounds.Machine.RunSupport
variable {t q a : ℕ}

private theorem step_local (M : Program t q a) (c d : Config t q a)
    (h : step M c = some d) (i : Fin t) :
    c.head i-1 ≤ d.head i ∧ d.head i ≤ c.head i+1 ∧
      ∀ z, z ≠ c.head i → d.tape i z = c.tape i z := by
  unfold step at h
  cases he : M.transition c.state (fun i => c.tape i (c.head i)) with
  | none => simp only [he] at h; cases h
  | some act =>
    simp only [he,Option.some.injEq] at h
    subst d
    have hm := Move.unit (act.2 i).2
    refine ⟨by dsimp; omega,by dsimp; omega,?_⟩
    intro z hz
    exact ite_eq_right hz

/-- Head displacement and the entire unvisited exterior are bounded directly
by the number of actual transitions, regardless of tape contents. -/
theorem run_local (M : Program t q a) (n : ℕ) (c d : Config t q a)
    (h : run M n c = some d) (i : Fin t) :
    c.head i-n ≤ d.head i ∧ d.head i ≤ c.head i+n ∧
      ∀ z, z < c.head i-n ∨ c.head i+n < z → d.tape i z = c.tape i z := by
  induction n generalizing c with
  | zero =>
    have he : c = d := Option.some.inj h
    subst c
    exact ⟨by omega,by omega,by intros; rfl⟩
  | succ n ih =>
    change (step M c >>= run M n) = some d at h
    cases hs : step M c with
    | none => simp only [hs] at h; cases h
    | some e =>
      simp only [hs] at h
      obtain ⟨hslo,hshi,hsframe⟩ := step_local M c e hs i
      obtain ⟨hrlo,hrhi,hrframe⟩ := ih e h
      refine ⟨by omega,by omega,?_⟩
      intro z hz
      rw [hrframe z (by omega)]
      exact hsframe z (by omega)

/-- Exact-bank Hoare contracts inherit finite support, using their verified
runtime as a bound rather than an assumed workspace oracle. -/
theorem hoare_blank (M : Program t q a) (v w : Tapes t a) (bound : ℕ)
    (h : HoareTime M (fun x => x = v) (fun x => x = w) bound)
    (i : Fin t) (hh : v.head i = 0) (ht : v.tape i = fun _ => blank) :
    -(bound : ℤ) ≤ w.head i ∧ w.head i ≤ bound ∧
      ∀ z, z < -(bound : ℤ) ∨ (bound : ℤ) < z → w.tape i z = blank := by
  obtain ⟨n,c,hn,hr,_,hw⟩ := h v rfl
  have hc := run_local M n (v.start M) c hr i
  have hh' : c.head i = w.head i := congrFun (congrArg Tapes.head hw) i
  have ht' : c.tape i = w.tape i := congrFun (congrArg Tapes.tape hw) i
  simp only [Tapes.start,hh] at hc
  rw [hh',ht'] at hc
  refine ⟨by omega,by omega,?_⟩
  intro z hz
  rw [hc.2.2 z (by omega),ht]

end IntegerMultBounds.Machine.RunSupport
