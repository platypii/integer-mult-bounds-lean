module

public import IntegerMultBounds.Machine.Branch
public import IntegerMultBounds.Machine.HoareWithin

/-! A physical one-step conditional preserves the branches' shared predicate. -/
@[expose] public section
namespace IntegerMultBounds.Machine.HoareWithin
variable {t q r a : ℕ}

theorem branch (test : (Fin t → Fin (a+4)) → Bool)
    {M : Program t q a} {N : Program t r a} {pre post H : TapePred t a} {bM bN : ℕ}
    (hM : HoareWithin M (fun v => pre v ∧ test v.reads = true) post bM H)
    (hN : HoareWithin N (fun v => pre v ∧ test v.reads = false) post bN H) :
    HoareWithin (Machine.branch test M N) pre post (max bM bN+1) H := by
  intro v hv
  cases h : test v.reads with
  | true =>
    obtain ⟨k,hk,c,hr,hh,hp⟩ := hM v ⟨hv,h⟩
    have henter : RunWithin (Machine.branch test M N) H 1 (v.start (Machine.branch test M N))
        ((v.start M).mapState (leftState q r)) :=
      RunWithin.single (branch_step_enter_true test M N v h) hr.initial hr.initial
    have hbody := hr.simulation (fun c => c.mapState (leftState q r))
      (N := Machine.branch test M N) (G := H)
      (by intro x y hs; rw [branch_step_left,hs]; rfl) (fun _ h => h)
    refine ⟨1+k,by omega,c.mapState (leftState q r),henter.trans hbody,?_,hp⟩
    rw [branch_step_left,hh]; rfl
  | false =>
    obtain ⟨k,hk,c,hr,hh,hp⟩ := hN v ⟨hv,h⟩
    have henter : RunWithin (Machine.branch test M N) H 1 (v.start (Machine.branch test M N))
        ((v.start N).mapState (rightState q r)) :=
      RunWithin.single (branch_step_enter_false test M N v h) hr.initial hr.initial
    have hbody := hr.simulation (fun c => c.mapState (rightState q r))
      (N := Machine.branch test M N) (G := H)
      (by intro x y hs; rw [branch_step_right,hs]; rfl) (fun _ h => h)
    refine ⟨1+k,by omega,c.mapState (rightState q r),henter.trans hbody,?_,hp⟩
    rw [branch_step_right,hh]; rfl

end IntegerMultBounds.Machine.HoareWithin
