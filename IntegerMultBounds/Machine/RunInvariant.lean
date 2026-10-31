module

public import IntegerMultBounds.Machine.HeadTravel

/-! Reachable configurations form a preserved invariant. Actual Hoare contracts
supply its halting boundary and, for linear-time components, head intervals. -/
@[expose] public section
namespace IntegerMultBounds.Machine
variable {t q a : ℕ}

theorem run_step_append {M : Program t q a} {c d z : Config t q a} {n : ℕ}
    (hr : run M n c = some d) (hs : step M d = some z) : run M (n+1) c = some z := by
  induction n generalizing c with
  | zero => simp only [run,Option.some.injEq] at hr; subst d; simp only [run,hs,Option.bind_some]
  | succ n ih =>
    change (step M c).bind (run M n) = some d at hr
    change (step M c).bind (run M (n+1)) = some z
    cases hc : step M c with
    | none => simp [hc] at hr
    | some x =>
      rw [hc,Option.bind_some] at hr
      simp only [Option.bind_some]
      exact ih hr

def RunInvariant (M : Program t q a) (pre : TapePred t a) (c : Config t q a) : Prop :=
  ∃ v, pre v ∧ ∃ n, run M n (v.start M) = some c

theorem RunInvariant.initial {M : Program t q a} {pre : TapePred t a}
    {v : Tapes t a} (hv : pre v) : RunInvariant M pre (v.start M) := ⟨v,hv,0,rfl⟩

theorem RunInvariant.step {M : Program t q a} {pre : TapePred t a} {c d : Config t q a}
    (hc : RunInvariant M pre c) (hs : Machine.step M c = some d) : RunInvariant M pre d := by
  obtain ⟨v,hv,n,hr⟩ := hc
  exact ⟨v,hv,n+1,run_step_append hr hs⟩

/-- A reached halting configuration is the endpoint of the actual Hoare run,
so its complete tapes satisfy the postcondition. -/
theorem RunInvariant.post {M : Program t q a} {pre post : TapePred t a} {k : ℕ}
    (h : HoareTime M pre post k) {c : Config t q a} (hc : RunInvariant M pre c)
    (hh : Machine.step M c = none) : post c.tapes := by
  obtain ⟨v,hv,n,hr⟩ := hc
  obtain ⟨m,z,_,hz,hhalt,hpost⟩ := h v hv
  have hn := run_length_le_of_halt hr hz hhalt
  have hm := run_length_le_of_halt hz hr hh
  have he : n = m := by omega
  rw [he,hz,Option.some.injEq] at hr
  subst c
  exact hpost

/-- Linear-time components get fixed intervals from their initial head bounds.
The theorem does not substitute runtime for space in recursive bodies. -/
theorem RunInvariant.heads {M : Program t q a} {pre post : TapePred t a} {k : ℕ}
    (h : HoareTime M pre post k) (lo hi : Fin t → ℤ)
    (hinitial : ∀ v, pre v → ∀ i, lo i+k ≤ v.head i ∧ v.head i+k ≤ hi i)
    {c : Config t q a} (hc : RunInvariant M pre c) :
    ∀ i, lo i ≤ c.head i ∧ c.head i ≤ hi i := by
  obtain ⟨v,hv,n,hr⟩ := hc
  obtain ⟨m,z,hm,hz,hhalt,_⟩ := h v hv
  have hn := (run_length_le_of_halt hr hz hhalt).trans hm
  intro i
  have ht := run_head_travel hr i
  have hi := hinitial v hv i
  change v.head i-(n : ℤ) ≤ c.head i ∧ c.head i ≤ v.head i+(n : ℤ) at ht
  omega

theorem RunInvariant.heads_eq {M : Program t q a} {v : Tapes t a}
    {post : TapePred t a} {k : ℕ} (h : HoareTime M (· = v) post k)
    {c : Config t q a} (hc : RunInvariant M (· = v) c) :
    ∀ i, v.head i-k ≤ c.head i ∧ c.head i ≤ v.head i+k := by
  apply RunInvariant.heads h (fun i => v.head i-k) (fun i => v.head i+k) ?_ hc
  intro w hw i
  subst w
  constructor <;> omega

end IntegerMultBounds.Machine
