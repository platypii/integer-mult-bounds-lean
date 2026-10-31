module

public import IntegerMultBounds.Machine.RunWithinComposition

/-! Actual halting contracts with one predicate shared by all prefixes.
Their time budgets add, while sequential composition reuses the predicate. -/
@[expose] public section
namespace IntegerMultBounds.Machine
variable {t q r a : ℕ}

def HoareWithin (M : Program t q a) (pre post : TapePred t a) (bound : ℕ)
    (H : TapePred t a) : Prop :=
  ∀ v, pre v → ∃ n ≤ bound, ∃ c, RunWithin M H n (v.start M) c ∧
    step M c = none ∧ post c.tapes

namespace HoareWithin
variable {M : Program t q a} {pre post H : TapePred t a} {B : ℕ}

theorem time (h : HoareWithin M pre post B H) : HoareTime M pre post B := by
  intro v hv
  obtain ⟨n,hn,c,hr,hh,hp⟩ := h v hv
  exact ⟨n,c,hn,hr.1,hh,hp⟩

theorem consequence {pre' post' J : TapePred t a} {C : ℕ}
    (h : HoareWithin M pre post B H) (hp : ∀ v, pre' v → pre v)
    (hq : ∀ v, post v → post' v) (hb : B ≤ C) (hH : ∀ v, H v → J v) :
    HoareWithin M pre' post' C J := by
  intro v hv
  obtain ⟨n,hn,c,hr,hh,hpost⟩ := h v (hp v hv)
  exact ⟨n,hn.trans hb,c,hr.mono hH,hh,hq _ hpost⟩

theorem seq {N : Program t r a} {middle final : TapePred t a} {C : ℕ}
    (hM : HoareWithin M pre middle B H) (hN : HoareWithin N middle final C H) :
    HoareWithin (Machine.seq M N) pre final (B+1+C) H := by
  intro v hv
  obtain ⟨n,hn,c,hr,hh,hp⟩ := hM v hv
  obtain ⟨m,hm,d,hs,hd,hpost⟩ := hN c.tapes hp
  exact ⟨n+1+m,by omega,d.mapState (Fin.natAdd q),hr.seq hh hs,
    seq_halt_right M N hd,hpost⟩

/-- Only linear phases use their time budget to bound workspace. -/
theorem of_time_heads (h : HoareTime M pre post B) (lo hi : ℤ)
    (hmargin : ∀ v, pre v → ∀ j, lo+(B : ℕ) ≤ v.head j ∧ v.head j+(B : ℕ) ≤ hi) :
    HoareWithin M pre post B (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) := by
  intro v hv
  obtain ⟨n,c,hn,hr,hh,hp⟩ := h v hv
  exact ⟨n,hn,c,RunWithin.heads_of_run_le hr hn lo hi (hmargin v hv),hh,hp⟩

/-- A known restored post-bank can bound a linear recovery phase. -/
theorem of_time_post_heads (h : HoareTime M pre post B) (lo hi : ℤ)
    (hmargin : ∀ v, post v → ∀ j, lo+(2*B : ℕ) ≤ v.head j ∧ v.head j+(2*B : ℕ) ≤ hi) :
    HoareWithin M pre post B (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) := by
  intro v hv
  obtain ⟨n,c,hn,hr,hh,hp⟩ := h v hv
  exact ⟨n,hn,c,RunWithin.heads_of_run_post_le hr hn lo hi (hmargin c.tapes hp),hh,hp⟩

/-- Reuse an existing complete execution once all reachable prefixes are bounded. -/
theorem of_time_invariant (h : HoareTime M pre post B)
    (hheads : ∀ c, RunInvariant M pre c → H c.tapes) : HoareWithin M pre post B H := by
  intro v hv
  obtain ⟨n,c,hn,hr,hh,hp⟩ := h v hv
  exact ⟨n,hn,c,⟨hr,fun m _ z hz => hheads z ⟨v,hv,m,hz⟩⟩,hh,hp⟩

/-- The halting certificate covers every actually reachable prefix. -/
theorem invariant (h : HoareWithin M pre post B H) {c : Config t q a}
    (hc : RunInvariant M pre c) : H c.tapes := by
  obtain ⟨v,hv,m,hm⟩ := hc
  obtain ⟨n,hn,d,hr,hh,hp⟩ := h v hv
  exact hr.prefix_of_halt hh hm

end HoareWithin
end IntegerMultBounds.Machine
