module

public import IntegerMultBounds.Machine.CountedLoopAlphabetPaths
public import IntegerMultBounds.Machine.RunInvariant

/-! Body prefix bounds control workspace for the entire counted loop.
Exact countdown words determine the body index. The allowance is paid once,
not multiplied by the number of iterations. -/
@[expose] public section
namespace IntegerMultBounds.Machine.CountedLoopAlphabet
open CountdownData
variable {t q a : ℕ}

private theorem decrement_advance (n : ℕ) (bs : List Bool) :
    decrement (advance n bs) = advance (n+1) bs := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => simpa only [advance] using ih (decrement bs)

private def LevelBody (M : Program t q a) (clock : ℤ → Fin (a+4)) (bs : List Bool)
    (v : ℕ → Tapes t a) (f : ℤ → Fin (a+4)) (c : Config t q a) : Prop :=
  ∃ l, l < Counter.value bs ∧ f = putBits clock 1 (advance (l+1) bs) ∧ RunInvariant M (· = v l) c

private def LevelClock (M : Program t q a) (clock : ℤ → Fin (a+4)) (bs : List Bool)
    (v : ℕ → Tapes t a) (w : Tapes t a) (f : ℤ → Fin (a+4)) (r : ℤ) (s : Fin 5) : Prop :=
  ∃ l, l ≤ Counter.value bs ∧ w = v l ∧
    ControlPath M (cfg M (v l) (putBits clock 1 (advance l bs)) 1 0) (cfg M w f r s)

private theorem level_invariant (M : Program t q a) (clock : ℤ → Fin (a+4)) (bs : List Bool)
    (v : ℕ → Tapes t a) (B : ℕ)
    (hbody : ∀ l < Counter.value bs, HoareTime M (· = v l) (· = v (l+1)) B)
    (hclock : ClockTape bs.length clock) {c : Config (t+1) (q+5) a} {n : ℕ}
    (hrun : Machine.run (program M) n ((bank (v 0) clock bs).start (program M)) = some c) :
    LoopInvariant M (LevelBody M clock bs v) (LevelClock M clock bs v) bs.length c := by
  have hI : ∀ f x y, LevelBody M clock bs v f x → Machine.step M x = some y → LevelBody M clock bs v f y := by
    intro f x y hx hs
    obtain ⟨l,hl,hf,hr⟩ := hx
    exact ⟨l,hl,hf,hr.step hs⟩
  have hstart : ∀ w f, LevelClock M clock bs v w f 1 3 → LevelBody M clock bs v f (w.start M) := by
    intro w f hw
    obtain ⟨l,hl,rfl,hpath⟩ := hw
    have hend : clock (1+(advance l bs).length) = blank := by
      have he : (1 : ℤ)+(advance l bs).length = (bs.length : ℤ)+1 := by rw [advance_length]; omega
      rw [he]; exact hclock.endpoint
    have he := decrement_body_entry M (v l) clock (advance l bs) hclock.origin hend hpath
    have hv := advance_value l bs hl
    have hlt : l < Counter.value bs := by have hp := he.2.2.1; omega
    refine ⟨l,hlt,?_,RunInvariant.initial rfl⟩
    rw [←decrement_advance]
    exact he.2.1
  have hreturn : ∀ f x, LevelBody M clock bs v f x → Machine.step M x = none → LevelClock M clock bs v x.tapes f 1 0 := by
    intro f x hx hh
    obtain ⟨l,hl,hf,hr⟩ := hx
    have hp : x.tapes = v (l+1) := RunInvariant.post (post := fun w => w = v (l+1)) (hbody l hl) hr hh
    refine ⟨l+1,by omega,hp,?_⟩
    rw [hp,hf]
  have hcontrol : ∀ w f r s f' r' s', LevelClock M clock bs v w f r s → s ≠ 3 →
      Machine.step (program M) (cfg M w f r s) = some (cfg M w f' r' s') → LevelClock M clock bs v w f' r' s' := by
    intro w f r s f' r' s' hw hs hh
    obtain ⟨l,hl,hv,hp⟩ := hw
    refine ⟨l,hl,hv,Relation.ReflTransGen.tail hp ?_⟩
    exact ⟨fun he => hs (by simpa only [cfg,Fin.natAdd_inj] using he),hh⟩
  have hinit : LoopInvariant M (LevelBody M clock bs v) (LevelClock M clock bs v) bs.length
      ((bank (v 0) clock bs).start (program M)) := by
    apply LoopInvariant.initial
    · exact ⟨0,Nat.zero_le _,rfl,Relation.ReflTransGen.refl⟩
    · exact hclock.putBits bs
  exact hinit.run hI hstart hreturn hcontrol hrun

/-- The clock proof accepts a body prefix certificate independently of runtime. -/
theorem loop_heads_of_body (M : Program t q a) (clock : ℤ → Fin (a+4)) (bs : List Bool)
    (v : ℕ → Tapes t a) (B : ℕ)
    (hbody : ∀ l < Counter.value bs, HoareTime M (· = v l) (· = v (l+1)) B)
    (hclock : ClockTape bs.length clock) (lo hi : Fin t → ℤ)
    (hbanks : ∀ l ≤ Counter.value bs, ∀ i, lo i ≤ (v l).head i ∧ (v l).head i ≤ hi i)
    (hheads : ∀ l < Counter.value bs, ∀ x, RunInvariant M (· = v l) x →
      ∀ i, lo i ≤ x.head i ∧ x.head i ≤ hi i)
    {c : Config (t+1) (q+5) a} {n : ℕ}
    (hrun : Machine.run (program M) n ((bank (v 0) clock bs).start (program M)) = some c) :
    ∀ i : Fin (t+1),
      (Fin.addCases (motive := fun _ : Fin (t+1) => ℤ) lo (fun _ : Fin 1 => 0)) i ≤ c.head i ∧
      c.head i ≤ (Fin.addCases (motive := fun _ : Fin (t+1) => ℤ) hi (fun _ : Fin 1 => (bs.length : ℤ)+1)) i := by
  have hc := level_invariant M clock bs v B hbody hclock hrun
  apply hc.heads lo hi
  · intro f x hx i
    obtain ⟨l,hl,hf,hr⟩ := hx
    exact hheads l hl x hr i
  · intro w f r s hw i
    obtain ⟨l,hl,rfl,hp⟩ := hw
    exact hbanks l hl i

/-- Every prefix of the real counted loop uses the body-bank intervals enlarged
by one body allowance B, plus the fixed binary clock interval. No factor of
Counter.value bs occurs in the workspace allowance. -/
theorem loop_heads (M : Program t q a) (clock : ℤ → Fin (a+4)) (bs : List Bool)
    (v : ℕ → Tapes t a) (B : ℕ)
    (hbody : ∀ l < Counter.value bs, HoareTime M (· = v l) (· = v (l+1)) B)
    (hclock : ClockTape bs.length clock) (lo hi : Fin t → ℤ)
    (hbanks : ∀ l ≤ Counter.value bs, ∀ i, lo i ≤ (v l).head i ∧ (v l).head i ≤ hi i)
    {c : Config (t+1) (q+5) a} {n : ℕ}
    (hrun : Machine.run (program M) n ((bank (v 0) clock bs).start (program M)) = some c) :
    ∀ i : Fin (t+1),
      (Fin.addCases (motive := fun _ : Fin (t+1) => ℤ) (fun i => lo i-B) (fun _ : Fin 1 => 0)) i ≤ c.head i ∧
      c.head i ≤ (Fin.addCases (motive := fun _ : Fin (t+1) => ℤ) (fun i => hi i+B) (fun _ : Fin 1 => (bs.length : ℤ)+1)) i := by
  have hc := level_invariant M clock bs v B hbody hclock hrun
  apply hc.heads (fun i => lo i-B) (fun i => hi i+B)
  · intro f x hx i
    obtain ⟨l,hl,hf,hr⟩ := hx
    have hb := hbanks l hl.le i
    have hh := hr.heads_eq (hbody l hl) i
    omega
  · intro w f r s hw i
    obtain ⟨l,hl,rfl,hp⟩ := hw
    have hb := hbanks l hl i
    omega

end IntegerMultBounds.Machine.CountedLoopAlphabet
