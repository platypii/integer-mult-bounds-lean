module

public import IntegerMultBounds.Machine.CountedLoopAlphabet

/-! Fixed clock intervals for the actual counted-loop transitions. The
origin marker and blank endpoint prevent repeated decrements from allocating
more clock cells, independently of the number of body iterations. -/
@[expose] public section
namespace IntegerMultBounds.Machine.CountedLoopAlphabet
variable {t q a W : ℕ}

structure ClockTape (W : ℕ) (f : ℤ → Fin (a+4)) : Prop where
  origin : f 0 = separator
  unique : ∀ z, 0 < z → f z ≠ separator
  endpoint : f (W+1) = blank

structure ClockBounds (W : ℕ) (f : ℤ → Fin (a+4)) (r : ℤ) (s : Fin 5) : Prop where
  tape : ClockTape W f
  lower : 0 ≤ r
  upper : r ≤ W+1
  borrow : s = 0 → 1 ≤ r
  boundary : s = 3 ∨ s = 4 → r = 1

theorem ClockTape.writeBit {f : ℤ → Fin (a+4)} (h : ClockTape W f) (r : ℤ)
    (hr : 0 < r) (hupper : r < W+1) (b : Bool) : ClockTape W (Function.update f r (bitSymbol b)) := by
  constructor
  · rw [Function.update_of_ne (by omega)]; exact h.origin
  · intro z hz
    by_cases he : z = r
    · subst z; rw [Function.update_self]; cases b <;> simp [bitSymbol,separator,Fin.ext_iff]
    · rw [Function.update_of_ne he]; exact h.unique z hz
  · rw [Function.update_of_ne (by omega)]; exact h.endpoint

theorem ClockTape.putBits (bs : List Bool) {f : ℤ → Fin (a+4)} (h : ClockTape bs.length f) :
    ClockTape bs.length (CountedLoopAlphabet.putBits f 1 bs) := by
  constructor
  · rw [putBits_outside _ _ _ _ (Or.inl (by omega))]; exact h.origin
  · intro z hz
    by_cases he : z < 1+bs.length
    · exact putBits_ne_separator f 1 z bs (by omega) he
    · rw [putBits_outside _ _ _ _ (Or.inr (by omega))]; exact h.unique z hz
  · rw [putBits_outside _ _ _ _ (Or.inr (by omega))]; exact h.endpoint

theorem ClockTape.binary (bs : List Bool) :
    ClockTape bs.length (CountedLoopAlphabet.putBits
      (fun z => if z = 0 then separator else blank : ℤ → Fin (a+4)) 1 bs) := by
  apply ClockTape.putBits
  constructor
  · simp
  · intro z hz
    simp [show z ≠ 0 by omega,blank,separator,Fin.ext_iff]
  · simp [show (bs.length : ℤ)+1 ≠ 0 by omega]

private theorem ClockBounds.not_endpoint {f : ℤ → Fin (a+4)} {r : ℤ} {s : Fin 5}
    (h : ClockBounds W f r s) (hb : f r ≠ blank) : r < W+1 := by
  have hn : r ≠ W+1 := by intro he; apply hb; rw [he]; exact h.tape.endpoint
  have hu := h.upper
  omega

private theorem ClockBounds.zero {f : ℤ → Fin (a+4)} {r : ℤ} (h : ClockBounds W f r 0)
    (hf : f r = bitSymbol false) : ClockBounds W (Function.update f r (bitSymbol true)) (r+1) 0 := by
  have hr := h.borrow rfl
  have hu := h.not_endpoint (by rw [hf]; simp [bitSymbol,blank])
  refine ⟨h.tape.writeBit r (by omega) hu true,by omega,by omega,?_,?_⟩
  · intro _; omega
  · simp

private theorem ClockBounds.one {f : ℤ → Fin (a+4)} {r : ℤ} (h : ClockBounds W f r 0)
    (hf : f r = bitSymbol true) : ClockBounds W (Function.update f r (bitSymbol false)) (r-1) 1 := by
  have hr := h.borrow rfl
  have hu := h.not_endpoint (by rw [hf]; simp [bitSymbol,blank])
  exact ⟨h.tape.writeBit r (by omega) hu false,by omega,by omega,by simp,by simp⟩

private theorem ClockBounds.on_blank {f : ℤ → Fin (a+4)} {r : ℤ} (h : ClockBounds W f r 0) :
    ClockBounds W f (r-1) 2 := by
  have hr := h.borrow rfl
  exact ⟨h.tape,by omega,by have := h.upper; omega,by simp,by simp⟩

private theorem ClockBounds.rewind {f : ℤ → Fin (a+4)} {r : ℤ} {s : Fin 5}
    (h : ClockBounds W f r s) (hs : s = 1 ∨ s = 2) (hf : f r ≠ separator) : ClockBounds W f (r-1) s := by
  have hr : 0 < r := by
    have hn : r ≠ 0 := by intro he; apply hf; rw [he]; exact h.tape.origin
    have hl := h.lower
    omega
  refine ⟨h.tape,by omega,by have := h.upper; omega,?_,?_⟩
  · rcases hs with rfl | rfl <;> simp
  · rcases hs with rfl | rfl <;> simp

private theorem ClockBounds.marker {f : ℤ → Fin (a+4)} {r : ℤ} {s : Fin 5}
    (h : ClockBounds W f r s) (hs : s = 1 ∨ s = 2) (hf : f r = separator) :
    ClockBounds W f (r+1) (if s = 1 then 3 else 4) := by
  have hr : r = 0 := by
    have hn : ¬0 < r := by intro hp; exact h.tape.unique r hp hf
    have hl := h.lower
    omega
  subst r
  refine ⟨h.tape,by omega,by omega,?_,?_⟩
  · rcases hs with rfl | rfl <;> simp
  · intro _; rfl

/-- Every real control transition preserves the fixed clock interval and the
whole nonclock bank. State 3 enters the body and is handled separately. -/
theorem ClockBounds.control_step (M : Program t q a) (v : Tapes t a)
    {f : ℤ → Fin (a+4)} {r : ℤ} {s : Fin 5} (h : ClockBounds W f r s) (hs : s ≠ 3)
    {d : Config (t+1) (q+5) a} (hd : Machine.step (program M) (cfg M v f r s) = some d) :
    ∃ f' r' s', d = cfg M v f' r' s' ∧ ClockBounds W f' r' s' := by
  fin_cases s
  · change Machine.step (program M) (cfg M v f r 0) = some d at hd
    change ClockBounds W f r 0 at h
    by_cases hf : f r = bitSymbol false
    · rw [step_zero M v f r hf,Option.some.injEq] at hd
      exact ⟨_,_,_,hd.symm,h.zero hf⟩
    · by_cases ht : f r = bitSymbol true
      · rw [step_one M v f r ht,Option.some.injEq] at hd
        exact ⟨_,_,_,hd.symm,h.one ht⟩
      · by_cases hb : f r = blank
        · rw [step_blank M v f r hb,Option.some.injEq] at hd
          exact ⟨_,_,_,hd.symm,h.on_blank⟩
        · simp [Machine.step,program,cfg,Tapes.append,clockProgram,hf,ht,hb] at hd
  · change Machine.step (program M) (cfg M v f r 1) = some d at hd
    change ClockBounds W f r 1 at h
    by_cases hf : f r = separator
    · rw [step_marker M v f r 1 (by simp) hf,Option.some.injEq] at hd
      exact ⟨_,_,_,hd.symm,h.marker (by simp) hf⟩
    · rw [step_return M v f r 1 (by simp) hf,Option.some.injEq] at hd
      exact ⟨_,_,_,hd.symm,h.rewind (by simp) hf⟩
  · change Machine.step (program M) (cfg M v f r 2) = some d at hd
    change ClockBounds W f r 2 at h
    by_cases hf : f r = separator
    · rw [step_marker M v f r 2 (by simp) hf,Option.some.injEq] at hd
      exact ⟨_,_,_,hd.symm,h.marker (by simp) hf⟩
    · rw [step_return M v f r 2 (by simp) hf,Option.some.injEq] at hd
      exact ⟨_,_,_,hd.symm,h.rewind (by simp) hf⟩
  · exact (hs rfl).elim
  · change Machine.step (program M) (cfg M v f r 4) = some d at hd
    rw [CountedLoopAlphabet.halt] at hd; cases hd

/-- Either a body configuration is active, or the clock is advancing while
the entire body bank is parked at an admissible boundary. -/
def LoopInvariant (M : Program t q a) (I : (ℤ → Fin (a+4)) → Config t q a → Prop)
    (J : Tapes t a → (ℤ → Fin (a+4)) → ℤ → Fin 5 → Prop)
    (W : ℕ) (c : Config (t+1) (q+5) a) : Prop :=
  (∃ x f, I f x ∧ ClockTape W f ∧ c = bodyCfg x f 1) ∨
    (∃ v f r s, J v f r s ∧ ClockBounds W f r s ∧ c = cfg M v f r s)

theorem LoopInvariant.initial (M : Program t q a) (I : (ℤ → Fin (a+4)) → Config t q a → Prop)
    (J : Tapes t a → (ℤ → Fin (a+4)) → ℤ → Fin 5 → Prop)
    (v : Tapes t a) (f : ℤ → Fin (a+4)) (hv : J v f 1 0) (hf : ClockTape W f) :
    LoopInvariant M I J W ((v.append ⟨fun _ => 1,fun _ => f⟩).start (program M)) := by
  refine Or.inr ⟨v,f,1,0,hv,?_,rfl⟩
  exact ⟨hf,by omega,by omega,by simp,by simp⟩

/-- The same body and parked-bank invariants are reused at every iteration.
No iteration count or total runtime occurs in this preservation theorem. -/
theorem LoopInvariant.step {M : Program t q a} {I : (ℤ → Fin (a+4)) → Config t q a → Prop}
    {J : Tapes t a → (ℤ → Fin (a+4)) → ℤ → Fin 5 → Prop}
    (hI : ∀ f x y, I f x → Machine.step M x = some y → I f y)
    (hstart : ∀ v f, J v f 1 3 → I f (v.start M))
    (hreturn : ∀ f x, I f x → Machine.step M x = none → J x.tapes f 1 0)
    (hcontrol : ∀ v f r s f' r' s', J v f r s → s ≠ 3 →
      Machine.step (program M) (cfg M v f r s) = some (cfg M v f' r' s') → J v f' r' s')
    {c d : Config (t+1) (q+5) a} (hc : LoopInvariant M I J W c)
    (hs : Machine.step (program M) c = some d) : LoopInvariant M I J W d := by
  rcases hc with ⟨x,f,hx,hf,rfl⟩ | ⟨v,f,r,s,hv,hclock,rfl⟩
  · cases hm : Machine.step M x with
    | some y =>
      rw [body_step M f 1 hm,Option.some.injEq] at hs
      exact Or.inl ⟨y,f,hI f x y hx hm,hf,hs.symm⟩
    | none =>
      rw [body_return M f 1 hm,Option.some.injEq] at hs
      refine Or.inr ⟨x.tapes,f,1,0,hreturn f x hx hm,?_,hs.symm⟩
      exact ⟨hf,by omega,by omega,by simp,by simp⟩
  · by_cases he : s = 3
    · subst s
      have hr := hclock.boundary (Or.inl rfl)
      subst r
      rw [body_enter M v f 1,Option.some.injEq] at hs
      exact Or.inl ⟨v.start M,f,hstart v f hv,hclock.tape,hs.symm⟩
    · obtain ⟨f',r',s',hd,hbounds⟩ := hclock.control_step M v he hs
      exact Or.inr ⟨v,f',r',s',hcontrol v f r s f' r' s' hv he (by rw [←hd]; exact hs),hbounds,hd⟩

theorem LoopInvariant.run {M : Program t q a} {I : (ℤ → Fin (a+4)) → Config t q a → Prop}
    {J : Tapes t a → (ℤ → Fin (a+4)) → ℤ → Fin 5 → Prop}
    (hI : ∀ f x y, I f x → Machine.step M x = some y → I f y)
    (hstart : ∀ v f, J v f 1 3 → I f (v.start M))
    (hreturn : ∀ f x, I f x → Machine.step M x = none → J x.tapes f 1 0)
    (hcontrol : ∀ v f r s f' r' s', J v f r s → s ≠ 3 →
      Machine.step (program M) (cfg M v f r s) = some (cfg M v f' r' s') → J v f' r' s')
    {c d : Config (t+1) (q+5) a} (hc : LoopInvariant M I J W c) {n : ℕ}
    (hrun : Machine.run (program M) n c = some d) : LoopInvariant M I J W d := by
  induction n generalizing c with
  | zero => simp only [Machine.run,Option.some.injEq] at hrun; subst d; exact hc
  | succ n ih =>
    simp only [Machine.run] at hrun
    cases hs : Machine.step (program M) c with
    | none => simp [hs] at hrun
    | some x =>
      rw [hs,Option.bind_some] at hrun
      exact ih (hc.step hI hstart hreturn hcontrol hs) hrun

/-- Whole-bank fixed intervals use the body's intervals and one clock interval
of width W+2. Repeated complete body scans do not accumulate extra storage. -/
theorem LoopInvariant.heads {M : Program t q a} {I : (ℤ → Fin (a+4)) → Config t q a → Prop}
    {J : Tapes t a → (ℤ → Fin (a+4)) → ℤ → Fin 5 → Prop}
    (lo hi : Fin t → ℤ)
    (hI : ∀ f x, I f x → ∀ i, lo i ≤ x.head i ∧ x.head i ≤ hi i)
    (hJ : ∀ v f r s, J v f r s → ∀ i, lo i ≤ v.head i ∧ v.head i ≤ hi i)
    {c : Config (t+1) (q+5) a} (hc : LoopInvariant M I J W c) :
    ∀ i : Fin (t+1), (Fin.addCases (motive := fun _ : Fin (t+1) => ℤ) lo (fun _ : Fin 1 => 0)) i ≤ c.head i ∧
      c.head i ≤ (Fin.addCases (motive := fun _ : Fin (t+1) => ℤ) hi (fun _ : Fin 1 => (W : ℤ)+1)) i := by
  rcases hc with ⟨x,f,hx,hf,rfl⟩ | ⟨v,f,r,s,hv,hclock,rfl⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [bodyCfg,Config.mapState,Config.extend,Config.tapes,Tapes.append,Fin.addCases_left] using hI f x hx i
    | right i =>
      fin_cases i
      simp only [bodyCfg,Config.mapState,Config.extend,Config.tapes,Tapes.append,Fin.addCases_right]
      omega
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [cfg,Tapes.append,Fin.addCases_left] using hJ v f r s hv i
    | right i =>
      fin_cases i
      simpa only [cfg,Tapes.append,Fin.addCases_right] using And.intro hclock.lower hclock.upper

end IntegerMultBounds.Machine.CountedLoopAlphabet
