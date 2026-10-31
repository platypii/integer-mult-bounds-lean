module

public import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
public import IntegerMultBounds.Machine.CountedLoopAlphabetSpace
public import IntegerMultBounds.Machine.RunInvariantComposition

/-! Uniform workspace for the actual reusable counted loop, including copying
the mutable clock, restoring its descriptor and clearing the exhausted clock.
The encoded count affects time, while space uses one body allowance. -/
@[expose] public section
namespace IntegerMultBounds.Machine.CountedLoopReuseAlphabet
variable {t q a : ℕ}

theorem loop_heads (M : Program t q a) (bs : List Bool) (v : ℕ → Tapes t a) (B : ℕ)
    (hbody : ∀ l < Counter.value bs, HoareTime M (· = v l) (· = v (l+1)) B)
    (lo hi : ℤ)
    (hbanks : ∀ l ≤ Counter.value bs, ∀ i, lo ≤ (v l).head i ∧ (v l).head i ≤ hi)
    {c : Config (t+2) (7+(q+5)+4) a} {n : ℕ}
    (hrun : Machine.run (program M) n ((bank (v 0) empty (binary bs) 1 1).start (program M)) = some c) :
    ∀ i, min lo 0-(B+3*bs.length+8 : ℕ) ≤ c.head i ∧
      c.head i ≤ max hi ((bs.length : ℤ)+1)+(B+3*bs.length+8 : ℕ) := by
  let budget := B+3*bs.length+8
  let lower := min lo 0
  let upper := max hi ((bs.length : ℤ)+1)
  let H : TapePred (t+2) a := fun w => ∀ i, lower-budget ≤ w.head i ∧ w.head i ≤ upper+budget
  change H c.tapes
  let prep := controlsProgram (prepareControls a) t
  let counted := extend (CountedLoopAlphabet.program M) 1
  let clean := controlsProgram (cleanControls a) t
  let initial := bank (v 0) empty (binary bs) 1 1
  let prepared := bank (v 0) (binary bs) (binary bs) 1 1
  let exhausted := bank (v (Counter.value bs)) (binary (List.replicate bs.length true)) (binary bs) 1 1
  have hp : HoareTime prep (· = initial) (· = prepared) (3*bs.length+8) :=
    controls_hoare (prepare_hoare bs) (v 0)
  have hl := counted_hoare M bs (Counter.value bs) v (fun _ => B) rfl hbody
  have he : HoareTime clean (· = exhausted)
      (· = bank (v (Counter.value bs)) empty (binary bs) 1 1) (2*bs.length+4) := by
    simpa only [List.length_replicate,clean,exhausted,bank] using
      controls_hoare (clean_hoare (List.replicate bs.length true) bs) (v (Counter.value bs))
  have hP : 3*bs.length+8 ≤ budget := by dsimp [budget]; omega
  have hC : 2*bs.length+4 ≤ budget := by dsimp [budget]; omega
  have hB : B ≤ budget := by dsimp [budget]; omega
  have hbank (l : ℕ) (hl : l ≤ Counter.value bs) (clock descriptor : ℤ → Fin (a+4)) :
      ∀ i, lower ≤ (bank (v l) clock descriptor 1 1).head i ∧
        (bank (v l) clock descriptor 1 1).head i ≤ upper := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      have h := hbanks l hl i
      simpa only [bank,Tapes.append,Fin.addCases_left] using
        And.intro ((min_le_left lo 0).trans h.1) (h.2.trans (le_max_left hi ((bs.length : ℤ)+1)))
    | right i =>
      simp only [bank,Tapes.append,Fin.addCases_right,controls,ite_self]
      have h0 := min_le_right lo (0 : ℤ)
      have h1 := le_max_right hi ((bs.length : ℤ)+1)
      dsimp only [lower,upper]
      constructor <;> omega
  have hpHeads : ∀ z, RunInvariant prep (· = initial) z → H z.tapes := by
    intro z hz i
    have hh := hz.heads_eq hp i
    have hb := hbank 0 (Nat.zero_le _) empty (binary bs) i
    change lower-budget ≤ z.head i ∧ z.head i ≤ upper+budget
    change initial.head i-(3*bs.length+8 : ℕ) ≤ z.head i ∧ z.head i ≤ initial.head i+(3*bs.length+8 : ℕ) at hh
    change lower ≤ initial.head i ∧ initial.head i ≤ upper at hb
    omega
  have heHeads : ∀ z, RunInvariant clean (· = exhausted) z → H z.tapes := by
    intro z hz i
    have hh := hz.heads_eq he i
    have hb := hbank (Counter.value bs) le_rfl (binary (List.replicate bs.length true)) (binary bs) i
    change lower-budget ≤ z.head i ∧ z.head i ≤ upper+budget
    change exhausted.head i-(2*bs.length+4 : ℕ) ≤ z.head i ∧ z.head i ≤ exhausted.head i+(2*bs.length+4 : ℕ) at hh
    change lower ≤ exhausted.head i ∧ exhausted.head i ≤ upper at hb
    omega
  have hlHeads : ∀ z, RunInvariant counted (· = prepared) z → H z.tapes := by
    intro z hz
    obtain ⟨w,hw,k,hr⟩ := hz
    subst w
    change Machine.run (extend (CountedLoopAlphabet.program M) 1) k
      ((bank (v 0) (binary bs) (binary bs) 1 1).start (extend (CountedLoopAlphabet.program M) 1)) = some z at hr
    rw [←loop_bank (v 0) bs bs] at hr
    change Machine.run (extend (CountedLoopAlphabet.program M) 1) k
      (((CountedLoopAlphabet.bank (v 0) empty bs).start (CountedLoopAlphabet.program M)).extend (one (binary bs) 1)) = some z at hr
    obtain ⟨x,hx,rfl⟩ := extend_run_inv (CountedLoopAlphabet.program M) (one (binary bs) 1) hr
    have hc : CountedLoopAlphabet.ClockTape bs.length (empty : ℤ → Fin (a+4)) := by
      constructor
      · simp [empty]
      · intro j hj; simp [empty,show j ≠ 0 by omega,blank,separator,Fin.ext_iff]
      · simp [empty,show (bs.length : ℤ)+1 ≠ 0 by omega]
    have hh := CountedLoopAlphabet.loop_heads M empty bs v B hbody hc (fun _ => lo) (fun _ => hi) hbanks hx
    intro i
    induction i using (Fin.addCases (m := t+1) (n := 1)) with
    | left i =>
      simp only [Config.extend,Config.tapes,Tapes.append,Fin.addCases_left]
      have hs := hh i
      induction i using Fin.addCases with
      | left i =>
        simp only [Fin.addCases_left] at hs
        have hlo := min_le_left lo (0 : ℤ)
        have hhi := le_max_left hi ((bs.length : ℤ)+1)
        dsimp only [lower,upper]
        omega
      | right i =>
        fin_cases i
        simp only [Fin.addCases_right] at hs
        have hlo := min_le_right lo (0 : ℤ)
        have hhi := le_max_right hi ((bs.length : ℤ)+1)
        dsimp only [lower,upper]
        omega
    | right i =>
      fin_cases i
      simp only [Config.extend,Config.tapes,Tapes.append,Fin.addCases_right,one]
      have hlo := min_le_right lo (0 : ℤ)
      have hhi := le_max_right hi ((bs.length : ℤ)+1)
      dsimp only [lower,upper]
      omega
  have hfull : RunInvariant (seq (seq prep counted) clean) (· = initial) c :=
    ⟨initial,rfl,n,hrun⟩
  apply RunInvariant.seq_tapes (hp.seq hl) H ?_ heHeads hfull
  intro z hz
  exact RunInvariant.seq_tapes hp H hpHeads hlHeads hz

end IntegerMultBounds.Machine.CountedLoopReuseAlphabet
