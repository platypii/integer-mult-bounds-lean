module

public import IntegerMultBounds.Machine.LevelLoop
public import IntegerMultBounds.Machine.CountedLoopReuseAlphabetSpace

/-! The repeated levels and last stage share one uniform workspace allowance.
Clock setup/cleanup and the real sequential boundary are included. -/
@[expose] public section
namespace IntegerMultBounds.Machine.LevelLoop
open FlatCoordinateSchedule
variable {t q r a : ℕ}

theorem level_heads (M : Program t q a) (S : Program t r a) (f : ℕ) (hf : 0 < f)
    (v : ℕ → Tapes t a) (w : Tapes t a) (B : ℕ)
    (hbody : ∀ l, l+1 < f → HoareTime M (· = v l) (· = v (l+1)) B)
    (hlast : HoareTime S (· = v (f-1)) (· = w) B)
    (lo hi : ℤ) (hbanks : ∀ l < f, ∀ i, lo ≤ (v l).head i ∧ (v l).head i ≤ hi)
    {c : Config (t+2) ((7+(q+5)+4)+r) a} {n : ℕ}
    (hrun : Machine.run (program M S) n ((bank (v 0) f).start (program M S)) = some c) :
    ∀ i, min lo 0-(B+3*(bits (f-1)).length+8 : ℕ) ≤ c.head i ∧
      c.head i ≤ max hi (((bits (f-1)).length : ℤ)+1)+(B+3*(bits (f-1)).length+8 : ℕ) := by
  let bs := bits (f-1)
  let budget := B+3*bs.length+8
  let lower := min lo 0
  let upper := max hi ((bs.length : ℤ)+1)
  let H : TapePred (t+2) a := fun z => ∀ i, lower-budget ≤ z.head i ∧ z.head i ≤ upper+budget
  change H c.tapes
  have hcount : Counter.value bs = f-1 := bits_value _
  have hB : B ≤ budget := by dsimp [budget]; omega
  have hp := CountedLoopReuseAlphabet.loop_hoare M bs (f-1) v (fun _ => B) hcount
    (fun l hl => hbody l (by omega))
  have hpHeads : ∀ z, RunInvariant (CountedLoopReuseAlphabet.program M) (· = bank (v 0) f) z → H z.tapes := by
    intro z hz
    obtain ⟨u,hu,k,hr⟩ := hz
    subst u
    exact CountedLoopReuseAlphabet.loop_heads M bs v B
      (fun l hl => hbody l (by rw [hcount] at hl; omega)) lo hi
      (fun l hl => hbanks l (by rw [hcount] at hl; omega)) hr
  have hsHeads : ∀ z, RunInvariant (extend S 2) (· = bank (v (f-1)) f) z → H z.tapes := by
    intro z hz
    obtain ⟨u,hu,k,hr⟩ := hz
    subst u
    let controls := CountedLoopReuseAlphabet.controls (a := a) CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary bs) 1 1
    change Machine.run (extend S 2) k (((v (f-1)).start S).extend controls) = some z at hr
    obtain ⟨x,hx,rfl⟩ := extend_run_inv S controls hr
    have hh := (RunInvariant.heads_eq hlast (show RunInvariant S (· = v (f-1)) x from ⟨v (f-1),rfl,k,hx⟩))
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [Config.extend,Config.tapes,Tapes.append,Fin.addCases_left]
      have ht := hh i
      have hb := hbanks (f-1) (by omega) i
      have hlo := min_le_left lo (0 : ℤ)
      have hhi := le_max_left hi ((bs.length : ℤ)+1)
      dsimp only [lower,upper]
      omega
    | right i =>
      simp only [Config.extend,Config.tapes,Tapes.append,Fin.addCases_right,controls,
        CountedLoopReuseAlphabet.controls,ite_self]
      have hlo := min_le_right lo (0 : ℤ)
      have hhi := le_max_right hi ((bs.length : ℤ)+1)
      dsimp only [lower,upper]
      omega
  have hfull : RunInvariant (seq (CountedLoopReuseAlphabet.program M) (extend S 2)) (· = bank (v 0) f) c :=
    ⟨bank (v 0) f,rfl,n,hrun⟩
  exact RunInvariant.seq_tapes hp H hpHeads hsHeads hfull

end IntegerMultBounds.Machine.LevelLoop
