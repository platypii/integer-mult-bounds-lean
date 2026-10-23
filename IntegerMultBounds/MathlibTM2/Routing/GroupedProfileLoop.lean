module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileCall

/-! A fixed loop generates grouped coordinates from activity/source profiles.
Group indices and within-group offsets are computed from the internal counter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def GroupedProfileReady (Li Ls g k b N : ℕ) (i : ℕ) : List (Bool × ℕ) → Prop
  | [] => True
  | (_, q) :: rest => i < 2 ^ Li ∧ i / g * k + (i % g + b) < N ∧ q + 1 < 2 ^ Ls ∧
      GroupedProfileReady Li Ls g k b N (i + 1) rest

def groupedProfileTraceBank (R : Fin T → List (Fin (A + 4))) (rg : GroupedProfileReg → Fin T)
    (Li Lg Lk Ls i g k b N : ℕ) : List (Bool × ℕ) → Fin T → List (Fin (A + 4))
  | [] => R
  | (enabled, q) :: rest => groupedProfileTraceBank
      (groupedProfileCallBank R rg Li Lg Lk Ls i g k b N q enabled (affineProfileFrames Ls rest))
      rg Li Lg Lk Ls (i + 1) g k b N rest

def groupedProfileLoopBody (rg : GroupedProfileReg → Fin T) : Pr P T Q A U :=
  .seq (groupedProfileCallProgram rg) (.act (peekR (rg .src)))

theorem groupedProfileLoop_exec (body : P → Pr P T Q A U)
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lg Lk Ls i g k b N : ℕ) (entries : List (Bool × ℕ))
    (hg : g < 2 ^ Lg) (hgpositive : 0 < g) (hk : k < 2 ^ Lk)
    (hwidth : Lg ≤ Li + Lk) (hN : N < 2 ^ (Li + Lk))
    (hready : GroupedProfileReady Li Ls g k b N i entries)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls entries)
    (hindex : S.R (rg (.coordinate (.arithmetic .index))) = binSyms Li i)
    (hgroup : S.R (rg (.coordinate (.arithmetic .group))) = binSyms Lg g)
    (hstride : S.R (rg (.coordinate (.arithmetic .stride))) = binSyms Lk k)
    (hbase : S.R (rg (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) b)
    (hlast : S.R (rg (.coordinate .last)) = binSyms (Li + Lk) (N - 1))
    (hone : S.R (rg (.coordinate .one)) = binSyms Ls 1)
    (hblank : ∀ r, r ∉ groupedProfileLive → S.R (rg r) = [])
    (hflag : v.flag = (affineProfileFrames (A := A) Ls entries).head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ entries.length * (groupedProfileCallCost Li Lg Lk Ls + 2) + 1 ∧
      Exec body (.loop (·.flag) (groupedProfileLoopBody rg)) (mk v S) steps
        (mk v' { S with R := groupedProfileTraceBank S.R rg Li Lg Lk Ls i g k b N entries }) := by
  induction entries generalizing i v S with
  | nil =>
    refine ⟨v, 1, rfl, by simp, ?_⟩
    exact Exec.loop_false (by simpa only [affineProfileFrames, List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons pair rest ih =>
    obtain ⟨enabled, q⟩ := pair
    obtain ⟨hi, hpos, hq, hr⟩ := hready
    obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := groupedProfileCall_exec body rg hrg Li Lg Lk Ls i g k b N q enabled
      hi hg hgpositive hk hwidth hN hpos hq (affineProfileFrames Ls rest) v S hsrc hindex hgroup hstride hbase hlast hone hblank
    let S₁ : Stacks T A := { S with R := groupedProfileCallBank S.R rg Li Lg Lk Ls i g k b N q enabled (affineProfileFrames Ls rest) }
    have hs : S₁.R (rg .src) = affineProfileFrames Ls rest := by simp [S₁, groupedProfileCallBank, hrg.eq_iff]
    have hi : S₁.R (rg (.coordinate (.arithmetic .index))) = binSyms Li (i + 1) := by simp [S₁, groupedProfileCallBank]
    have hkeep (r : GroupedProfileReg) (hs : r ≠ .src) (ha : r ≠ .archive)
        (hd : r ≠ .coordinate .dst) (hi : r ≠ .coordinate (.arithmetic .index)) : S₁.R (rg r) = S.R (rg r) := by
      simp [S₁, groupedProfileCallBank, hrg.eq_iff, hs, ha, hd, hi]
    have hb : ∀ r, r ∉ groupedProfileLive → S₁.R (rg r) = [] := by
      intro r hr
      have hne (j : GroupedProfileReg) (hj : j ∈ groupedProfileLive) : r ≠ j := by
        intro he; apply hr; simpa only [he] using hj
      exact (hkeep r (hne _ (by simp [groupedProfileLive])) (hne _ (by simp [groupedProfileLive]))
        (hne _ (by simp [groupedProfileLive])) (hne _ (by simp [groupedProfileLive]))).trans (hblank r hr)
    let v₂ := { v₁ with flag := (affineProfileFrames (A := A) Ls rest).head?.isSome }
    have hp : (peekR (rg .src) : Act T Q A U).run (mk v₁ S₁) = mk v₂ S₁ := by
      simp only [peekR_run, hs]; rfl
    obtain ⟨v₃, n₃, hu₃, ht₃, he₃⟩ := ih (i + 1) hr v₂ S₁ hs hi
      ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hgroup)
      ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hstride)
      ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hbase)
      ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hlast)
      ((hkeep _ (by decide) (by decide) (by decide) (by decide)).trans hone) hb rfl
    have hf : v.flag = true := by
      have hn : affineProfileFrames (A := A) Ls ((enabled, q) :: rest) ≠ [] := by
        intro he
        have hh := congrArg List.length he
        simp [affineProfileFrames] at hh
      obtain ⟨a, as, he⟩ := List.exists_cons_of_ne_nil hn
      simpa only [he, List.head?_cons, Option.isSome_some] using hflag
    have hex := Exec.loop_true (body := body) (f := (·.flag)) (by simpa only [mk_var] using hf)
      (Exec.seq he₁ (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v₁ S₁))) he₃
    refine ⟨v₃, n₁ + n₃ + 2, hu₃.trans hu₁, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · exact Exec.cast hex (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
