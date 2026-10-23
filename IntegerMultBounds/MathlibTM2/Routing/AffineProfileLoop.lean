module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileCall

/-! A fixed loop generates coordinates from activity/source profiles. Slot
indices come from the internal counter rather than supplied position words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def affineProfileFrames (Ls : ℕ) : List (Bool × ℕ) → List (Fin (A + 4))
  | [] => []
  | (enabled, q) :: rest => binSyms 1 enabled.toNat ++ separator ::
      (binSyms Ls q ++ separator :: affineProfileFrames Ls rest)

def AffineProfileReady (Li Ls k o N : ℕ) (i : ℕ) : List (Bool × ℕ) → Prop
  | [] => True
  | (_, q) :: rest => i < 2 ^ Li ∧ i * k + o < N ∧ q + 1 < 2 ^ Ls ∧
      AffineProfileReady Li Ls k o N (i + 1) rest

def affineProfileTraceBank (R : Fin T → List (Fin (A + 4))) (rg : AffineProfileReg → Fin T)
    (Li Lk Ls i k o N : ℕ) : List (Bool × ℕ) → Fin T → List (Fin (A + 4))
  | [] => R
  | (enabled, q) :: rest => affineProfileTraceBank
      (affineProfileCallBank R rg Li Lk Ls i k o N q enabled (affineProfileFrames Ls rest))
      rg Li Lk Ls (i + 1) k o N rest

def affineProfileLoopBody (rg : AffineProfileReg → Fin T) : Pr P T Q A U :=
  .seq (affineProfileCallProgram rg) (.act (peekR (rg .src)))

theorem affineProfileLoop_exec (body : P → Pr P T Q A U)
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lk Ls i k o N : ℕ) (entries : List (Bool × ℕ))
    (hk : k < 2 ^ Lk) (hN : N < 2 ^ (Li + Lk))
    (hready : AffineProfileReady Li Ls k o N i entries)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls entries)
    (hindex : S.R (rg .index) = binSyms Li i) (hstride : S.R (rg .stride) = binSyms Lk k)
    (hoffset : S.R (rg .offset) = binSyms (Li + Lk) o)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg .one) = binSyms Ls 1)
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride →
      r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (rg r) = [])
    (hflag : v.flag = (affineProfileFrames (A := A) Ls entries).head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ entries.length * (affineProfileCallCost Li Lk Ls + 2) + 1 ∧
      Exec body (.loop (·.flag) (affineProfileLoopBody rg)) (mk v S) steps
        (mk v' { S with R := affineProfileTraceBank S.R rg Li Lk Ls i k o N entries }) := by
  induction entries generalizing i v S with
  | nil =>
    refine ⟨v, 1, rfl, by simp, ?_⟩
    exact Exec.loop_false (by simpa only [affineProfileFrames, List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons pair rest ih =>
    obtain ⟨enabled, q⟩ := pair
    obtain ⟨hi, hpos, hq, hr⟩ := hready
    obtain ⟨v₁, n₁, hu₁, ht₁, he₁⟩ := affineProfileCall_exec body rg hrg Li Lk Ls i k o N q enabled
      hi hk hN hpos hq (affineProfileFrames Ls rest) v S hsrc hindex hstride hoffset hlast hone hblank
    let S₁ : Stacks T A := { S with R := affineProfileCallBank S.R rg Li Lk Ls i k o N q enabled (affineProfileFrames Ls rest) }
    have hs : S₁.R (rg .src) = affineProfileFrames Ls rest := by simp [S₁, affineProfileCallBank, hrg.eq_iff]
    have hi : S₁.R (rg .index) = binSyms Li (i + 1) := by simp [S₁, affineProfileCallBank]
    have hkeep (r : AffineProfileReg) (hs : r ≠ .src) (ha : r ≠ .archive)
        (hd : r ≠ .dst) (hi : r ≠ .index) : S₁.R (rg r) = S.R (rg r) := by
      simp [S₁, affineProfileCallBank, hrg.eq_iff, hs, ha, hd, hi]
    have hb : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride →
        r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S₁.R (rg r) = [] := by
      intro r hs ha hi hk ho hl h1 hd
      exact (hkeep r hs ha hd hi).trans (hblank r hs ha hi hk ho hl h1 hd)
    let v₂ := { v₁ with flag := (affineProfileFrames (A := A) Ls rest).head?.isSome }
    have hp : (peekR (rg .src) : Act T Q A U).run (mk v₁ S₁) = mk v₂ S₁ := by
      simp only [peekR_run, hs]; rfl
    obtain ⟨v₃, n₃, hu₃, ht₃, he₃⟩ := ih (i + 1) hr v₂ S₁ hs hi
      ((hkeep .stride (by decide) (by decide) (by decide) (by decide)).trans hstride)
      ((hkeep .offset (by decide) (by decide) (by decide) (by decide)).trans hoffset)
      ((hkeep .last (by decide) (by decide) (by decide) (by decide)).trans hlast)
      ((hkeep .one (by decide) (by decide) (by decide) (by decide)).trans hone) hb rfl
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
