module

public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceWords
public import IntegerMultBounds.MathlibTM2.Routing.SharedSelectedSourceReverse

/-! A fixed loop consumes raw selected-source records. Every record is archived,
its frame is accumulated in reverse, and all coordinate scratch is restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sharedSelectedSourceLoopBody (rg : Fin 4 → Fin 13 → Fin T)
    (src saved index localOffset tmp dst accum : Fin T) : Pr P T Q A U :=
  .seq (sharedSelectedSourceReverseProgram rg src saved index localOffset tmp dst accum) (.act (peekR src))

def sharedSelectedSourceTraceBank (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) : List GatedSelectedSourceChoice → Fin T → List (Fin (A + 4))
  | [] => R
  | x :: xs => sharedSelectedSourceTraceBank
      (sharedSelectedSourceReverseBank R src saved accum Li Lk x.index k (base x.tag) x.offset x.lo x.hi x.enabled
        (gatedSelectedSourceWords Li Lk xs)) src saved accum Li Lk k base xs

def sharedSelectedSourceIterationCost (Li Lk : ℕ) :=
  (4 * Li + 4 * (Li + Lk) + 12) + (selectedSourceFrameCost Li Lk + 4) +
    (2 * Li + 2) + (2 * (Li + Lk) + 2) + 1 + (2 * (Li + Lk + 3) + 2) + 2

theorem sharedSelectedSourceLoop_exec (body : P → Pr P T Q A U)
    (rg : Fin 4 → Fin 13 → Fin T) (hrg : ∀ tag, Function.Injective (rg tag))
    (src saved index localOffset tmp dst accum : Fin T)
    (hreg : [src, saved, index, localOffset, tmp, dst, accum].Nodup)
    (hsrc : ∀ tag j, src ≠ rg tag j) (hsaved : ∀ tag j, saved ≠ rg tag j)
    (hindexReg : ∀ tag, rg tag 0 = index) (hlocalReg : ∀ tag, rg tag 3 = localOffset)
    (hsep : ∀ tag j, dst ≠ rg tag j) (hacc : ∀ tag j, accum ≠ rg tag j)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) (hk : k < 2 ^ Lk)
    (hfit : ∀ x ∈ xs, x.index < 2 ^ Li ∧ x.position k base < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = gatedSelectedSourceWords Li Lk xs)
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (houtput : S.R dst = [])
    (hstride : ∀ tag, S.R (rg tag 1) = binSyms Lk k)
    (hbase : ∀ tag, S.R (rg tag 2) = binSyms (Li + Lk) (base tag))
    (hblank : ∀ tag j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → S.R (rg tag j) = [])
    (hflag : v.flag = xs.head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ xs.length * sharedSelectedSourceIterationCost Li Lk + 1 ∧
      Exec body (.loop (·.flag) (sharedSelectedSourceLoopBody rg src saved index localOffset tmp dst accum)) (mk v S) steps
        (mk v' { S with R := sharedSelectedSourceTraceBank S.R src saved accum Li Lk k base xs }) := by
  have hn := hreg
  regs_ne hn
  induction xs generalizing v S with
  | nil => exact ⟨v, 1, rfl, by simp, Exec.loop_false (by simpa only [List.head?_nil, Option.isSome_none, mk_var] using hflag)⟩
  | cons x xs ih =>
    obtain ⟨u₁, m₁, hu₁, hm₁, hx₁⟩ := sharedSelectedSourceReverse_exec body rg x.lo x.hi (hrg x.tag)
      src saved index localOffset tmp dst (by regs_nodup) (hsrc x.tag) (hsaved x.tag)
      hindexReg hlocalReg (hsep x.tag) ‹src ≠ dst›.symm ‹saved ≠ dst›.symm
      accum ‹src ≠ accum›.symm ‹saved ≠ accum›.symm ‹dst ≠ accum›.symm
      Li Lk x.index k (base x.tag) x.offset (hfit x (by simp)).1 hk (hfit x (by simp)).2 x.enabled
      (gatedSelectedSourceWords Li Lk xs) v S
      (by simpa [gatedSelectedSourceWords, GatedSelectedSourceChoice.word, gatedSelectedSourceRecord, List.append_assoc] using hraw)
      houtput hindex hlocal htmp (hstride x.tag) (hbase x.tag) (hblank x.tag)
    let B : Stacks T A := { S with R := sharedSelectedSourceReverseBank S.R src saved accum Li Lk x.index k (base x.tag) x.offset x.lo x.hi x.enabled (gatedSelectedSourceWords Li Lk xs) }
    have hc : B.R src = gatedSelectedSourceWords Li Lk xs := by
      simp [B, sharedSelectedSourceReverseBank, ‹src ≠ accum›, ‹src ≠ saved›]
    have hkeep (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) (hc : j ≠ accum) : B.R j = S.R j := by
      simp [B, sharedSelectedSourceReverseBank, hs, ha, hc]
    have hrkeep (tag : Fin 4) (j : Fin 13) : B.R (rg tag j) = S.R (rg tag j) :=
      hkeep _ (hsrc tag j).symm (hsaved tag j).symm (hacc tag j).symm
    let u₂ := { u₁ with flag := xs.head?.isSome }
    have hp : (peekR src : Act T Q A U).run (mk u₁ B) = mk u₂ B := by
      simp only [peekR_run, hc, gatedSelectedSourceWords_head]; rfl
    obtain ⟨v', m₂, hu₂, hm₂, hx₂⟩ := ih (fun y hy => hfit y (by simp [hy])) u₂ B hc
      ((hkeep index ‹src ≠ index›.symm ‹saved ≠ index›.symm ‹index ≠ accum›).trans hindex)
      ((hkeep localOffset ‹src ≠ localOffset›.symm ‹saved ≠ localOffset›.symm ‹localOffset ≠ accum›).trans hlocal)
      ((hkeep tmp ‹src ≠ tmp›.symm ‹saved ≠ tmp›.symm ‹tmp ≠ accum›).trans htmp)
      ((hkeep dst ‹src ≠ dst›.symm ‹saved ≠ dst›.symm ‹dst ≠ accum›).trans houtput)
      (fun tag => (hrkeep tag 1).trans (hstride tag)) (fun tag => (hrkeep tag 2).trans (hbase tag))
      (fun tag j h0 h1 h2 h3 => (hrkeep tag j).trans (hblank tag j h0 h1 h2 h3)) rfl
    refine ⟨v', (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      unfold sharedSelectedSourceIterationCost at *
      omega
    · exact Exec.cast (Exec.loop_true
        (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag)
        (Exec.seq hx₁ (hp ▸ Exec.act (body := body) _ (mk u₁ B))) hx₂) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
