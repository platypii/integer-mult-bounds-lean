module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceReverseStep

/-! Iterate directly over raw activity bits. The activity tape supplies both
loop termination and branch selection; every consumed bit is archived. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceLoopBody (rg : Fin 12 → Fin T)
    (zr : BinaryZeroReg → Fin T) (src saved dst : Fin T) : Pr P T Q A U :=
  .seq (optionalAffineSourceReverseStepProgram rg zr src saved dst) (.act (peekR src))

def optionalAffineSourceTraceBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 12 → Fin T) (src saved dst : Fin T) (Li Lk i k o : ℕ) :
    List Bool → Fin T → List (Fin (A + 4))
  | [] => R
  | b :: rest => optionalAffineSourceTraceBank
      (optionalAffineSourceReverseStepBank R rg src saved dst Li Lk i k o b (rest.map bitSymbol))
      rg src saved dst Li Lk (i + 1) k o rest

def optionalAffineSourceIterationCost (Lw Li Lk : ℕ) :=
  optionalAffineSourceFrameCost Lw Li Lk + 1 + (4 * Li + 5) + (2 * (Li + Lk + 3) + 2) + 2

theorem optionalAffineSourceLoop_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (src saved dst : Fin T) (hss : src ≠ saved)
    (hsrcRg : ∀ r, src ≠ rg r) (hsavedRg : ∀ r, saved ≠ rg r)
    (hsrcZr : ∀ r, src ≠ zr r) (hsavedZr : ∀ r, saved ≠ zr r)
    (hdsep : ∀ r, dst ≠ rg r) (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (hdZr : ∀ r, dst ≠ zr r) (hzIndex : ∀ r, zr r ≠ rg 0)
    (Lw Li Lk i k o : ℕ) (input : List Bool) (hwidth : Li + Lk < 2 ^ Lw)
    (hk : k < 2 ^ Lk) (hi : i + input.length ≤ 2 ^ Li)
    (hfit : ∀ j < input.length, (i + j) * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = input.map bitSymbol)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = [])
    (hflag : v.flag = input.head?.isSome) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ input.length * optionalAffineSourceIterationCost Lw Li Lk + 1 ∧
      Exec body (.loop (·.flag) (optionalAffineSourceLoopBody rg zr src saved dst)) (mk v S) steps
        (mk v' { S with R := optionalAffineSourceTraceBank S.R rg src saved dst Li Lk i k o input }) := by
  induction input generalizing i v S with
  | nil =>
    exact ⟨v, 1, rfl, by simp, Exec.loop_false (by simpa only [List.head?_nil, Option.isSome_none, mk_var] using hflag)⟩
  | cons b rest ih =>
    obtain ⟨u₁, m₁, hu₁, hm₁, hx₁⟩ := optionalAffineSourceReverseStep_exec body rg hrg zr hzr hdst
      src saved hss hsrcRg hsavedRg hsrcZr hsavedZr dst hdsep hdsrc hdsaved
      Lw Li Lk i k o hwidth (by simp only [List.length_cons] at hi; omega) hk
      (by simpa using hfit 0 (by simp)) b (rest.map bitSymbol) v S
      (by simpa using hsrc) hindex hstride hoffset hblank hwidthInput hunary hzeroScratch
    let B : Stacks T A := { S with R := optionalAffineSourceReverseStepBank S.R rg src saved dst Li Lk i k o b (rest.map bitSymbol) }
    have hc : B.R src = rest.map bitSymbol := by
      simp [B, optionalAffineSourceReverseStepBank, (hsrcRg 0), hdsrc.symm, hss]
    let u₂ := { u₁ with flag := rest.head?.isSome }
    have hpeek : (peekR src : Act T Q A U).run (mk u₁ B) = mk u₂ B := by
      simp only [peekR_run, hc, List.head?_map, Option.isSome_map]; rfl
    have hnext (r : Fin 12) (hr : r ≠ 0) : B.R (rg r) = S.R (rg r) := by
      simp [B, optionalAffineSourceReverseStepBank, hrg.eq_iff, hr,
        (hdsep r).symm, (hsrcRg r).symm, (hsavedRg r).symm]
    have hznext (r : BinaryZeroReg) : B.R (zr r) = S.R (zr r) := by
      simp [B, optionalAffineSourceReverseStepBank, hzIndex r,
        (hdZr r).symm, (hsrcZr r).symm, (hsavedZr r).symm]
    obtain ⟨v', m₂, hu₂, hm₂, hx₂⟩ := ih (i + 1)
      (by simp only [List.length_cons] at hi; omega)
      (by intro j hj; simpa only [Nat.add_assoc, Nat.add_comm 1] using hfit (j + 1) (by simp; omega))
      u₂ B hc (by simp [B, optionalAffineSourceReverseStepBank])
      ((hnext 1 (by decide)).trans hstride) ((hnext 2 (by decide)).trans hoffset)
      (fun r h0 h1 h2 => (hnext r h0).trans (hblank r h0 h1 h2))
      ((hznext .width).trans hwidthInput) ((hznext .unary).trans hunary)
      (fun r => (hznext (.scratch r)).trans (hzeroScratch r)) rfl
    refine ⟨v', (m₁ + 1) + m₂ + 1, hu₂.trans hu₁, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      unfold optionalAffineSourceIterationCost at *
      omega
    · exact Exec.cast (Exec.loop_true
        (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag)
        (Exec.seq hx₁ (hpeek ▸ Exec.act (body := body) _ (mk u₁ B))) hx₂) (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
