module

public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceTrace

/-! Generate a complete source profile from raw tagged coordinates, then rewind
the raw input and reverse the accumulator. Only the profile output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def gatedSelectedSourceGenerateProgram (rg : Fin 4 → Fin 13 → Fin T)
    (zr : BinaryZeroReg → Fin T) (src saved index localOffset tmp dst accum out : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src))
    (.seq (.loop (·.flag) (gatedSelectedSourceLoopBody rg zr src saved index localOffset tmp dst accum))
      (.seq (moveR saved src id) (moveR accum out id)))

theorem gatedSelectedSourceGenerate_clean (R : Fin T → List (Fin (A + 4)))
    (src saved accum out : Fin T) (hreg : [src, saved, accum, out].Nodup)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice)
    (hraw : R src = gatedSelectedSourceWords Li Lk xs)
    (harchive : R saved = []) (haccum : R accum = []) :
    let G := gatedSelectedSourceClosedBank R src saved accum Li Lk k base xs
    let H := movedR G saved src id (G saved)
    movedR H accum out id (H accum) =
      Function.update R out (gatedSelectedSourceProfileWord Li Lk k base xs ++ R out) := by
  have hn := hreg
  regs_ne hn
  dsimp only
  funext j
  by_cases hsJ : j = src <;> by_cases haJ : j = saved <;> by_cases hcJ : j = accum <;> by_cases hoJ : j = out <;>
    simp_all [movedR, gatedSelectedSourceClosedBank]
  simp_all [eq_comm]

theorem gatedSelectedSourceGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 4 → Fin 13 → Fin T) (hrg : ∀ tag, Function.Injective (rg tag))
    (src saved index localOffset tmp dst accum out : Fin T)
    (hreg : [src, saved, index, localOffset, tmp, dst, accum, out].Nodup)
    (hsrc : ∀ tag j, src ≠ rg tag j) (hsaved : ∀ tag j, saved ≠ rg tag j)
    (hindexReg : ∀ tag, rg tag 0 = index) (hlocalReg : ∀ tag, rg tag 3 = localOffset)
    (hsep : ∀ tag j, dst ≠ rg tag j) (hacc : ∀ tag j, accum ≠ rg tag j)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = dst)
    (hz5 : ∀ tag j, zr j ≠ rg tag 5)
    (hsrcZr : ∀ j, src ≠ zr j) (hsavedZr : ∀ j, saved ≠ zr j)
    (hzIndex : ∀ j, zr j ≠ index) (hzLocal : ∀ j, zr j ≠ localOffset)
    (hzAcc : ∀ j, accum ≠ zr j)
    (Lw Li Lk k : ℕ) (hwidth : Li + Lk < 2 ^ Lw) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) (hk : k < 2 ^ Lk)
    (hfit : ∀ x ∈ xs, x.index < 2 ^ Li ∧ x.position k base < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = gatedSelectedSourceWords Li Lk xs)
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (houtput : S.R dst = [])
    (hstride : ∀ tag, S.R (rg tag 1) = binSyms Lk k)
    (hbase : ∀ tag, S.R (rg tag 2) = binSyms (Li + Lk) (base tag))
    (hblank : ∀ tag j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → S.R (rg tag j) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ j, S.R (zr (.scratch j)) = [])
    (harchive : S.R saved = []) (haccum : S.R accum = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ xs.length * gatedSelectedSourceIterationCost Lw Li Lk +
        2 * (xs.length * (Li + (Li + Lk) + 5)) + 2 * (xs.length * (Li + Lk + 3)) + 6 ∧
      Exec body (gatedSelectedSourceGenerateProgram rg zr src saved index localOffset tmp dst accum out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (gatedSelectedSourceProfileWord Li Lk k base xs ++ S.R out) }) := by
  have hn := hreg
  regs_ne hn
  let u := { v with flag := xs.head?.isSome }
  have hp : (peekR src : Act T Q A U).run (mk v S) = mk u S := by
    simp only [peekR_run, hraw, gatedSelectedSourceWords_head]; rfl
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := gatedSelectedSourceLoop_exec body rg hrg
    src saved index localOffset tmp dst accum (by regs_nodup) hsrc hsaved hindexReg hlocalReg hsep hacc
    zr hzr hdst hz5 hsrcZr hsavedZr hzIndex hzLocal hzAcc Lw Li Lk k hwidth base xs hk hfit u S hraw hindex hlocal htmp houtput hstride hbase hblank hwidthInput hunary hzeroScratch rfl
  rw [gatedSelectedSourceTrace_closed S.R src saved accum ‹src ≠ saved› ‹src ≠ accum› ‹saved ≠ accum›
    Li Lk k base xs hraw] at hx₁
  let G : Stacks T A := { S with R := gatedSelectedSourceClosedBank S.R src saved accum Li Lk k base xs }
  have hs : G.R saved = (gatedSelectedSourceWords Li Lk xs).reverse := by
    simp [G, gatedSelectedSourceClosedBank, ‹saved ≠ accum›, harchive]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) saved src ‹src ≠ saved›.symm id v₁ G
  let H : Stacks T A := { G with R := movedR G.R saved src id (G.R saved) }
  have ha : H.R accum = (gatedSelectedSourceProfileWord Li Lk k base xs).reverse := by
    simp [H, movedR, G, gatedSelectedSourceClosedBank, ‹src ≠ accum›.symm, ‹saved ≠ accum›.symm, haccum]
  obtain ⟨v₃, hu₃, hx₃⟩ := moveR_exec (body := body) accum out ‹accum ≠ out› id v₂ H
  have hf : movedR H.R accum out id (H.R accum) =
      Function.update S.R out (gatedSelectedSourceProfileWord Li Lk k base xs ++ S.R out) :=
    gatedSelectedSourceGenerate_clean S.R src saved accum out (by regs_nodup)
      Li Lk k base xs hraw harchive haccum
  have hslen : (G.R saved).length = xs.length * (Li + (Li + Lk) + 5) := by
    rw [hs, List.length_reverse, gatedSelectedSourceWords_length]
  rw [hslen] at hx₂
  rw [hf, ha, List.length_reverse, gatedSelectedSourceProfileWord_length] at hx₃
  exact ⟨v₃, 1 + (m₁ + ((2 * (xs.length * (Li + (Li + Lk) + 5)) + 2) +
      (2 * (xs.length * (Li + Lk + 3)) + 2))), hu₃.trans (hu₂.trans (hu₁.trans rfl)), by omega,
    Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq hx₁ (Exec.seq hx₂ hx₃))⟩

end IntegerMultBounds.MathlibTM2.Routing
