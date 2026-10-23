module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateRecord
public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoad

/-! Load a physical coordinate and activity from a self-delimiting input
record. The full input is archived while the fixed decoder emits its raw record. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

structure SourceCoordinateSetup (rg : Fin 21 → Fin T) (Li Lk low high k : ℕ)
    (S : Stacks T A) : Prop where
  low : S.R (rg 1) = binSyms (Li + Lk) low
  high : S.R (rg 2) = binSyms (Li + Lk) high
  stride : S.R (rg 3) = binSyms Lk k
  zero : S.R (rg 4) = binSyms (Li + Lk) 0
  width : (S.R (rg 5)).length = Li
  blank : ∀ j ∈ ([0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 20] : List (Fin 21)), S.R (rg j) = []

def sourceCoordinateInputRecord (Li Lk q : ℕ) (enabled : Bool) : List (Fin (A + 4)) :=
  binSyms (Li + Lk) q ++ separator :: (binSyms 1 enabled.toNat ++ [separator])

def sourceCoordinateLoadProgram (rg : Fin 21 → Fin T) (src saved tmp : Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram src saved (rg 0) (rg 20) tmp) (sourceCoordinateRecordProgram rg)

theorem sourceCoordinateLoaded_ready
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg) (src saved : Fin T)
    (hsrc : ∀ j, src ≠ rg j) (hsaved : ∀ j, saved ≠ rg j)
    (Li Lk q low high k : ℕ) (enabled : Bool) (rest : List (Fin (A + 4)))
    (S : Stacks T A) (setup : SourceCoordinateSetup rg Li Lk low high k S) :
    SourceCoordinateData rg Li Lk q low high k enabled
      { S with R := selectorRunLoaded S.R src saved (rg 0) (rg 20) (binSyms (Li + Lk) q) (binSyms 1 enabled.toNat) rest } := by
  have hkeep (j : Fin 21) (h0 : j ≠ 0) (h20 : j ≠ 20) :
      selectorRunLoaded S.R src saved (rg 0) (rg 20) (binSyms (Li + Lk) q)
        (binSyms 1 enabled.toNat) rest (rg j) = S.R (rg j) :=
    selectorRunLoaded_keep S.R src saved (rg 0) (rg 20) (rg j) _ _ rest
      (hsrc j).symm (hsaved j).symm (hrg.ne h0) (hrg.ne h20)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [selectorRunLoaded, hrg.eq_iff]
  · exact (hkeep 1 (by decide) (by decide)).trans setup.low
  · exact (hkeep 2 (by decide) (by decide)).trans setup.high
  · exact (hkeep 3 (by decide) (by decide)).trans setup.stride
  · exact (hkeep 4 (by decide) (by decide)).trans setup.zero
  · simpa only [hkeep 5 (by decide) (by decide)] using setup.width
  · cases enabled <;> simp [selectorRunLoaded, binSyms]
  · intro j hj
    have h0 : j ≠ 0 := by intro he; subst j; simp at hj
    have h20 : j ≠ 20 := by intro he; subst j; simp at hj
    dsimp only
    rw [hkeep j h0 h20]
    exact setup.blank j (by simp only [List.mem_cons] at hj ⊢; tauto)

theorem sourceCoordinateLoad_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg) (src saved tmp : Fin T)
    (hreg : [src, saved, tmp].Nodup)
    (hsrc : ∀ j, src ≠ rg j) (hsaved : ∀ j, saved ≠ rg j) (htmp : ∀ j, tmp ≠ rg j)
    (Li Lk q low high k : ℕ) (enabled : Bool)
    (hq : q < 2 ^ (Li + Lk)) (hlow : low < 2 ^ (Li + Lk)) (hhigh : high < 2 ^ (Li + Lk))
    (hk : k < 2 ^ Lk) (hk0 : 0 < k)
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (setup : SourceCoordinateSetup rg Li Lk low high k S)
    (hraw : S.R src = sourceCoordinateInputRecord Li Lk q enabled ++ rest) (htmpBlank : S.R tmp = []) :
    let B := selectorRunLoaded S.R src saved (rg 0) (rg 20) (binSyms (Li + Lk) q) (binSyms 1 enabled.toNat) rest
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ 4 * (Li + Lk) + 16 + sourceCoordinateRecordCost Li Lk ∧
      Exec body (sourceCoordinateLoadProgram rg src saved tmp) (mk v S) steps
        (mk v' { S with R := Function.update B (rg 19) ((sourceCoordinateChoice q low high k enabled).word Li Lk ++ B (rg 19)) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, hx₁⟩ := selectorRunLoad_exec body src saved (rg 0) (rg 20) tmp
    (by simp [List.nodup_cons, hsrc, hsaved, htmp, hrg.eq_iff, ne_comm,
      ‹src ≠ saved›, ‹src ≠ tmp›, ‹saved ≠ tmp›])
    (Li + Lk) 1 q enabled.toNat rest v S
    (by simpa [sourceCoordinateInputRecord, List.append_assoc] using hraw)
    (setup.blank 0 (by decide)) (setup.blank 20 (by decide)) htmpBlank
  let G : Stacks T A := { S with R := selectorRunLoaded S.R src saved (rg 0) (rg 20) (binSyms (Li + Lk) q) (binSyms 1 enabled.toNat) rest }
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := sourceCoordinateRecord_exec body rg hrg Li Lk q low high k enabled
    hq hlow hhigh hk hk0 v₁ G (sourceCoordinateLoaded_ready rg hrg src saved hsrc hsaved Li Lk q low high k enabled rest S setup)
  exact ⟨v₂, (4 * (Li + Lk) + 4 * 1 + 12) + m₂, hu₂.trans hu₁, by omega, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
