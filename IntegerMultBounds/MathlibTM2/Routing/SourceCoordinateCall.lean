module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateLoad

/-! One complete input-coordinate call, with loaded coordinate and activity
cleared afterward. Only input, rewind archive and record destination change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceCoordinateCallProgram (rg : Fin 21 → Fin T) (src saved tmp : Fin T) : Pr P T Q A U :=
  .seq (sourceCoordinateLoadProgram rg src saved tmp) (.seq (bclear (rg 0)) (bclear (rg 20)))

def sourceCoordinateCallBank (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk q low high k : ℕ) (enabled : Bool) (rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest)
    saved ((sourceCoordinateInputRecord Li Lk q enabled).reverse ++ R saved)) dst
    ((sourceCoordinateChoice q low high k enabled).word Li Lk ++ R dst)

theorem sourceCoordinateCallBank_clean (R : Fin T → List (Fin (A + 4)))
    (src saved coordinate activity dst : Fin T)
    (hreg : [src, saved, coordinate, activity, dst].Nodup)
    (Li Lk q low high k : ℕ) (enabled : Bool) (rest : List (Fin (A + 4)))
    (hc : R coordinate = []) (ha : R activity = []) :
    let B := selectorRunLoaded R src saved coordinate activity (binSyms (Li + Lk) q) (binSyms 1 enabled.toNat) rest
    let G := Function.update B dst ((sourceCoordinateChoice q low high k enabled).word Li Lk ++ B dst)
    Function.update (Function.update G coordinate []) activity [] =
      sourceCoordinateCallBank R src saved dst Li Lk q low high k enabled rest := by
  have hn := hreg
  regs_ne hn
  dsimp only
  funext j
  by_cases hs : j = src <;> by_cases haJ : j = saved <;> by_cases hcJ : j = coordinate <;>
    by_cases he : j = activity <;> by_cases hd : j = dst <;>
    simp_all [selectorRunLoaded, sourceCoordinateCallBank, sourceCoordinateInputRecord,
      List.reverse_append, List.append_assoc]

theorem sourceCoordinateCall_exec (body : P → Pr P T Q A U)
    (rg : Fin 21 → Fin T) (hrg : Function.Injective rg) (src saved tmp : Fin T)
    (hreg : [src, saved, tmp].Nodup)
    (hsrc : ∀ j, src ≠ rg j) (hsaved : ∀ j, saved ≠ rg j) (htmp : ∀ j, tmp ≠ rg j)
    (Li Lk q low high k : ℕ) (enabled : Bool)
    (hq : q < 2 ^ (Li + Lk)) (hlow : low < 2 ^ (Li + Lk)) (hhigh : high < 2 ^ (Li + Lk))
    (hk : k < 2 ^ Lk) (hk0 : 0 < k)
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (setup : SourceCoordinateSetup rg Li Lk low high k S)
    (hraw : S.R src = sourceCoordinateInputRecord Li Lk q enabled ++ rest) (htmpBlank : S.R tmp = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ sourceCoordinateRecordCost Li Lk + 6 * (Li + Lk) + 22 ∧
      Exec body (sourceCoordinateCallProgram rg src saved tmp) (mk v S) steps
        (mk v' { S with R := sourceCoordinateCallBank S.R src saved (rg 19) Li Lk q low high k enabled rest }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := sourceCoordinateLoad_exec body rg hrg src saved tmp hreg hsrc hsaved htmp
    Li Lk q low high k enabled hq hlow hhigh hk hk0 rest v S setup hraw htmpBlank
  let B := selectorRunLoaded S.R src saved (rg 0) (rg 20) (binSyms (Li + Lk) q) (binSyms 1 enabled.toNat) rest
  let G : Stacks T A := { S with R := Function.update B (rg 19) ((sourceCoordinateChoice q low high k enabled).word Li Lk ++ B (rg 19)) }
  obtain ⟨v₂, hu₂, _, hx₂⟩ := bclear_exec body (rg 0) v₁ G
  let H : Stacks T A := { G with R := Function.update G.R (rg 0) [] }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (rg 20) v₂ H
  have hc : (G.R (rg 0)).length = Li + Lk := by simp [G, B, selectorRunLoaded, hrg.eq_iff]
  have ha : (H.R (rg 20)).length = 1 := by simp [H, G, B, selectorRunLoaded, hrg.eq_iff]
  have hf : Function.update H.R (rg 20) [] = sourceCoordinateCallBank S.R src saved (rg 19) Li Lk q low high k enabled rest :=
    sourceCoordinateCallBank_clean S.R src saved (rg 0) (rg 20) (rg 19)
      (by simp [List.nodup_cons, hsrc, hsaved, hrg.eq_iff, ‹src ≠ saved›])
      Li Lk q low high k enabled rest (setup.blank 0 (by decide)) (setup.blank 20 (by decide))
  rw [hc] at hx₂
  rw [ha, hf] at hx₃
  exact ⟨v₃, m₁ + ((2 * (Li + Lk) + 2) + (2 * 1 + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
