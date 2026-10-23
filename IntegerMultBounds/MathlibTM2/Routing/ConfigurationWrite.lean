module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationBatch
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankLoad
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-!
# Executed serialization of a fixed metadata bank

Copies each live word and a framing separator into the configuration stream.
All sources and both temporary tapes are restored. The field list is fixed code;
word lengths and values remain live data. Repeated destination prepending lets
successive instruction frames be assembled without another scratch bank.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def delimitedConfigurationWrite (delimiter : Fin (A + 4)) (dst tmp work : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | src :: fields => .seq (delimitedConfigurationWrite delimiter dst tmp work fields)
      (.seq (.act (.push (.rt dst) (fun _ => delimiter) .done)) (bcopy src dst tmp work))

def configurationWrite (dst tmp work : Fin T) (fields : List (Fin T)) : Pr P T Q A U :=
  delimitedConfigurationWrite separator dst tmp work fields

def configurationWriteCost (R : Fin T → List (Fin (A + 4))) : List (Fin T) → ℕ
  | [] => 1
  | src :: fields => configurationWriteCost R fields + (6 * (R src).length + 7)

/-- Serialize a bank with full frame restoration, including arbitrary existing
configuration contents as a suffix. -/
theorem delimitedConfigurationWrite_exec (body : P → Pr P T Q A U) (delimiter : Fin (A + 4)) (dst tmp work : Fin T)
    (hreg : [dst, tmp, work].Nodup) (fields : List (Fin T))
    (hfields : ∀ src ∈ fields, src ≠ dst ∧ src ≠ tmp ∧ src ≠ work)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (delimitedConfigurationWrite delimiter dst tmp work fields) (mk v S) (configurationWriteCost S.R fields)
        (mk v' { S with R := Function.update S.R dst (delimitedBankFrames delimiter (fields.map (fun j => (j, S.R j))) ++ S.R dst) }) := by
  induction fields generalizing v S with
  | nil =>
    refine ⟨v, rfl, ?_⟩
    simpa [delimitedConfigurationWrite, configurationWriteCost, delimitedBankFrames] using
      Exec.act (body := body) .done (mk v S)
  | cons src fields ih =>
    have hn := hreg
    regs_ne hn
    have hsrc := hfields src (by simp)
    obtain ⟨v₁, hu₁, he₁⟩ := ih (fun x hx => hfields x (by simp [hx])) v S htmp hwork
    let S₁ : Stacks T A :=
      { S with R := Function.update S.R dst (delimitedBankFrames delimiter (fields.map (fun j => (j, S.R j))) ++ S.R dst) }
    let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (delimiter :: S₁.R dst) }
    have hp : (Action.push (.rt dst) (fun _ => delimiter) .done : Act T Q A U).run (mk v₁ S₁) =
        mk v₁ S₂ := by simp [Action.run, update_rt, S₂]
    have hs₂ : S₂.R src = S.R src := by simp [S₂, S₁, hsrc.1]
    obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec body (a := src) (c := dst) (t₁ := tmp) (t₂ := work)
      (by simpa using List.nodup_cons.mpr ⟨by simpa using hsrc, hreg⟩) v₁ S₂
      (by simp [S₂, S₁, Ne.symm ‹dst ≠ tmp›, htmp])
      (by simp [S₂, S₁, Ne.symm ‹dst ≠ work›, hwork])
    have hfinal : Function.update S₂.R dst (S₂.R src ++ S₂.R dst) =
        Function.update S.R dst (delimitedBankFrames delimiter ((src :: fields).map (fun j => (j, S.R j))) ++ S.R dst) := by
      rw [hs₂]
      funext j
      by_cases hj : j = dst
      · subst j
        simp [S₂, S₁, delimitedBankFrames, List.map_cons, List.append_assoc]
      · simp [S₂, S₁, hj]
    refine ⟨v₂, hu₂.trans hu₁, ?_⟩
    refine Exec.cast (Exec.seq he₁ (Exec.seq (hp ▸ Exec.act (body := body) _ (mk v₁ S₁)) he₂)) ?_ ?_
    · rw [hs₂, configurationWriteCost]
      omega
    · simp only [hfinal]
      rfl

theorem delimitedBankFrames_separator (R : Fin T → List (Fin (A + 4))) (fields : List (Fin T)) :
    delimitedBankFrames separator (fields.map (fun j => (j, R j))) = configurationWords (fields.map R) := by
  induction fields with
  | nil => rfl
  | cons j fields ih => simp only [List.map_cons, delimitedBankFrames, configurationWords, ih]

theorem configurationWrite_exec (body : P → Pr P T Q A U) (dst tmp work : Fin T)
    (hreg : [dst, tmp, work].Nodup) (fields : List (Fin T))
    (hfields : ∀ src ∈ fields, src ≠ dst ∧ src ≠ tmp ∧ src ≠ work)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (configurationWrite dst tmp work fields) (mk v S) (configurationWriteCost S.R fields)
        (mk v' { S with R := Function.update S.R dst (configurationWords (fields.map S.R) ++ S.R dst) }) := by
  obtain ⟨v', hu, he⟩ := delimitedConfigurationWrite_exec body separator dst tmp work hreg fields hfields v S htmp hwork
  rw [delimitedBankFrames_separator] at he
  exact ⟨v', hu, he⟩

/-- The same linear bound holds for any delimiter, including nested frames. -/
theorem configurationWriteCost_delimited_le (delimiter : Fin (A + 4))
    (R : Fin T → List (Fin (A + 4))) (fields : List (Fin T)) :
    configurationWriteCost R fields ≤
      7 * (delimitedBankFrames delimiter (fields.map (fun j => (j, R j)))).length + 1 := by
  induction fields with
  | nil => simp [configurationWriteCost, delimitedBankFrames]
  | cons src fields ih =>
    simp only [configurationWriteCost, List.map_cons, delimitedBankFrames, List.length_append, List.length_cons]
    omega

/-- Serialization costs at most seven steps per framed input symbol, plus one. -/
theorem configurationWriteCost_le (R : Fin T → List (Fin (A + 4))) (fields : List (Fin T)) :
    configurationWriteCost R fields ≤ 7 * (configurationWords (fields.map R)).length + 1 := by
  simpa only [delimitedBankFrames_separator] using
    configurationWriteCost_delimited_le separator R fields

end IntegerMultBounds.MathlibTM2.Routing
