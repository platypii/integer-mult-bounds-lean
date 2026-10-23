module

public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreBank

/-! Three fixed loader tapes outside an arbitrary core. Their number is independent
of geometry and schedule length; every core scratch tape can be loaded as empty. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {N Q A : ℕ} {P U : Type}

def framedCoreEmbed (N : ℕ) (j : Fin N) : Fin (N + 3) := Fin.castAdd 3 j

def framedCoreAux (N : ℕ) (i : Fin 3) : Fin (N + 3) := ⟨N + i.val, by omega⟩

/-- Extend a framed core while keeping the same three outer loader roles. -/
def framedCoreExtend (N extra : ℕ) (j : Fin (N + 3)) : Fin (N + extra + 3) :=
  if h : j.val < N then ⟨j.val, by omega⟩ else ⟨extra + j.val, by have := j.isLt; omega⟩

theorem framedCoreExtend_injective (N extra : ℕ) : Function.Injective (framedCoreExtend N extra) := by
  intro i j he
  have hv := congrArg (fun x : Fin (N + extra + 3) => x.val) he
  by_cases hi : i.val < N <;> by_cases hj : j.val < N
  all_goals simp only [framedCoreExtend, hi, hj, dite_true, dite_false] at hv
  all_goals apply Fin.ext; omega

@[simp] theorem framedCoreExtend_core (N extra : ℕ) (j : Fin N) :
    framedCoreExtend N extra (framedCoreEmbed N j) =
      framedCoreEmbed (N + extra) (Fin.castAdd extra j) := by
  unfold framedCoreExtend
  split
  · rfl
  · rename_i h
    exact (h j.isLt).elim

@[simp] theorem framedCoreExtend_aux (N extra : ℕ) (j : Fin 3) :
    framedCoreExtend N extra (framedCoreAux N j) = framedCoreAux (N + extra) j := by
  unfold framedCoreExtend
  split
  · rename_i h
    change N + j.val < N at h
    omega
  · apply Fin.ext
    change extra + (N + j.val) = N + extra + j.val
    omega

theorem framedCoreEmbed_injective (N : ℕ) : Function.Injective (framedCoreEmbed N) := by
  intro i j he
  have hv := congrArg (fun x : Fin (N + 3) => x.val) he
  exact Fin.ext hv

theorem framedCoreAux_injective (N : ℕ) : Function.Injective (framedCoreAux N) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  change N + i.val = N + j.val at hv
  omega

theorem framedCoreEmbed_aux (N : ℕ) (j : Fin N) (i : Fin 3) :
    framedCoreEmbed N j ≠ framedCoreAux N i := by
  intro he
  have hv := congrArg Fin.val he
  change j.val = N + i.val at hv
  omega

theorem framedCoreAux_nodup (N : ℕ) :
    [framedCoreAux N 0, framedCoreAux N 1, framedCoreAux N 2].Nodup := by
  simp [List.nodup_cons, (framedCoreAux_injective N).eq_iff]

theorem framedCoreStream_nodup (N : ℕ) (str : Fin N) :
    [framedCoreAux N 0, framedCoreAux N 2, framedCoreEmbed N str].Nodup := by
  have h0 := framedCoreEmbed_aux N str 0
  have h2 := framedCoreEmbed_aux N str 2
  simp_all [List.nodup_cons, (framedCoreAux_injective N).eq_iff, ne_comm]

def framedCoreLoadProgram (str : Fin N) (delimiter : Fin (A + 4)) (scan : Fin (A + 4) → Bool) :
    Pr P (N + 3) Q A U :=
  delimitedBankLoad (framedCoreAux N 0) (framedCoreAux N 1) (framedCoreAux N 2) delimiter scan
    (framedCoreDestinations (framedCoreEmbed N) str)

/-- Actual full-core loading uses fixed code and establishes every non-stream
word, including empty scratch, from one framed metadata stream. -/
theorem framedCoreLoad_exec (body : P → Pr P (N + 3) Q A U)
    (str : Fin N) (delimiter : Fin (A + 4)) (scan : Fin (A + 4) → Bool)
    (hstop : scan delimiter = false) (words : Fin N → List (Fin (A + 4)))
    (hword : ∀ j, j ≠ str → ∀ x ∈ words j, scan x = true)
    (rest : List (Fin (A + 4))) (v : HS (N + 3) Q A U) (S : Stacks (N + 3) A)
    (hinput : S.R (framedCoreAux N 0) =
      delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed N) str words) ++ rest)
    (htmp : S.R (framedCoreAux N 1) = [])
    (hblank : ∀ j, j ≠ str → S.R (framedCoreEmbed N j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (framedCoreLoadProgram str delimiter scan) (mk v S)
        (delimitedBankLoadCost (framedCoreJobs (framedCoreEmbed N) str words))
        (mk v' { S with R := delimitedBankLoaded (framedCoreAux N 0) (framedCoreAux N 1) (framedCoreAux N 2) delimiter rest (framedCoreJobs (framedCoreEmbed N) str words) S.R }) := by
  have hx := delimitedBankLoad_exec body (framedCoreAux N 0) (framedCoreAux N 1) (framedCoreAux N 2)
    (framedCoreAux_nodup N) delimiter scan hstop (framedCoreJobs (framedCoreEmbed N) str words)
    (by rw [framedCoreJobs_destinations]; exact framedCoreDestinations_nodup _ (framedCoreEmbed_injective N) str)
    (by intro job hj; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hj
        exact ⟨framedCoreEmbed_aux N j 0, framedCoreEmbed_aux N j 1, framedCoreEmbed_aux N j 2⟩)
    (by intro job hj; obtain ⟨j, hmem, rfl⟩ := List.mem_map.mp hj
        exact hword j ((mem_framedCoreRegisters str j).mp hmem))
    rest v S hinput htmp
    (by intro job hj; obtain ⟨j, hmem, rfl⟩ := List.mem_map.mp hj
        exact hblank j ((mem_framedCoreRegisters str j).mp hmem))
  simpa only [framedCoreJobs_destinations, framedCoreLoadProgram] using hx

/-- The concrete loader's core projection is the declared bank, with the live
stream substituted. This single identity transports generated-call readiness. -/
theorem framedCoreLoad_bank (str : Fin N) (delimiter : Fin (A + 4))
    (rest : List (Fin (A + 4))) (words : Fin N → List (Fin (A + 4)))
    (bank : Fin (N + 3) → List (Fin (A + 4))) :
    delimitedBankLoaded (framedCoreAux N 0) (framedCoreAux N 1) (framedCoreAux N 2) delimiter rest
      (framedCoreJobs (framedCoreEmbed N) str words) bank ∘ framedCoreEmbed N =
      Function.update words str (bank (framedCoreEmbed N str)) :=
  framedCoreLoaded (framedCoreEmbed N) (framedCoreEmbed_injective N) str _ _ _
    (fun j => framedCoreEmbed_aux N j 0) (fun j => framedCoreEmbed_aux N j 1)
    (fun j => framedCoreEmbed_aux N j 2) delimiter rest words bank

/-- All stack-level readiness hypotheses can be transported through one exact
core-bank identity; left stacks and external input/output remain the caller's. -/
theorem framedCoreLoad_stack (str : Fin N) (delimiter : Fin (A + 4))
    (rest : List (Fin (A + 4))) (words : Fin N → List (Fin (A + 4)))
    (S : Stacks (N + 3) A) :
    embStk (framedCoreEmbed N)
      { S with R := delimitedBankLoaded (framedCoreAux N 0) (framedCoreAux N 1) (framedCoreAux N 2) delimiter rest (framedCoreJobs (framedCoreEmbed N) str words) S.R } =
      { embStk (framedCoreEmbed N) S with R := Function.update words str (S.R (framedCoreEmbed N str)) } := by
  have h := framedCoreLoad_bank str delimiter rest words S.R
  simpa only [embStk] using congrArg
    (fun R => ({ embStk (framedCoreEmbed N) S with R := R } : Stacks N A)) h

end IntegerMultBounds.MathlibTM2.Routing
