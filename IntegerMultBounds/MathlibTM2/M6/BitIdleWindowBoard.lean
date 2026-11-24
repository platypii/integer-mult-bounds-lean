module

public import IntegerMultBounds.MathlibTM2.M6.BitCompiledIdleRecord
public import IntegerMultBounds.MathlibTM2.M6.BitIdleParentArchive

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- Place each occurrence's dispatch registers beside the same six role words.
The setup program runs once for the window and preserves the scratch banks. -/
theorem prepareIdleCallerBoards {Job P U : Type} {H N T Q : ℕ}
    (origin : Fin H → Option (Σ _ : Job, Fin (72+N)))
    (free : ∃ a b, a ≠ b ∧ origin a = none ∧ origin b = none)
    (body : P → Pr P T Q prime U) (bank : Fin (H+(80+273)) ↪ Fin T)
    (master : Fin 12 → Fin T) (apart : ∀ i j, bank i ≠ master j)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q)
    (raw : Job → Fin 72 ↪ Fin H) (scratch : Job → Fin 35 ↪ Fin T)
    (outside : ∀ j k a, bank a ≠ scratch j k) :
    let window := (Fin.castAddEmb (80+273)).trans bank
    ∃ (board : Job → Fin 113 ↪ Fin T) (code : Pr P T Q prime U) (rate : ℕ),
      (∀ j (k : Fin 72), board j (k.castLE (by decide)) = window (raw j k)) ∧
      (∀ j (k : Fin 35), board j (k.natAdd 78) = scratch j k) ∧
      (∀ j l k, board j (idleRolePorts k) = board l (idleRolePorts k)) ∧
      ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
        (∀ i, S.R (master i) = nodeSeedWords c i) →
        (∀ i, S.L (bank i) = [] ∧ S.R (bank i) = []) →
        let seed := idleWindowSeed origin (fun _ => idleDispatchStacks N c.w c.idleWidth c.root.width.size c.cutoff)
        ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (rate*c.cells) ∧
          (∀ j k, F.R (board j (idleRolePorts k)) = (Routines.hdr (role c.node 142080) k).map bitSymbol) ∧
          (∀ j, F.L (window j) = seed.L j ∧ F.R (window j) = seed.R j) ∧
          ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro window
  let dst := ((Fin.natAddEmb 38 (m := 6)).trans (Fin.castAddEmb 36)).trans (Fin.castAddEmb 273)
  let roleBank := dst.trans ((Fin.natAddEmb H).trans bank)
  let shared (j : Job) := appendPorts ((raw j).trans window) roleBank
    (fun k a => bank.injective.ne (suffixApart (dst a) (raw j k)).symm)
  have away (j : Job) (k : Fin 78) (a : Fin 35) : shared j k ≠ scratch j a := by
    induction k using Fin.addCases (m := 72) (n := 6) with
    | left k => simpa [shared, appendPorts, window] using outside j a ((raw j k).castAdd (80+273))
    | right k => simpa [shared, appendPorts, roleBank] using outside j a ((dst k).natAdd H)
  let board j := appendPorts (shared j) (scratch j) (away j)
  have field (j : Job) (k : Fin 6) : board j (idleRolePorts k) = roleBank k := by
    fin_cases k <;> rfl
  obtain ⟨code,rate,run⟩ := prepareIdleWindowRoles origin free body bank master apart capacity
  refine ⟨board,code,rate,?_,?_,fun j l k => (field j k).trans (field l k).symm,?_⟩
  · intro j k
    change board j ((k.castAdd 6).castAdd 35) = _
    simp [board,shared,appendPorts]
  · intro j k
    simp [board,appendPorts]
  · intro c u S words fresh seed
    obtain ⟨z,F,t,exec,user,paid,live,roles,frame⟩ := run c u S words fresh
    exact ⟨z,F,t,exec,user,paid,fun j k => field j k ▸ roles k,live,frame⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
