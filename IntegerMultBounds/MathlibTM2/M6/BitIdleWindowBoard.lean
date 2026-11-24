module

public import IntegerMultBounds.MathlibTM2.M6.BitCompiledIdleRecord
public import IntegerMultBounds.MathlibTM2.M6.BitIdleParentArchive

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- Allocate a dispatch bank for each owner, sharing tape 24 with the owner
and reserving two blank window tapes for header setup. -/
private theorem allocateIdleCallerWindow {Job : Type} [Fintype Job] {B : ℕ}
    (owner : Job ↪ Fin B) (N : ℕ) :
    ∃ (H : ℕ) (fan : Fin B ↪ Fin H) (raw : Job → Fin 72 ↪ Fin H)
      (origin : Fin H → Option (Σ _ : Job, Fin (72+N))),
      (∀ j, raw j 24 = fan (owner j)) ∧
      (∀ i j, i ≠ j → ∀ k l, raw i k ≠ raw j l) ∧
      (∃ a b, a ≠ b ∧ origin a = none ∧ origin b = none) ∧
      ∀ (c : CutoffNodeInput) j (k : Fin 72), k ≠ 24 →
        let seed := idleWindowSeed origin (fun _ => idleDispatchStacks N c.w c.idleWidth c.root.width.size c.cutoff)
        seed.L (raw j k) = [] ∧ seed.R (raw j k) = idleDispatchWord c.w c.idleWidth c.root.width.size c.cutoff k.val := by
  let base := Fin.castAddEmb N (n := 72)
  obtain ⟨H,fan,place,shared,_,apart,source,init⟩ := idleWorkspace (A := prime)
    (fun _ : Job => 72+N) owner (fun _ => base 24)
  let keep := Fin.castAddEmb 2 (n := H)
  let origin (k : Fin (H+2)) : Option (Σ _ : Job, Fin (72+N)) := Fin.addCases source (fun _ => none) k
  refine ⟨H+2,fan.trans keep,fun j => (base.trans (place j)).trans keep,origin,
    fun j => congrArg keep (shared j),fun i j ne k l => keep.injective.ne (apart i j ne _ _),?_,?_⟩
  · refine ⟨Fin.natAdd H (0 : Fin 2),Fin.natAdd H (1 : Fin 2),?_,?_,?_⟩
    · exact (Fin.natAddEmb H).injective.ne (by decide : (0 : Fin 2) ≠ 1)
    all_goals simp [origin]
  · intro c j k ne seed
    have entry := init (fun _ => idleDispatchStacks N c.w c.idleWidth c.root.width.size c.cutoff)
      j (base k) (base.injective.ne ne)
    simpa [seed,idleWindowSeed,idleDispatchStacks,base,origin,keep,Function.Embedding.trans_apply] using entry

/-- Place each occurrence's dispatch registers beside the same six role words.
The setup program runs once for the window and preserves the scratch banks. -/
theorem prepareIdleCallerBoards {Job P U : Type} [Fintype Job] {B N Q : ℕ}
    (owner : Job ↪ Fin B)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q) :
    ∃ (H : ℕ) (fan : Fin B ↪ Fin H) (raw : Job → Fin 72 ↪ Fin H)
      (origin : Fin H → Option (Σ _ : Job, Fin (72+N))),
    (∀ j, raw j 24 = fan (owner j)) ∧ (∀ i j, i ≠ j → ∀ k l, raw i k ≠ raw j l) ∧
    ∀ {T : ℕ} (body : P → Pr P T Q prime U) (bank : Fin (H+(80+273)) ↪ Fin T) (master : Fin 12 → Fin T)
      (_ : ∀ i j, bank i ≠ master j) (scratch : Job → Fin 35 ↪ Fin T)
      (_ : ∀ j k a, bank a ≠ scratch j k),
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
          (∀ j, IdleDispatchReady ((Fin.castLEEmb (by decide : 72 ≤ 113)).trans (board j))
            c.w c.idleWidth c.root.width.size c.cutoff F) ∧
          (∀ j k, F.R (board j (idleRolePorts k)) = (Routines.hdr (role c.node 142080) k).map bitSymbol) ∧
          (∀ j, F.L (window j) = seed.L j ∧ F.R (window j) = seed.R j) ∧
          ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨H,fan,raw,origin,payload,separate,free,seedAt⟩ := allocateIdleCallerWindow owner N
  refine ⟨H,fan,raw,origin,payload,separate,?_⟩
  intro T body bank master apart scratch outside window
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
  have rawAt (j : Job) (k : Fin 72) : board j (k.castLE (by decide)) = window (raw j k) := by
    change board j ((k.castAdd 6).castAdd 35) = _
    simp [board,shared,appendPorts]
  obtain ⟨code,rate,run⟩ := prepareIdleWindowRoles origin free body bank master apart capacity
  refine ⟨board,code,rate,rawAt,?_,fun j l k => (field j k).trans (field l k).symm,?_⟩
  · intro j k
    simp [board,appendPorts]
  · intro c u S words fresh seed
    obtain ⟨z,F,t,exec,user,paid,live,roles,frame⟩ := run c u S words fresh
    refine ⟨z,F,t,exec,user,paid,?_,fun j k => field j k ▸ roles k,live,frame⟩
    intro j k ne
    change F.L (board j (k.castLE (by decide))) = _ ∧ F.R (board j (k.castLE (by decide))) = _
    rw [rawAt]
    exact ⟨(live _).1.trans (seedAt c j k ne).1,(live _).2.trans (seedAt c j k ne).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
