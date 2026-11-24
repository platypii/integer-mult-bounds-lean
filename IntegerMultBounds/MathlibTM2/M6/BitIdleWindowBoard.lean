module

public import IntegerMultBounds.MathlibTM2.M6.BitScheduledIdleRecord
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
    (∀ j k, k ≠ 24 → ∀ r, raw j k ≠ fan r) ∧
      (∃ a b, a ≠ b ∧ origin a = none ∧ origin b = none) ∧
      ∀ (c : CutoffNodeInput) j (k : Fin 72), k ≠ 24 →
        let seed := idleWindowSeed origin (fun _ => idleDispatchStacks N c.w c.idleWidth c.root.width.size c.cutoff)
        seed.L (raw j k) = [] ∧ seed.R (raw j k) = idleDispatchWord c.w c.idleWidth c.root.width.size c.cutoff k.val := by
  let base := Fin.castAddEmb N (n := 72)
  obtain ⟨H,fan,place,shared,off,apart,source,init⟩ := idleWorkspace (A := prime)
    (fun _ : Job => 72+N) owner (fun _ => base 24)
  let keep := Fin.castAddEmb 2 (n := H)
  let origin (k : Fin (H+2)) : Option (Σ _ : Job, Fin (72+N)) := Fin.addCases source (fun _ => none) k
  refine ⟨H+2,fan.trans keep,fun j => (base.trans (place j)).trans keep,origin,
    fun j => congrArg keep (shared j),fun i j ne k l => keep.injective.ne (apart i j ne _ _),?_,?_,?_⟩
  · intro j k ne r
    apply keep.injective.ne
    by_cases h : r = owner j
    · subst r
      rw [← shared]
      exact (place j).injective.ne (base.injective.ne ne)
    · exact off j r h _
  · refine ⟨Fin.natAdd H (0 : Fin 2),Fin.natAdd H (1 : Fin 2),?_,?_,?_⟩
    · exact (Fin.natAddEmb H).injective.ne (by decide : (0 : Fin 2) ≠ 1)
    all_goals simp [origin]
  · intro c j k ne seed
    have entry := init (fun _ => idleDispatchStacks N c.w c.idleWidth c.root.width.size c.cutoff)
      j (base k) (base.injective.ne ne)
    simpa [seed,idleWindowSeed,idleDispatchStacks,base,origin,keep,Function.Embedding.trans_apply] using entry

/-- Place each occurrence's dispatch registers beside the same six role words.
The setup program runs once for the window. -/
theorem prepareIdleCallerBoards {Job P U : Type} [Fintype Job] {B N Q : ℕ}
    (owner : Job ↪ Fin B)
    (capacity : (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q) :
    ∃ (H : ℕ) (fan : Fin B ↪ Fin H) (raw : Job → Fin 72 ↪ Fin H)
      (origin : Fin H → Option (Σ _ : Job, Fin (72+N))),
    (∀ j, raw j 24 = fan (owner j)) ∧ (∀ i j, i ≠ j → ∀ k l, raw i k ≠ raw j l) ∧
    (∀ j k, k ≠ 24 → ∀ r, raw j k ≠ fan r) ∧
    ∀ {T : ℕ} (body : P → Pr P T Q prime U) (bank : Fin (H+(80+273)) ↪ Fin T) (master : Fin 12 → Fin T)
      (_ : ∀ i j, bank i ≠ master j),
    let window := (Fin.castAddEmb (80+273)).trans bank
    ∃ (board : Job → Fin 78 ↪ Fin T) (code : Pr P T Q prime U) (rate : ℕ),
      (∀ j (k : Fin 72), board j (k.castAdd 6) = window (raw j k)) ∧
      (∀ j l k, board j ((k : Fin 6).natAdd 72) = board l (k.natAdd 72)) ∧
      (∀ j (k : Fin 6) r, board j (k.natAdd 72) ≠ window (fan r)) ∧
      ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
        (∀ i, S.R (master i) = nodeSeedWords c i) →
        (∀ i, S.L (bank i) = [] ∧ S.R (bank i) = []) →
        let seed := idleWindowSeed origin (fun _ => idleDispatchStacks N c.w c.idleWidth c.root.width.size c.cutoff)
        ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧ CleanupBound S F t (rate*c.cells) ∧
          (∀ j, IdleDispatchReady ((Fin.castAddEmb 6).trans (board j))
            c.w c.idleWidth c.root.width.size c.cutoff F) ∧
          (∀ j k, F.R (board j ((k : Fin 6).natAdd 72)) = (Routines.hdr (role c.node 142080) k).map bitSymbol) ∧
          (∀ j, F.L (window j) = seed.L j ∧ F.R (window j) = seed.R j) ∧
          ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨H,fan,raw,origin,payload,separate,off,free,seedAt⟩ := allocateIdleCallerWindow owner N
  refine ⟨H,fan,raw,origin,payload,separate,off,?_⟩
  intro T body bank master apart window
  let dst := ((Fin.natAddEmb 38 (m := 6)).trans (Fin.castAddEmb 36)).trans (Fin.castAddEmb 273)
  let roleBank := dst.trans ((Fin.natAddEmb H).trans bank)
  let board (j : Job) := appendPorts ((raw j).trans window) roleBank
    (fun k a => bank.injective.ne (suffixApart (dst a) (raw j k)).symm)
  have field (j : Job) (k : Fin 6) : board j (k.natAdd 72) = roleBank k := by simp [board,appendPorts]
  have rawAt (j : Job) (k : Fin 72) : board j (k.castAdd 6) = window (raw j k) := by simp [board,appendPorts]
  obtain ⟨code,rate,run⟩ := prepareIdleWindowRoles origin free body bank master apart capacity
  refine ⟨board,code,rate,rawAt,fun j l k => (field j k).trans (field l k).symm,?_,?_⟩
  · intro j k r
    rw [field]
    exact bank.injective.ne (suffixApart _ _)
  intro c u S words fresh seed
  obtain ⟨z,F,t,exec,user,paid,live,roles,frame⟩ := run c u S words fresh
  refine ⟨z,F,t,exec,user,paid,?_,fun j k => field j k ▸ roles k,live,frame⟩
  intro j k ne
  change F.L (board j (k.castAdd 6)) = _ ∧ F.R (board j (k.castAdd 6)) = _
  rw [rawAt]
  exact ⟨(live _).1.trans (seedAt c j k ne).1,(live _).2.trans (seedAt c j k ne).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
