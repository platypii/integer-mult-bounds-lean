module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode
public import IntegerMultBounds.MathlibTM2.M6.BitCompactWorkerSeeds

/-! Initialize a selected component on its allocated worker banks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine RecursiveInterchangeLayout Certificates.PR589
open Shared50ModularControl (prime)

/-- The six dimension and scratch tapes and the cutoff word follow the phase bank. -/
def PhaseSeedExec {T Q k : ℕ} {U : Type}
    (setup : Pr Empty (T+7) Q prime U) (fan : Fin k ↪ Fin T) (count : ℕ)
    (c : CutoffNodeInput) (prepared : Stacks T prime) (overhead : ℕ := 2) : Prop :=
  let place := Fin.castAddEmb 7 (n := T)
  let ext := Fin.natAddEmb T (m := 7)
  let M := prime^(c.w+1)
  let W := c.stageWidth
  ∀ u S, S.R (ext 0) = binSyms M.size M → S.R (ext 1) = binSyms W.size W →
    S.R (ext 2) = binSyms 1 1 → S.R (ext 3) = binSyms (c.w+1).size (c.w+1) →
    S.R (ext 4) = [] → S.R (ext 5) = [] → S.R (ext 6) = binSyms c.root.width.size c.cutoff →
    (∀ j, (∀ h, fan h ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) →
    ∃ z F t, Exec Empty.elim setup (mk u S) t (mk z F) ∧ z.user = u.user ∧
      CleanupBound S F t (178*count*c.cells+count*(8*(S.R (ext 6)).length+6)+overhead) ∧
      (∀ j, (∀ h, fan h ≠ j) → F.L (place j) = prepared.L j ∧ F.R (place j) = prepared.R j) ∧
      (∀ h, F.L (place (fan h)) = S.L (place (fan h)) ∧ F.R (place (fan h)) = S.R (place (fan h))) ∧
      ∀ i, F.L (ext i) = S.L (ext i) ∧ F.R (ext i) = S.R (ext i)

/-- Embed a loader on a caller's bank. Only the private component tapes
can change, so all other components keep their input or their loaded seed. -/
theorem PhaseSeedExec.place {T Q k H count overhead : ℕ} {P U : Type}
    {setup : Pr Empty (T+7) Q prime U} {fan : Fin k ↪ Fin T}
    {c : CutoffNodeInput} {prepared : Stacks T prime}
    (run : PhaseSeedExec setup fan count c prepared overhead) (host : P → Pr P H Q prime U)
    (bank : Fin (T+7) ↪ Fin H) :
    let data := (Fin.castAddEmb 7 (n := T)).trans bank
    let ext := (Fin.natAddEmb T (m := 7)).trans bank
    let M := prime^(c.w+1)
    let W := c.stageWidth
    ∀ u S, S.R (ext 0) = binSyms M.size M → S.R (ext 1) = binSyms W.size W →
      S.R (ext 2) = binSyms 1 1 → S.R (ext 3) = binSyms (c.w+1).size (c.w+1) →
      S.R (ext 4) = [] → S.R (ext 5) = [] → S.R (ext 6) = binSyms c.root.width.size c.cutoff →
      (∀ j, (∀ h, fan h ≠ j) → S.L (data j) = [] ∧ S.R (data j) = []) →
      ∃ z F t, Exec host (embProg bank Empty.elim setup) (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (178*count*c.cells+count*(8*(S.R (ext 6)).length+6)+overhead) ∧
        (∀ j, (∀ h, fan h ≠ j) → F.L (data j) = prepared.L j ∧ F.R (data j) = prepared.R j) ∧
        ∀ j, (∀ l, (∀ h, fan h ≠ l) → data l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro data ext M W u S modulus spectator unit atom ht hs cut blank
  obtain ⟨v,D,t,exec,user,paid,loaded,owners,controls⟩ := run (embDn bank u) (embStk bank S)
    modulus spectator unit atom ht hs cut blank
  obtain ⟨z,F,placed,_,same,view,off⟩ := exec_emb (ι := Empty.elim) (body' := host)
    bank.injective (fun g => nomatch g) exec u rfl S rfl
  subst D
  refine ⟨z,F,t,placed,same.trans user,CleanupBound.place bank off paid,loaded,?_⟩
  intro j away
  by_cases inside : ∃ i, bank i = j
  · obtain ⟨i,rfl⟩ := inside
    revert away
    refine Fin.addCases (fun l away => ?_) (fun s _ => controls s) i
    by_cases shared : ∃ h, fan h = l
    · obtain ⟨h,rfl⟩ := shared
      exact owners h
    · exact False.elim (away l (fun h eq => shared ⟨h,eq⟩) rfl)
  · exact off j (fun i eq => inside ⟨i,eq⟩)

/-- Load disjoint component banks in order. The common header words stay
available throughout, and the setup costs add once per component. -/
theorem loadComponentList {I P U : Type} {H Q : ℕ} (host : P → Pr P H Q prime U)
    (setup : I → Pr P H Q prime U) (inputs : Stacks H prime → Prop)
    (blank ready : I → Stacks H prime → Prop) (price : I → ℕ)
    (frame : Stacks H prime → Stacks H prime → Prop)
    (trans : ∀ {S D F}, frame S D → frame D F → frame S F)
    (load : ∀ i u S, inputs S → blank i S →
      ∃ z F t, Exec host (setup i) (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (price i) ∧ inputs F ∧ ready i F ∧ frame S F ∧
        ∀ j, j ≠ i → (blank j S → blank j F) ∧ (ready j S → ready j F))
    (i : I) (rest : List I) (distinct : (i :: rest).Nodup) :
    ∀ u S, inputs S → (∀ j ∈ i :: rest, blank j S) →
      ∃ z F t, Exec host (rest.foldl (fun code j => code.seq (setup j)) (setup i)) (mk u S) t (mk z F) ∧
        z.user = u.user ∧ CleanupBound S F t (((i :: rest).map price).sum) ∧ inputs F ∧
        (∀ j ∈ i :: rest, ready j F) ∧ frame S F := by
  intro u S input free
  obtain ⟨v,D,a,start,user,paid,words,stored,held,keep⟩ := load i u S input (free i (by simp))
  have loop (xs : List I) (unique : xs.Nodup) (code : Pr P H Q prime U) (base : ℕ)
      (done : List I) (v : HS H Q prime U) (D : Stacks H prime) (a : ℕ)
      (exec : Exec host code (mk u S) a (mk v D)) (same : v.user = u.user)
      (cost : CleanupBound S D a base) (current : inputs D) (saved : frame S D)
      (stock : ∀ j ∈ done, ready j D) (clear : ∀ j ∈ xs, blank j D)
      (apart : ∀ j ∈ done, j ∉ xs) :
      ∃ z F t, Exec host (xs.foldl (fun c j => c.seq (setup j)) code) (mk u S) t (mk z F) ∧
        z.user = u.user ∧ CleanupBound S F t (base+(xs.map price).sum) ∧ inputs F ∧
        (∀ j ∈ done ++ xs, ready j F) ∧ frame S F := by
    induction xs generalizing code base done v D a with
    | nil => exact ⟨v,D,a,exec,same,by simpa using cost,current,by simpa using stock,saved⟩
    | cons j xs ih =>
      obtain ⟨y,E,b,step,user,bill,words,ok,held,keep⟩ := load j v D current (clear j (by simp))
      obtain ⟨z,F,t,run,last,charge,input,all,frame⟩ := ih unique.tail (code.seq (setup j)) (base+price j)
        (j::done) y E (a+b) (exec.seq step) (user.trans same) (cost.seq bill) words (trans saved held)
        (fun l h => by rcases List.mem_cons.mp h with rfl | h
                       · exact ok
                       · exact (keep l (fun eq => apart l h (eq ▸ List.mem_cons_self))).2 (stock l h))
        (fun l h => (keep l (fun eq => unique.notMem (eq ▸ h))).1 (clear l (List.mem_cons_of_mem _ h)))
        (fun l h => by rcases List.mem_cons.mp h with rfl | h
                       · exact unique.notMem
                       · exact fun hx => apart l h (List.mem_cons_of_mem _ hx))
      exact ⟨z,F,t,run,last,by simpa [Nat.add_assoc] using charge,input,
        fun l h => all l (by simpa [List.mem_append,or_assoc,or_left_comm,or_comm] using h),frame⟩
  obtain ⟨z,F,t,run,same,bill,input,all,held⟩ := loop rest distinct.tail (setup i) (price i) [i]
    v D a start user paid words held (by simpa using stored)
    (fun j h => (keep j (fun eq => distinct.notMem (eq ▸ h))).1 (free j (List.mem_cons_of_mem _ h)))
    (by simpa using distinct.notMem)
  exact ⟨z,F,t,run,same,bill,input,all,held⟩

/-- Prepare a component on its allocated worker banks. Coverage identifies each
private tape of the combined bank with the worker seed loaded there. -/
theorem allocatedPhaseSeed [M8.Machine.Net] {U : Type} {T Q k count : ℕ}
    (tapes : Fin count → ℕ)
    (regs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes j))
    (basis : ∀ j, WorkerBasisLayout (regs j)) (owners : ∀ j, Fin k ↪ Fin (tapes j))
    (owned : ∀ j, (basis j).OwnerTapes (owners j)) (fan : Fin k ↪ Fin T)
    (bank : ∀ j, Fin (tapes j) ↪ Fin T)
    (cover : ∀ z, (∀ h, fan h ≠ z) → ∃ i l, (∀ h, owners i h ≠ l) ∧ bank i l = z)
    (apart : ∀ i l, (∀ h, owners i h ≠ l) →
      (∀ h, fan h ≠ bank i l) ∧ ∀ j, j ≠ i → ∀ m, bank j m ≠ bank i l) :
    ∃ setup : Pr Empty (T+7) Q prime U, ∀ (c : CutoffNodeInput) (prepared : Stacks T prime),
      (∀ i l, (∀ h, owners i h ≠ l) →
        let seed := (basis i).seed c.w c.stageWidth (binSyms c.root.width.size c.cutoff)
        prepared.L (bank i l) = seed.L l ∧ prepared.R (bank i l) = seed.R l) →
      PhaseSeedExec setup fan count c prepared := by
  let place := Fin.castAddEmb 7 (n := T)
  let ext := Fin.natAddEmb T (m := 7)
  let caller := (Fin.castAddEmb 1 (n := 6)).trans ext
  have disjoint (i : Fin T) (j : Fin 7) : place i ≠ ext j := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = T+j.val at h
    omega
  obtain ⟨setup,load⟩ := loadCompactWorkerSeeds (P := Empty) (Q := Q) (U := U) Empty.elim tapes regs basis
    (fun j => (bank j).trans place) owners caller (ext 6) (fun i j s => disjoint _ _) (fun i j => disjoint _ _)
    (ext.injective.ne (by decide)) (ext.injective.ne (by decide)) owned
    (fun i j off m ne l => place.injective.ne ((apart i j off).2 m ne l))
  refine ⟨setup,?_⟩
  intro c prepared initial
  let W := c.stageWidth
  intro u S modulus spectator unit atom ht hs cut blank
  have pos : 0 < (prime^(c.w+1))^16*W := c.stageCells.symm ▸
    Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))
  obtain ⟨z,F,t,exec,user,bill,stock,frame⟩ := load c.w W u S (Nat.pos_of_mul_pos_left pos)
    modulus spectator unit atom ht hs (fun i j off => blank _ (apart i j off).1)
  refine ⟨z,F,t,exec,user,?_,?_,?_,?_⟩
  · simpa only [← c.stageCells] using bill
  · intro j off
    obtain ⟨i,l,priv,rfl⟩ := cover j off
    have h := stock i l priv
    rw [cut] at h
    exact ⟨h.1.trans (initial i l priv).1.symm,h.2.trans (initial i l priv).2.symm⟩
  · intro h
    exact frame _ (fun i j off => place.injective.ne (Ne.symm ((apart i j off).1 h)))
  · intro i
    exact frame _ (fun _ j _ => disjoint _ i)

end IntegerMultBounds.MathlibTM2.M6.BitNode
