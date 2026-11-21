module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryOutgoingScan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders
public import Mathlib.Data.Fin.Tuple.Embedding

/-! Retain the directory, its prefix width, and the two masks for the outgoing scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open Mult.PhaseCellToeplitz
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- The outgoing scan reads these four words beginning at their saved positions. -/
def replaySlots : Fin 4 ↪ Fin 66 := ⟨![46,47,57,56],by decide⟩

/-- Charge the archive, one prefix-width word and both selector masks. -/
def directoryReplayTime (m w records width tail : ℕ) : ℕ :=
  6*(records*(width+(w+1)*(m*m))+tail+width+2*records)+25

/-- At width 64 the archive and its two masks cost at most thirty steps per
payload cell, plus the inherited archive tail and the fixed copy instructions. -/
theorem directoryReplayTime_volume (w R W width tail : ℕ) (rows : 0 < R) (positive : 0 < W) :
    let M := prime^(w+1)
    let N := M^128*W
    width ≤ N → directoryReplayTime 64 w R width tail ≤ 30*(R*N)+6*tail+25 := by
  intro M N fits
  have radix : 2 ≤ M := (Shared50ModularControl.prime_prime.two_le).trans
    (Nat.le_self_pow (by omega : w+1 ≠ 0) prime)
  have ticks : w+1 ≤ M := Nat.le_of_lt (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt)
  have digits : (w+1)*(64*64) ≤ N := calc
    _ ≤ M*M^12 := Nat.mul_le_mul ticks (by simpa using Nat.pow_le_pow_left radix 12)
    _ = M^13 := by rw [show M^13 = M^12*M from pow_succ M 12,Nat.mul_comm]
    _ ≤ M^128 := Nat.pow_le_pow_right (by omega) (by decide)
    _ ≤ N := Nat.le_mul_of_pos_right _ positive
  have nonzero : 0 < N := Nat.mul_pos (pow_pos (by omega : 0 < M) _) positive
  have archive := Nat.mul_le_mul_left R (Nat.add_le_add fits digits)
  have prefixWidth := fits.trans (Nat.le_mul_of_pos_left N rows)
  have masks := Nat.le_mul_of_pos_right R nonzero
  unfold directoryReplayTime
  rw [Nat.mul_add R N N] at archive
  omega

/-- Replay, mask copying and restoration together charge the recursive child once. -/
theorem directoryReturnTime_volume {R N tail replay child steps : ℕ} (positive : 0 < N)
    (saved : replay ≤ 30*(R*N)+6*tail+25) (returned : steps ≤ child+R*(16*N+14)+12) :
    replay+(12*R+12)+steps ≤ child+72*(R*N)+6*tail+49 := by
  have rows := Nat.le_mul_of_pos_right R positive
  rw [show R*(16*N+14) = 16*(R*N)+14*R by ring] at returned
  omega

theorem directoryReplayTime_eq {K m w W H J R : ℕ} {v : RecursiveInterchangeLayout.Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {weights : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {tail : List (Fin (prime+4))}
    {schedule : List ℕ → List (Fin (prime+4))} (S : Stacks (66+K) prime)
    (ready : DirectoryReady v proj w W H J weights prefixes tail schedule S (List.range R))
    (positive : 0 < R) :
    let caller := Fin.castAddEmb (n := 66) K
    (S.R (caller 57)).length = R → (S.R (caller 56)).length = R →
    ((List.finRange 4).map (fun j => 6*(S.R (caller (replaySlots j))).length+6)).sum+1 =
      directoryReplayTime m w R (prefixes 0).length tail.length := by
  intro caller live bad
  have width := ready.2.1 0 (List.mem_range.mpr positive)
  have archive : ((List.range R).flatMap (LabelDirectory.entry prefixes m (w+1))).length =
      R*((prefixes 0).length+(w+1)*(m*m)) := by
    rw [List.flatMap_def,BlockRotationData.uniform_volume ((prefixes 0).length+(w+1)*(m*m))]
    · simp
    · intro xs hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
      rw [LabelDirectory.entry_length,← ready.2.1 j hj,width]
  change (6*(S.R (caller 46)).length+6)+((6*(S.R (caller 47)).length+6)+
    ((6*(S.R (caller 57)).length+6)+((6*(S.R (caller 56)).length+6)+0)))+1 = _
  rw [ready.1,List.length_append,archive,width,live,bad]
  unfold directoryReplayTime
  omega

noncomputable def replayRole {n : ℕ} (slots : Fin 4 ↪ Fin n) (i : Fin n) : Option (Fin 4) :=
  if h : ∃ j, slots j = i then some h.choose else none

private theorem replayRole_eq {n : ℕ} (slots : Fin 4 ↪ Fin n) (j : Fin 4) :
    replayRole slots (slots j) = some j := by
  unfold replayRole
  have h : ∃ k, slots k = slots j := ⟨j,rfl⟩
  rw [dite_eq_left h]
  exact congrArg some (slots.injective h.choose_spec)

noncomputable def replayPlacement {n T : ℕ} (e : Fin n ↪ Fin T) (slots : Fin 4 ↪ Fin n)
    (saved : Fin 4 ↪ Fin T) (apart : ∀ i j, e i ≠ saved j) : Fin n ↪ Fin T :=
  ⟨sharedRegisterPlacement e saved (replayRole slots),
    sharedRegisterPlacement_injective e e.injective saved saved.injective apart _ (by
      intro i k j hi hk
      have atSlot (a : Fin n) (h : replayRole slots a = some j) : slots j = a := by
        unfold replayRole at h
        split at h
        · next present => exact Option.some.inj h ▸ present.choose_spec
        · contradiction
      exact (atSlot i hi).symm.trans (atSlot k hk))⟩

theorem replayPlacement_saved {n T : ℕ} (e : Fin n ↪ Fin T) (slots : Fin 4 ↪ Fin n)
    (saved : Fin 4 ↪ Fin T) (apart : ∀ i j, e i ≠ saved j) (j : Fin 4) :
    replayPlacement e slots saved apart (slots j) = saved j := by
  simp [replayPlacement,sharedRegisterPlacement,replayRole_eq]

theorem replayPlacement_off {n T : ℕ} (e : Fin n ↪ Fin T) (slots : Fin 4 ↪ Fin n)
    (saved : Fin 4 ↪ Fin T) (apart : ∀ i j, e i ≠ saved j) (i : Fin n) (off : ∀ j, slots j ≠ i) :
    replayPlacement e slots saved apart i = e i := by
  simp [replayPlacement,sharedRegisterPlacement,replayRole,show ¬ ∃ j, slots j = i from fun ⟨j,h⟩ => off j h]

/-- Redirecting the four directory words leaves each disjoint owner register available. -/
theorem replayPlacement_ne {n T : ℕ} (e : Fin n ↪ Fin T) (slots : Fin 4 ↪ Fin n)
    (saved : Fin 4 ↪ Fin T) (apart : ∀ i j, e i ≠ saved j) {reg : Fin T}
    (localOff : ∀ i, e i ≠ reg) (savedOff : ∀ j, saved j ≠ reg) (i : Fin n) :
    replayPlacement e slots saved apart i ≠ reg := by
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j,rfl⟩ := h
    rw [replayPlacement_saved]
    exact savedOff j
  · rw [replayPlacement_off e slots saved apart i (fun j eq => h ⟨j,eq⟩)]
    exact localOff i

/-- Place the outgoing scanner and the five physical owner registers in one machine. -/
def outgoingOwnerPlacement {n T : ℕ} (bank : Fin n ↪ Fin T) (regs : Fin 5 ↪ Fin T)
    (apart : ∀ i j, bank i ≠ regs j) : Fin (n+5) ↪ Fin T :=
  Fin.Embedding.append (Set.disjoint_range_iff.mpr apart)

@[simp] theorem outgoingOwnerPlacement_bank {n T : ℕ} (bank : Fin n ↪ Fin T) (regs : Fin 5 ↪ Fin T)
    (apart : ∀ i j, bank i ≠ regs j) (i : Fin n) :
    outgoingOwnerPlacement bank regs apart (i.castAdd 5) = bank i := by
  simp [outgoingOwnerPlacement]

@[simp] theorem outgoingOwnerPlacement_reg {n T : ℕ} (bank : Fin n ↪ Fin T) (regs : Fin 5 ↪ Fin T)
    (apart : ∀ i j, bank i ≠ regs j) (j : Fin 5) :
    outgoingOwnerPlacement bank regs apart (Fin.natAdd n j) = regs j := by
  simp [outgoingOwnerPlacement]

/-- Snapshot four right stacks before the incoming pass. The scanner's own stacks
are unchanged, and the exact charge counts each copied symbol. -/
theorem saveDirectoryReplay_exec {P U : Type} {n T Q : ℕ} (body : P → Pr P T Q prime U)
    (e : Fin n ↪ Fin T) (slots : Fin 4 ↪ Fin n) (work : Fin 6 ↪ Fin T)
    (apart : ∀ i j, e i ≠ work j) (u : HS T Q prime U) (S : Stacks T prime)
    (free : ∀ j, S.R (work j) = []) :
    let saved := (Fin.castLEEmb (by decide : 4 ≤ 6)).trans work
    let pairs := (List.finRange 4).map fun j => (e (slots j),saved j)
    ∃ z D, z.user = u.user ∧
      Exec body (copyWordHeaders (work 4) (work 5) pairs) (mk u S)
        (((List.finRange 4).map (fun j => 6*(S.R (e (slots j))).length+6)).sum+1) (mk z D) ∧
      embStk e D = embStk e S ∧ (∀ j, D.R (saved j) = S.R (e (slots j))) ∧ D.L = S.L ∧
      ∀ i, (∀ j, saved j ≠ i) → D.R i = S.R i := by
  intro saved pairs
  obtain ⟨z,user,run⟩ := copyWordHeaders_exec (body := body) (work 4) (work 5) pairs (by
    intro p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    have lo : j.val < 4 := j.isLt
    simp [List.nodup_cons,apart,saved,work.injective.eq_iff,Fin.ext_iff]
    <;> omega) (by
    intro p hp q hq
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
    exact (apart _ _).symm) S.R u S (fun _ _ => rfl) (free 4) (free 5)
  have off (i) (hi : ∀ j, saved j ≠ i) := copyWordHeadersR_off S.R pairs S.R i (by
    intro p hp
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    exact hi j)
  refine ⟨z,{S with R := copyWordHeadersR S.R pairs S.R},user,by simpa only [pairs,List.map_map,Function.comp_def] using run,?_,?_,rfl,off⟩
  · refine Stacks.ext rfl rfl rfl ?_
    funext i
    exact off _ (fun j => (apart i _).symm)
  · intro j
    have nd : (pairs.map Prod.snd).Nodup := by
      simpa [pairs,List.map_map,Function.comp_def] using (List.nodup_finRange 4).map saved.injective
    exact (copyWordHeadersR_get S.R pairs nd S.R _ (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩)).trans
      (by rw [show S.R (saved j) = [] from free _,List.append_nil])

/-- At the return boundary the preserved directory and masks supply the second pass.
All other headers and the private workspace come from the completed incoming scan. -/
theorem outgoingReplay_ready {K T m w W H J : ℕ} {v : RecursiveInterchangeLayout.Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {tail : List (Fin (prime+4))}
    {schedule : List ℕ → List (Fin (prime+4))} {rs : List ℕ}
    (e : Fin (66+K) ↪ Fin T) (saved : Fin 4 ↪ Fin T) (apart : ∀ i j, e i ≠ saved j)
    (initial : Stacks (66+K) prime) (F : Stacks T prime) (live bad : ℕ → Bool) :
    let caller := Fin.castAddEmb (n := 66) K
    let slots := replaySlots.trans caller
    let old := embStk e F
    let D := embStk (replayPlacement e slots saved apart) F
    DirectoryReady v proj w W H J parent prefixes tail schedule initial rs →
    DirectoryReady v proj w W H J parent prefixes tail schedule old [] →
    schedule [] = [] →
    (∀ j, F.R (saved j) = initial.R (slots j)) →
    initial.R (caller 57) = rs.map (fun j => bitSymbol (live j)) →
    initial.R (caller 56) = rs.map (fun j => bitSymbol (bad j)) →
    DirectoryReady v proj w W H J parent prefixes tail (fun _ => []) D rs ∧
      D.R (caller 57) = rs.map (fun j => bitSymbol (live j)) ∧
      D.R (caller 56) = rs.map (fun j => bitSymbol (bad j)) := by
  intro caller slots old D start finish endSchedule retained ls bs
  have restored (j : Fin 4) : D.R (slots j) = initial.R (slots j) := by
    change F.R (replayPlacement e slots saved apart (slots j)) = _
    rw [replayPlacement_saved,retained]
  have same (i : Fin (66+K)) (off : ∀ j, slots j ≠ i) :
      D.L i = old.L i ∧ D.R i = old.R i := by
    change F.L (replayPlacement e slots saved apart i) = _ ∧ F.R (replayPlacement e slots saved apart i) = _
    rw [replayPlacement_off e slots saved apart i off]
    exact ⟨rfl,rfl⟩
  have port (k : Fin 66) (off : ∀ j, replaySlots j ≠ k) :=
    (same (caller k) (fun j => caller.injective.ne (off j))).2
  obtain ⟨_,_,clear,scratch,matrix,base,one,width,headers,padded,clock,weights,residual⟩ := finish
  refine ⟨⟨(restored 0).trans start.1,fun j hj => (congrArg List.length (restored 1)).trans (start.2.1 j hj),
    ?_,(port 49 (by decide)).trans scratch,?_,(port 2 (by decide)).trans base,(port 28 (by decide)).trans one,
    (port 53 (by decide)).trans width,?_,(port 44 (by decide)).trans padded,
    (congrArg List.length (port 45 (by decide))).trans clock,(port 55 (by decide)).trans weights,
    (port 54 (by decide)).trans (residual.trans endSchedule)⟩,(restored 2).trans ls,(restored 3).trans bs⟩
  · intro i hi
    have h := same i (fun j eq => by
      have val := congrArg Fin.val eq
      change (replaySlots j).val = i.val at val
      have bound := (by decide : ∀ j, (replaySlots j).val < 58) j
      omega)
    exact ⟨h.1.trans (clear i hi).1,h.2.trans (clear i hi).2⟩
  · obtain ⟨suffix,h⟩ := matrix
    exact ⟨suffix,(port 48 (by decide)).trans h⟩
  · intro i
    exact (port _ ((by decide : ∀ i : Fin 6, ∀ j, replaySlots j ≠ (i.natAdd 33).castLE (by decide : 39 ≤ 66)) i)).trans (headers i)

end IntegerMultBounds.MathlibTM2.M6.BitNode
