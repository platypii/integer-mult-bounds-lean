module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedStageAddress
public import IntegerMultBounds.MathlibTM2.M6.BitSweepExitReturn

/-! Return all independently occupied sweep records to the parent owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback SweepFile SweepFile.Exit
open Shared50ModularControl (prime)

private theorem fan_owner_rep {k T V N : ℕ} (fan : Fin (k+2) ↪ Fin T)
    (x : Fin k → Fin V → ZMod 2) (S : Stacks T prime) (live : HelperFan fan x S) (size : N = V) :
    let source := (Fin.castAddEmb 2).trans fan
    RepT (phaseOwners (fun i j => x i (j.cast size))) (embStk source S).L (embStk source S).R := by
  subst N
  intro source i z
  have read := fanPayload live i z
  rw [encodedOwnerCell,sub_zero] at read
  simpa only [source,Function.Embedding.trans_apply,Fin.castAddEmb_apply,Fin.cast_refl,id_eq,phaseOwners,embStk,Function.comp_apply,sub_zero] using read.symm

/-- Materialize the complete output bank once and run the existing inverse
stage permutation over its full spectator records. -/
theorem borrowedReturn_exec {P U : Type} {Q T : ℕ} (n : Fin 9) (body : P → Pr P T Q prime U)
    (fan : Fin (142081+2) ↪ Fin T) (sw : Fin SweepFile.tapes ↪ Fin T) (tmp : Fin T)
    (apart : ∀ (i : Fin 142081) j, fan (i.castAdd 2) ≠ sw (owners j))
    (srcTmp : ∀ i : Fin 142081, fan (i.castAdd 2) ≠ tmp) (dstTmp : ∀ i, sw (owners i) ≠ tmp) :
    ∃ code C, ∀ (w H B K : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
    let M := prime^(w+1)
    let labels := prime^(64*((w+1)*64))
    let W := B*labels*K
    let V := M^16*(M^112*B*labels*K)
    M^128 < 2^H → H ≤ M^128+1 → 0 < W →
    ∀ (x : Fin 142081 → Fin V → ZMod 2) (v : HS T Q prime U) (S : Stacks T prime),
    HelperFan fan x S → S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (sw (owners i)) = []) →
    ReturnHeaders w H parent W 1 (embStk sw S).R →
    ∃ z G l, Exec body code (mk v S) l (mk z G) ∧
      l ≤ 142081*(8*V+10)+1 + (142080*(C*(M^16*(labels*(M^112*W)))+8)+1) ∧ z.user = v.user ∧
      (∀ i, G.L (sw (owners i)) = S.L (sw (owners i))) ∧
      G.R (sw (owners (Fin.last 142080))) = List.ofFn (fun j => SparseRoleCircuit.encode
        (borrowedNodeArray n parent units x (Fin.last 142080) j)) ∧
      ∀ r, G.R (sw (owners (sweepRoleTape r))) = List.ofFn fun i =>
        SparseRoleCircuit.encode (borrowedNodeArray n parent units x (sweepRoleTape r) i) := by
  let source := (Fin.castAddEmb 2).trans fan
  let dest := owners.trans sw
  obtain ⟨copy,load⟩ := materializeOwners_exec body source dest tmp apart srcTmp dstTmp
  obtain ⟨C,back⟩ := placedWordReturn_exec (P := P) (U := U) (Q := Q) n
  obtain ⟨ret,restore⟩ := back body sw
  refine ⟨copy.seq ret,C,?_⟩
  intro w H B K parent units M labels W V fits bits positive x v S live left right empty headers
  let a : OwnerArray (w+1) 1 W := fun i j => x i (j.cast (borrowedOwnerVolume (w+1) B K))
  obtain ⟨u,R,k,copied,bill,user,words,off⟩ := load a v S (fan_owner_rep fan x S live _) left right empty
  obtain ⟨z,G,l,done,paid,same,heads,spare,out⟩ := restore w H 1 W parent units fits bits Nat.one_pos positive
    a u S {S with R := R} headers (fun j apart => off (sw j) (fun i eq => apart i (sw.injective eq)))
    (fun r => words (sweepRoleTape r))
  refine ⟨z,G,k+l,Exec.seq copied done,?_,same.trans user,heads,?_,out⟩
  rotate_left
  · simpa only [borrowedNodeArray,nodeArray,Fin.lastCases_last] using spare.trans (words (Fin.last 142080))
  apply Nat.add_le_add _ (by simpa only [Nat.one_mul] using paid)
  simpa only [W,V,M,labels,borrowedOwnerVolume (w+1) B K] using bill

/-- Append the physical return to a corrected worker. The worker owns its
original tapes and preserves the return headers and empty destinations. -/
theorem borrowedStageReturn_exec {P U : Type} {Q T : ℕ} (n : Fin 9)
    (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U) (fan : Fin (142081+2) ↪ Fin T) :
    let place := Fin.castAddEmb (SweepFile.tapes+1) (n := T)
    let sw := (Fin.castAddEmb 1 (n := SweepFile.tapes)).trans (Fin.natAddEmb T)
    let tmp := (Fin.last SweepFile.tapes).natAdd T
    let host := fun f => embProg place id (body f)
    ∃ code C, ∀ (w H B K : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
    let M := prime^(w+1)
    let labels := prime^(64*((w+1)*64))
    let W := B*labels*K
    let V := M^16*(M^112*B*labels*K)
    M^128 < 2^H → H ≤ M^128+1 → 0 < W →
    ∀ (x : Fin 142081 → Fin V → ZMod 2) (price : ℕ) u S,
    (∃ z F k y, Exec body worker (mk (embDn place u) (embStk place S)) k (mk z F) ∧
      k ≤ price ∧ z.user = u.user ∧ HelperFan fan y F ∧
      ∀ b t g, borrowedStageRead n b t g y = (Piece.stage n).run (borrowedStageRead n b t g x)) →
    S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (sw (owners i)) = []) →
    ReturnHeaders w H parent W 1 (embStk sw S).R →
    ∃ z F k d, Exec host code (mk u S) k (mk z F) ∧
      k ≤ price + (142081*(8*V+10)+1 + (142080*(C*(M^16*(labels*(M^112*W)))+8)+1)) ∧
      z.user = u.user ∧ borrowedStageHandoff (w+1) B K parent units n (borrowedNodeArray n parent units x) d ∧
      ∀ r, F.R (sw (owners (sweepRoleTape r))) =
        List.ofFn fun i => SparseRoleCircuit.encode (d (sweepRoleTape r) i) := by
  intro place sw tmp host
  have apart (i j) : place i ≠ sw j := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = T+j.val at h
    omega
  have separate (i) : place i ≠ tmp := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = T+SweepFile.tapes at h
    omega
  have temporary (i) : sw i ≠ tmp := by
    intro eq
    have h := congrArg Fin.val eq
    change T+i.val = T+SweepFile.tapes at h
    omega
  obtain ⟨back,C,ret⟩ := borrowedReturn_exec n host (fan.trans place) sw tmp
    (fun i j => apart _ _) (fun i => separate _) (fun i => temporary _)
  refine ⟨(embProg place id worker).seq back,C,?_⟩
  intro w H B K parent units M labels W V fits bits positive x price u S run left right empty headers
  obtain ⟨v,D,k,y,exec,bill,user,live,stage⟩ := run
  obtain ⟨v',D',middle,_,user',view,off⟩ := exec_emb (body' := host) (ι := id) place.injective
    (fun _ => rfl) exec u rfl S rfl
  have represented : HelperFan (fan.trans place) y D' := by
    rw [← view] at live
    exact live
  have keep (j) := off (sw j) (fun i => apart i j)
  have held : (embStk sw D').R = (embStk sw S).R := funext fun j => (keep j).2
  obtain ⟨z,F,l,done,paid,same,_,_,words⟩ := ret w H B K parent units fits bits positive y v' D' represented
    ((off tmp separate).1.trans left) ((off tmp separate).2.trans right)
    (fun i => (keep _).2.trans (empty i)) (held ▸ headers)
  exact ⟨z,F,k+l,borrowedNodeArray n parent units y,Exec.seq middle done,Nat.add_le_add bill paid,
    same.trans (user'.trans user),⟨x,y,rfl,rfl,stage⟩,words⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
