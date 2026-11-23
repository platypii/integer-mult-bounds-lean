module

public import IntegerMultBounds.MathlibTM2.M6.BitInheritedReturnMerge
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead
public import IntegerMultBounds.MathlibTM2.M6.BitParentArchiveSeed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Prepare the private record slots before the selected archive loader writes
slot 34. The shared payload at slot 24 may already be live. -/
theorem loadWorkerRecordSeed [M8.Machine.Net] {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (place : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (source : Fin 3 → Fin T) (width tmp saved : Fin T) :
    let bank := scheduledRecordPorts place
    let slots := copyRecordTargets.trans ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits))
    (∀ i, width ≠ bank i) →
    (∀ i j, place (slots i) ≠ source j) →
    (∀ i, [source i,place (slots i),tmp,saved].Nodup) →
    ∃ code, ∀ w W u (S : Stacks T prime),
      let M := prime^(w+1)
      let seed := moveRecordSeed w W [] [] []
      S.R (source 0) = binSyms M.size M → S.R (source 1) = binSyms W.size W → S.R (source 2) = binSyms 1 1 →
      S.R width = binSyms (w+1).size (w+1) →
      (∀ j, j.val ≠ 24 → S.L (place j) = [] ∧ S.R (place j) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (18*M.size+8*W.size+8*(w+1)+11*(w+1).size+53) ∧
        (∀ j, j.val ≠ 24 → F.L (place j) = seed.L j ∧ F.R (place j) = seed.R j) ∧
        ∀ j, (∀ l, l.val ≠ 24 → place l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro bank slots outside apart regs
  obtain ⟨copy,load⟩ := installChildSeed body place slots source tmp saved apart regs
  let pad : Pr P T Q prime U := toBinary (bank 28) (bank 2) (bank 32) (bank 0) (bank 1) (bank 3)
  let clock : Pr P T Q prime U := toUnary width (bank 33) (bank 0) (bank 1) (bank 3)
  let drop : Act T Q prime U := .pop (.rt (bank 33)) (fun v _ => v) .done
  refine ⟨copy.seq (pad.seq (clock.seq (.act drop))),?_⟩
  intro w W u S M seed modulus spectator unit atom blank ht hs
  have nonpayload (i : Fin 3) : (slots i).val ≠ 24 := (by decide : ∀ i : Fin 3, (copyRecordTargets i).val ≠ 24) i
  obtain ⟨v,R,n,start,user,paid,stored,frame⟩ := load seed u S (fun i => by
    fin_cases i <;> first | exact modulus | exact spectator | exact unit)
    (fun i => (blank _ (nonpayload i)).2) ht hs
  let D := {S with R := R}
  have copied i := stored (slots i) (fun off => False.elim (off i rfl))
  have clear (i : Fin 35) (hi : i ∈ ([0,1,3,32,33] : List (Fin 35))) : D.R (bank i) = [] := by
    have sep := (by decide : ∀ i ∈ ([0,1,3,32,33] : List (Fin 35)), (∀ j, copyRecordTargets j ≠ i) ∧ i.val ≠ 24) i hi
    exact (frame _ (fun j => bank.injective.ne (sep.1 j))).trans (blank _ sep.2).2
  obtain ⟨z,t,done,time,finish⟩ := copyRecordControls_exec body bank width outside w v D (copied 0) (copied 2)
    ((frame width (fun i => (outside (copyRecordTargets i)).symm)).trans atom) clear
  let A := {D with R := Function.update D.R (bank 32) (binSyms M.size 1)}
  let F := {A with R := Function.update A.R (bank 33) (List.replicate w Node.tick)}
  refine ⟨z,F,n+t,start.seq finish,done.trans user,?_,?_,?_⟩
  · have price : seedLoadBill (fun i => seed.R (slots i)) = 8*(M.size+W.size)+27 := by
      have m : seed.R (slots 0) = binSyms M.size M := rfl
      have s : seed.R (slots 1) = binSyms W.size W := rfl
      have o : seed.R (slots 2) = binSyms 1 1 := rfl
      simp [seedLoadBill,Fin.sum_univ_succ,m,s,o,length_binSyms]
      omega
    intro js nd
    have bill := paid js nd
    rw [price] at bill
    have a := prependedWordCharge D (bank 32) (binSyms M.size 1) js nd
    have b := prependedWordCharge A (bank 33) (List.replicate w Node.tick) js nd
    have fresh : A.R (bank 33) = [] := by simp [A,bank.injective.eq_iff,clear 33 (by decide)]
    simp only [clear 32 (by decide),List.append_nil,length_binSyms] at a
    simp only [fresh,List.append_nil,List.length_replicate] at b
    change tapeCharge cleanupWeight js A ≤ _ at a
    change tapeCharge cleanupWeight js F ≤ _ at b
    change n+tapeCharge cleanupWeight js D ≤ _ at bill
    change n+t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
    change t ≤ 8*M.size+6*(w+1)+11*(w+1).size+25 at time
    omega
  · intro j ne
    have unitVal : (1 : ZMod M).val = 1 := ZMod.val_one'' (Nat.ne_of_gt
      (Shared50ModularControl.prime_prime.one_lt.trans_le (Nat.le_self_pow (Nat.succ_ne_zero _) prime)))
    refine ⟨(blank j ne).1.trans (by simp [seed,moveRecordSeed]),?_⟩
    by_cases a : j.val = 32
    · have eq : place j = bank 32 := congrArg place (Fin.ext a)
      simp [F,A,eq,bank.injective.eq_iff,seed,moveRecordSeed,a,unitVal]
      rfl
    by_cases b : j.val = 33
    · have eq : place j = bank 33 := congrArg place (Fin.ext b)
      simp [F,eq,seed,moveRecordSeed,b]
    have atPort (k : Fin 35) (off : j.val ≠ k.val) : place j ≠ bank k :=
      place.injective.ne (fun eq => off (congrArg Fin.val eq))
    change Function.update A.R (bank 33) _ (place j) = _
    rw [Function.update_of_ne (atPort 33 b)]
    change Function.update D.R (bank 32) _ (place j) = _
    rw [Function.update_of_ne (atPort 32 a)]
    apply stored
    intro off
    have miss (i : Fin 3) : j.val ≠ (slots i).val := fun eq => off i (Fin.ext eq.symm)
    have p : j.val ≠ 2 := miss 0
    have q : j.val ≠ 27 := miss 1
    have u : j.val ≠ 28 := miss 2
    simp [seed,moveRecordSeed,p,q,u,a,b,ne,(blank j ne).2]
  · intro j off
    have keep (k : Fin 35) (ne : k.val ≠ 24) : j ≠ bank k := (off _ ne).symm
    exact ⟨rfl,(Function.update_of_ne (keep 33 (by decide)) ..).trans
      ((Function.update_of_ne (keep 32 (by decide)) ..).trans (frame j (fun i => off _ (nonpayload i))))⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
