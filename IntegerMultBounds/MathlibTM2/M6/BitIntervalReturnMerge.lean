module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalPack
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners

/-! Return the recursive owner rows to inherited order and merge them on the host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem unpackMerge_exec {T capacity : ℕ} (fitsStates : Q ≤ capacity)
    (mergeStates : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ capacity)
    (place : Fin intervalSplitTapes ↪ Fin T)
    (body : P → Pr P (T+142080*(N+35)) capacity prime U) (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) :
    let live := (intervalOwners 142080).trans place
    let mergeBank := place.trans (Fin.castAddEmb (142080*(N+35)))
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank live (small 24)
    let fan := live.trans (Fin.castAddEmb (142080*(N+35)))
    ∀ w W, 0 < W →
      let M := prime^(w+1)
      let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      ∀ (u : HS (T+142080*(N+35)) capacity prime U) (S : Stacks (T+142080*(N+35)) prime) (record : Fin 142080 → List (Fin (prime+4)))
        (dest : Fin 142080 → ℤ → Fin 4) (q : Fin 142080 → ℤ)
        (output : Fin 142080 → Fin (volume prime (phaseIntervalChild lo hi (w+1) W 64)) → ZMod 2),
      let stored := fun r word F => RecordReady (b := prime) (w := w) (W := W) (d := 128)
        (small.trans (ports r)) M.size W.size (record r) SparseRoleCircuit.encode (fun _ => blank)
        (dest r) 0 (q r) word F ∧ ∀ k : Fin (N+35), 35 ≤ k.val →
          F.L (ports r k) = [] ∧ F.R (ports r k) = []
      HelperFan fan (fun r => output r ∘ position.symm) S →
      (∀ r, ∃ word D, stored r word D ∧ ∀ k, k ≠ small 24 →
        S.L (ports r k) = D.L (ports r k) ∧ S.R (ports r k) = D.R (ports r k)) →
      let code := fun r => statePlacedNormalized (ports r) fitsStates swapStates_pos Empty.elim (packSchedule 128 is.reverse)
      ∀ (target : ℤ → Fin (prime+4)) (original : Fin 142080 → Fin (M^128*W) → ZMod 2)
        (before : Stacks intervalSplitTapes prime),
      RepT (intervalOwnerBank target original) before.L before.R →
      (S.L (mergeBank 0) = before.L 0 ∧ S.R (mergeBank 0) = before.R 0) →
      (∀ j : Fin 2, let k := (j.natAdd (1+142080)).castAdd 2
        S.L (mergeBank k) = before.L k ∧ S.R (mergeBank k) = before.R k) →
      let data := fun r (i : Fin (M^128*W)) => output r (i.cast size.symm)
      let word := fun k : Fin (M^128*W*142080) => let p := finProdFinEquiv.symm k
                                                  SparseRoleCircuit.encode (a := prime) (data p.2 p.1)
      ∃ z F n, Exec body ((Prog.seqList ((List.finRange 142080).map code)).seq
        (embProg mergeBank Empty.elim (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) mergeStates))))
        (mk u S) n (mk z F) ∧
        n ≤ ((List.finRange 142080).map (fun _ => intervalPassTime U lo hi w W)).sum+1
          +(149*(M^128*W*142080)*(intervalSplitTapes+5)+6) ∧ z.user = u.user ∧
        RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) data) (embStk mergeBank F).L (embStk mergeBank F).R := by
  intro live mergeBank small ports fan
  have unpack := placedIntervalPass_exec fitsStates live body lo hi ordered fits true
  intro w W hW M is size position u S record dest q output stored packed saved code target original before split source inner data word
  obtain ⟨v,D,t,unpacked,paid,user,returned,_,frame⟩ :=
    unpack w W hW u S record dest q output packed saved
  have pos : 0 < M^128*W := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  have keep (k : Fin intervalSplitTapes) (off : ∀ r : Fin 142080, intervalOwners 142080 (r.castAdd 2) ≠ k) :
      D.L (mergeBank k) = S.L (mergeBank k) ∧ D.R (mergeBank k) = S.R (mergeBank k) :=
    frame (place k) (fun r => place.injective.ne (off r))
  have src := keep 0 (fun r eq => by
    have h := congrArg Fin.val eq
    simp [intervalOwners] at h)
  obtain ⟨z,F,l,merged,cost,same,result,_,_⟩ := placedMergeReturnedOwners_exec body mergeBank
    mergeStates pos target original data before v D split returned
    ⟨src.1.trans source.1,src.2.trans source.2⟩ (by
      intro j
      have kept := keep ((j.natAdd (1+142080)).castAdd 2) (fun r eq => by
        have h := congrArg Fin.val eq
        simp [intervalOwners] at h
        omega)
      exact ⟨kept.1.trans (inner j).1,kept.2.trans (inner j).2⟩)
  exact ⟨z,F,t+l,.seq unpacked merged,Nat.add_le_add paid cost,same.trans user,result⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
