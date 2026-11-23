module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedSweepCharge

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

private theorem scannedPayload {V T : ℕ} (word : Fin V → ZMod 2) (S : Stacks T prime) (port : Fin T)
    (read : WordAtZero word (S.L port) (S.R port)) : RecordPayload port (fun _ => blank) 0 word S := by
  intro j
  rw [encodedOwnerCell,sub_zero]
  exact read j

private theorem scanTotal {t s f r h A B N K : ℕ}
    (bill : t+f ≤ s+r*((A*B)*(N*K))+h*(A*(B*N*K))) :
    t+f ≤ s+(r+h)*((A*B)*(N*K)) := by
  simpa only [Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using bill

private theorem projectedScanFan {k T R V : ℕ} (fan : Fin (k+2) ↪ Fin T) (ext : Fin T ↪ Fin R)
    (out : Fin k → Fin V → ZMod 2) (S : Stacks R prime) (ready : HelperFan (fan.trans ext) out S) :
    HelperFan fan out (embStk ext S) := ready

private theorem projectedScanUser {T R Q A : ℕ} {U : Type} (e : Fin T ↪ Fin R)
    (u : HS R Q A U) : (embDn e u).user = u.user := rfl

/-- Read the restored targets and return the collapsed parent words on one fixed program. -/
theorem restoredSweepOutputWithCharge (n : Fin 9) :
    let I := (Fin 32 × Fin 5) × Fin 111
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (fan : Fin (142081+2) ↪ Fin T), states ≤ Q →
    let inner := (Fin.castAddEmb 14 (n := T)).trans (Fin.castAddEmb (142081*7))
    let placedFan := fan.trans (Fin.castAddEmb 14)
    let bank := fun k : I => targetScanBank placedFan (targetOwner n k)
    let reg := (Fin.castAddEmb 4 (n := 10)).trans ((Fin.natAddEmb T (m := 14)).trans (Fin.castAddEmb (142081*7)))
    let ext := (Fin.castAddEmb 142081 (n := (T+14)+142081*7)).trans (Fin.castAddEmb 10)
    ∀ (body : P → Pr P ((T+14)+142081*7) Q prime U), ∃ code, ∃ rate : ℕ,
    ∀ (w B W : ℕ) (x),
    let K := (prime^w)^112*W
    let N := prime^(64*(w*64))
    let D := (prime^w)^16*B
    let label := firstRowLabel w
    0 < K → 0 < B → ∀ u S y out, HelperFan ((fan.trans inner).trans ext) out S →
    (∀ j, (T+14)+142081*7 ≤ j.val → S.L j = [] ∧ S.R j = []) →
    stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k w B W a b ∧ next b)
      (fun a => a = y) (singleLabelBank label x) →
    HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
    (∀ i : Fin 3, S.L (ext (reg (i.castAdd 7))) = [separator] ∧
      S.R (ext (reg (i.castAdd 7))) = binSyms (![K,N,D] i).size (![K,N,D] i)) →
    (∀ i : Fin 7, S.R (ext (reg (i.natAdd 3))) = []) →
    (∀ k (j : Fin 7), S.L (ext (bank k j.succ)) = [] ∧ S.R (ext (bank k j.succ)) = []) →
    ∃ z F steps, Exec (fun g => embProg ext id (body g)) code (mk u S) steps (mk z F) ∧
      (∀ js : List _, js.Nodup → steps+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+rate*(D*(N*K))) ∧
      z.user = u.user ∧ HelperFan (stageOutputFan n placedFan)
        (singleLabelBank label (Function.update (collapseLabelBank (B := B) (K := K) out)
          (Fin.last 142080) (fun _ => 0))) F := by
  intro I
  obtain ⟨states,build⟩ := scanRestoredTargetsWithCharge n
  refine ⟨max states 215,?_⟩
  intro T Q P U fan fits inner placedFan bank reg ext body
  obtain ⟨scan,scanRate,scanRun⟩ := build fan ((le_max_left _ _).trans fits) body
  let src : Fin 3 → Fin (T+14) := fun i : Fin 3 => (((i.castAdd 7).castAdd 4).natAdd T : Fin (T+14))
  have apart (i j) : placedFan i ≠ src j := by
    intro eq
    have h := congrArg Fin.val eq
    change (fan i).val = T+j.val at h
    exact (fan i).isLt.not_ge (h ▸ Nat.le_add_right T j.val)
  obtain ⟨combined,rate,run⟩ := scannedStageWithHandoffCharge (T := T+14) n placedFan ((le_max_right _ _).trans fits)
    src apart body scan
  refine ⟨combined,scanRate+rate,?_⟩
  intro w B W x K N D label hk hb u S y out restored fresh trace labels dims free scratch
  obtain ⟨v,A,m,ran,paid,user,words,controls,headers,_,retained⟩ :=
    scanRun w B W label x hk hb (embDn ext u) (embStk ext S) y out (projectedScanFan _ ext out S restored) trace labels dims free scratch
  have targets (k : I) := scannedPayload _ A _ (words k)
  obtain ⟨z,F,t,exec,cost,same,ready,_,_⟩ :=
    run w B W hb hk x y out u S v A m (scanRate*(D*(N*K)))
      ran paid (user.trans (projectedScanUser ext u)) fresh headers controls retained targets trace labels
  exact ⟨z,F,t,exec,fun js unique => scanTotal (cost js unique),same,ready⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
