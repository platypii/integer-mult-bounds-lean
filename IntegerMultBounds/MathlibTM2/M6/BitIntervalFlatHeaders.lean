module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalSeededRecord
public import IntegerMultBounds.MathlibTM2.M6.BitHelperParentSeeds

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout IntervalDescriptor
open Shared50ModularControl (prime)

/-- The two leading dimensions of an interval are one. Its other three
spectator factors occupy descriptor fields 2, 4 and 5. -/
def intervalSpectatorPorts : Fin 11 ↪ Fin 72 := ⟨![35,37,38,59,65,60,61,62,63,64,58],by decide⟩

def intervalFlatSources : Fin 6 → Fin 72 := ![33,33,33,36,33,65]

theorem flatSpectatorVolume (lane : Descriptor) {atom : ℕ} (width : lane.width = 64*atom) :
    volume prime (flatNodeDescriptor atom (CopyChildLayout.spectators lane)) = volume prime lane := by
  simp only [volume,flatNodeDescriptor,CopyChildLayout.spectators,width,one_mul,mul_one]
  ring

theorem flatSpectators_le_volume (lane : Descriptor) :
    CopyChildLayout.spectators lane ≤ volume prime lane := by
  have pos := pow_pos Shared50ModularControl.prime_prime.pos lane.width
  calc
    _ ≤ CopyChildLayout.spectators lane * ((prime^lane.width)*(prime^lane.width)) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos pos pos)
    _ = _ := by unfold CopyChildLayout.spectators volume; ring

theorem intervalFlatHeaders_exec {P U : Type} {T Q : ℕ} (host : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (lo hi w W axes atom : ℕ) (positive : 0 < W) :
    let lane := phaseIntervalChild lo hi w W axes
    let count := CopyChildLayout.spectators lane
    let flat := flatNodeDescriptor atom count
    lane.width = 64*atom →
    ∀ u S, (∀ i, S.R (bank (descriptorPorts i)) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j : Fin 72, 59 ≤ j.val → j.val ≤ 65 → S.R (bank j) = []) →
      ∃ v D n, Exec host (middleRowDescriptor (intervalSpectatorPorts.trans bank)) (mk u S) n (mk v D) ∧
        v.user = u.user ∧ n ≤ 432*count ∧
        (∀ i, D.R (bank (intervalFlatSources i)) = (Routines.hdr flat i).map bitSymbol) ∧
        (∀ js : List _, js.Nodup → n+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+434*count) ∧
        D.L = S.L ∧ ∀ j, j ≠ bank 65 → D.R j = S.R j := by
  intro lane count flat width u S fields empty
  let r := intervalSpectatorPorts.trans bank
  have digits (i) := (fields i).trans (canonicalBits_symbols _)
  have pos := pow_pos Shared50ModularControl.prime_prime.pos w
  obtain ⟨v,n,user,paid,exec⟩ := seedProduct_exec host r lane.beforeH lane.between lane.afterD
    (pow_pos pos _) (pow_pos pos _) (Nat.mul_pos (pow_pos pos _) positive) u S
    (digits 2) (digits 4) (digits 5) (fun i lo hi => by
      obtain ⟨a,b⟩ := (by decide : ∀ j : Fin 11, 3 ≤ j → j < 10 →
        59 ≤ (intervalSpectatorPorts j).val ∧ (intervalSpectatorPorts j).val ≤ 65) i lo hi
      exact empty _ a b)
  have product : lane.beforeH*lane.between*lane.afterD = count := by
    simp [count,CopyChildLayout.spectators,lane,phaseIntervalChild]
  rw [product] at exec paid
  refine ⟨v,_,n,exec,user,paid,?_,?_,rfl,fun j ne => Function.update_of_ne ne ..⟩
  swap
  · intro js unique
    have growth := prependedWordCharge S (bank 65) (binSyms count.size count) js unique
    simp only [empty 65 (by decide) (by decide),List.append_nil,length_binSyms] at growth
    have size : count.size ≤ count := Nat.size_le.mpr Nat.lt_two_pow_self
    change n+tapeCharge cleanupWeight js {S with R := Function.update S.R (bank 65) _} ≤ _
    omega
  intro i
  have unit : S.R (bank 33) = (FlatCoordinateSchedule.bits 1).map bitSymbol := fields 0
  have active : S.R (bank 36) = (FlatCoordinateSchedule.bits (64*atom)).map bitSymbol := by
    rw [← width]
    exact fields 3
  change Function.update S.R (bank 65) (binSyms count.size count) (bank (intervalFlatSources i)) = _
  fin_cases i <;> first
    | (rw [Function.update_of_ne (bank.injective.ne (by decide))]; exact unit)
    | (rw [Function.update_of_ne (bank.injective.ne (by decide))]; exact active)
    | (change Function.update S.R (bank 65) _ (bank 65) = _; rw [Function.update_self]; exact (canonicalBits_symbols count).symm)

end IntegerMultBounds.MathlibTM2.M6.BitNode
