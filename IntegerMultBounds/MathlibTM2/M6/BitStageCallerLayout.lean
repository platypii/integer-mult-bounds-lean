module

public import IntegerMultBounds.MathlibTM2.M6.BitStageSetupSeed
public import IntegerMultBounds.MathlibTM2.M6.BitParkedPackedChild
public import IntegerMultBounds.MathlibTM2.M6.BitCleanupBound

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Cover Certificates.PR589 Certificates.PR589.Nine RecursiveInterchangeLayout

def callerHeaderPorts : Fin 6 ↪ Fin 37 := Fin.castAddEmb 31
private def clocks : Fin 7 ↪ Fin 37 := ⟨![3,6,7,8,9,10,11],by decide⟩
private def powers : Fin 10 ↪ Fin 37 := ⟨![6,12,13,14,15,16,17,18,19,20],by decide⟩
private def divider : Fin 11 ↪ Fin 37 := ⟨fun j => ⟨23+j.val,by omega⟩,by
  intro i j h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩

def callerHeaderBank (words : Fin 6 → List (Fin (prime+4))) (i : Fin 37) :=
  if h : i.val < 6 then words ⟨i.val,h⟩ else []

/-- Copy the six live header words into the external stage bank. Several
fields may come from the same caller tape. -/
theorem loadCallerHeaderBank {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 37 ↪ Fin T) (source : Fin 6 → Fin T) (tmp saved : Fin T)
    (apart : ∀ i j, bank (callerHeaderPorts i) ≠ source j)
    (regs : ∀ i, [source i,bank (callerHeaderPorts i),tmp,saved].Nodup) :
    ∃ code : Pr P T Q prime U, ∀ u (S : Stacks T prime),
      let words := fun i => S.R (source i)
      (∀ i, S.R (bank i) = []) → S.R tmp = [] → S.R saved = [] →
      ∃ v R n, Exec body code (mk u S) n (mk v {S with R := R}) ∧ v.user = u.user ∧
        CleanupBound S {S with R := R} n (seedLoadBill words) ∧
        (∀ i, R (bank i) = callerHeaderBank words i) ∧
        ∀ j, (∀ i, bank (callerHeaderPorts i) ≠ j) → R j = S.R j := by
  obtain ⟨code,load⟩ := installChildSeed body bank callerHeaderPorts source tmp saved apart regs
  refine ⟨code,?_⟩
  intro u S words vacant ht hs
  let seed : Stacks 37 prime := ⟨[],[],fun _ => [],callerHeaderBank words⟩
  have word (i : Fin 6) : seed.R (callerHeaderPorts i) = words i := dif_pos i.isLt
  obtain ⟨v,R,n,exec,user,bill,loaded,off⟩ := load seed u S (fun i => (word i).symm)
    (fun i => vacant _) ht hs
  refine ⟨v,R,n,exec,user,?_,?_,off⟩
  · intro js nd
    change n+tapeCharge cleanupWeight js _ ≤ tapeCharge cleanupWeight js S+seedLoadBill words
    simpa only [word] using bill js nd
  · intro j
    apply loaded
    intro outside
    rw [vacant]
    change [] = callerHeaderBank words j
    unfold callerHeaderBank
    have h : ¬ j.val < 6 := fun lt => outside ⟨j.val,lt⟩ (Fin.ext rfl)
    simp [h]

/-- The external bank starts with six descriptor words and blank scratch tapes. -/
def CallerHeaderInput {H : ℕ} (source : Fin 6 → Fin (H+37)) (r : Fin 7 ↪ Fin (H+37))
    (power : Fin 10 ↪ Fin (H+37)) (tmp saved : Fin (H+37)) (dim : Fin 6 ↪ Fin (H+37))
    (division : Fin 11 ↪ Fin (H+37)) : Prop :=
  ∀ words : Fin 6 → List (Fin (prime+4)),
    ∀ R : Fin (H+37) → List (Fin (prime+4)), (∀ i : Fin 37, R (i.natAdd H) = callerHeaderBank words i) →
    (∀ i, R (source i) = words i) ∧ (∀ i, i ≠ 0 → R (r i) = []) ∧
    (∀ i, i ≠ 0 → R (power i) = []) ∧ R tmp = [] ∧ R saved = [] ∧ (∀ i, R (division i) = []) ∧
    R (dim 3) = [] ∧ R (dim 4) = [] ∧ R (dim 5) = []

/-- Place the caller's descriptor and scratch tapes after the stage. Two
dimension inputs borrow words already installed in the archive. -/
theorem stageCallerLayout {H T : ℕ} (owner : Fin T ↪ Fin H)
    (archive : Fin (80+273) ↪ Fin H) (separate : ∀ i h, archive i ≠ owner h) :
    let place := Fin.castAddEmb 37 (n := H)
    let bank := archive.trans place
    ∃ (source : Fin 6 → Fin (H+37)) (r : Fin 7 ↪ Fin (H+37)) (power : Fin 10 ↪ Fin (H+37))
      (tmp saved : Fin (H+37)) (dimensions : Fin 6 ↪ Fin (H+37)) (division : Fin 11 ↪ Fin (H+37)),
    CallerHeaderInput source r power tmp saved dimensions division ∧
    division 2 = dimensions 1 ∧ (∀ i j, place j ≠ division i) ∧
    (∀ i, outsideArchiveOutputs r power (division i) ∧ division i ≠ dimensions 3) ∧
    dimensions 0 = bank (parentArchivePorts 6) ∧ dimensions 2 = bank (parentArchivePorts 7) ∧
    (∀ j : Fin 6, j ≠ 0 → j ≠ 2 → outsideArchiveOutputs r power (dimensions j) ∧ ∀ i, bank i ≠ dimensions j) ∧
    (∀ j, place j ≠ dimensions 3) ∧
    [bank (parentArchivePorts 3),dimensions 3,dimensions 4,dimensions 5].Nodup ∧
    (∀ j h, place (owner h) ≠ dimensions j) ∧
    r 0 = source 3 ∧ power 0 = r 1 ∧ (∀ i, r 2 ≠ power i) ∧
    (∀ i, outsideArchiveOutputs r power (source i)) ∧
    (∀ i, outsideArchiveOutputs r power (place i)) ∧
    outsideArchiveOutputs r power tmp ∧ outsideArchiveOutputs r power saved ∧
    (∀ i j, bank (parentArchivePorts i) ≠ descriptorArchiveSources source r power j) ∧
    ∀ i, [descriptorArchiveSources source r power i,bank (parentArchivePorts i),tmp,saved].Nodup := by
  intro place bank
  let ext := Fin.natAddEmb H (m := 37)
  have apart (i : Fin H) (j : Fin 37) : place i ≠ ext j := fun eq => by
    have h := congrArg Fin.val eq
    change i.val = H+j.val at h
    omega
  let r := clocks.trans ext
  let power := powers.trans ext
  let src := callerHeaderPorts.trans ext
  let dims : Fin 6 → Fin (H+37) := ![bank (parentArchivePorts 6),ext (divider 2),bank (parentArchivePorts 7),ext 34,ext 35,ext 36]
  have inj : Function.Injective dims := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> first | rfl | exact False.elim (apart _ _ eq) | exact False.elim (apart _ _ eq.symm) |
      exact False.elim (ext.injective.ne (by decide) eq) | exact False.elim (bank.injective.ne (parentArchivePorts.injective.ne (by decide)) eq)
  let dim : Fin 6 ↪ Fin (H+37) := ⟨dims,inj⟩
  have safe (i : Fin 37) (h : outsideArchiveOutputs clocks powers i) : outsideArchiveOutputs r power (ext i) :=
    ⟨ext.injective.ne h.1,ext.injective.ne h.2.1,ext.injective.ne h.2.2.1,ext.injective.ne h.2.2.2⟩
  have inside (i : Fin H) : outsideArchiveOutputs r power (place i) := ⟨apart i (clocks 1),apart i (clocks 2),apart i (powers 1),apart i (powers 3)⟩
  have sourceAt (i : Fin 9) : descriptorArchiveSources src r power i = ext (descriptorArchiveSources callerHeaderPorts clocks powers i) := by
    fin_cases i <;> rfl
  refine ⟨src,r,power,ext 21,ext 22,dim,divider.trans ext,?_,rfl,fun i j => apart j _,?_,rfl,rfl,?_,
    fun j => apart j _,?_,?_,rfl,rfl,?_,?_,inside,?_,?_,?_,?_⟩
  · intro words
    intro R read
    have empty (i : Fin 37) (h : 6 ≤ i.val) : R (ext i) = [] :=
      (read i).trans (dif_neg (Nat.not_lt_of_ge h))
    refine ⟨fun i => (read (callerHeaderPorts i)).trans (dif_pos i.isLt),?_,?_,empty 21 (by decide),
      empty 22 (by decide),?_,empty 34 (by decide),empty 35 (by decide),empty 36 (by decide)⟩
    · exact fun i ne => empty _ ((by decide : ∀ i : Fin 7, i ≠ 0 → 6 ≤ (clocks i).val) i ne)
    · exact fun i _ => empty _ ((by decide : ∀ i : Fin 10, 6 ≤ (powers i).val) i)
    · exact fun i => empty _ ((by decide : ∀ i : Fin 11, 6 ≤ (divider i).val) i)
  · intro i
    exact ⟨safe _ ((by unfold outsideArchiveOutputs; decide : ∀ i, outsideArchiveOutputs clocks powers (divider i)) i),
      ext.injective.ne ((by decide : ∀ i, divider i ≠ 34) i)⟩
  · intro j h0 h2
    fin_cases j <;> first | contradiction | exact ⟨safe _ (by unfold outsideArchiveOutputs; decide),fun i => apart _ _⟩
  · change [place _,ext 34,ext 35,ext 36].Nodup
    simp [List.nodup_cons,apart,ext.injective.eq_iff]
  · intro j h
    fin_cases j <;> first | exact apart _ _ | exact place.injective.ne (separate _ _).symm
  · exact fun i => ext.injective.ne ((by decide : ∀ i, clocks 2 ≠ powers i) i)
  · exact fun i => safe _ ((by unfold outsideArchiveOutputs; decide : ∀ i, outsideArchiveOutputs clocks powers (callerHeaderPorts i)) i)
  · exact safe _ (by unfold outsideArchiveOutputs; decide)
  · exact safe _ (by unfold outsideArchiveOutputs; decide)
  · intro i j
    rw [sourceAt]
    exact apart _ _
  · intro i
    rw [sourceAt]
    have clean := (by decide : ∀ i, descriptorArchiveSources callerHeaderPorts clocks powers i ≠ 21 ∧
      descriptorArchiveSources callerHeaderPorts clocks powers i ≠ 22) i
    change [ext _,place _,ext 21,ext 22].Nodup
    simp [List.nodup_cons,apart,Ne.symm (apart _ _),ext.injective.eq_iff,clean]

end IntegerMultBounds.MathlibTM2.M6.BitNode
