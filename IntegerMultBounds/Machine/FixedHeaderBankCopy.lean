import IntegerMultBounds.Machine.BinaryDescriptorInstall
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.RecursiveDimensionBank

/-! A fixed finite family of actual descriptor copies from retained caller
tapes into a private header bank, followed by paid physical bank cleanup. -/
namespace IntegerMultBounds.Machine.FixedHeaderBankCopy
noncomputable section
variable {t n a : ℕ}
open SharedPlacementAlphabet (setTape)

def empty (n : ℕ) : Tapes n a := ⟨fun _ => 0,fun _ _ => blank⟩
def bank (ds : Fin n → Option (List Bool)) : Tapes n a :=
  ⟨fun i => RecursiveDimensionBank.head (ds i),fun i => RecursiveDimensionBank.tape (ds i)⟩
def headerBank (bs : Fin n → List Bool) : Tapes n a := bank (fun i => some (bs i))
def source (focus : Fin n → Fin t) (i : Fin n) : Fin (t+n) := Fin.castAdd n (focus i)
def target (i : Fin n) : Fin (t+n) := Fin.natAdd t i

theorem distinct (focus : Fin n → Fin t) (i : Fin n) : source focus i ≠ target i := by
  intro h
  have he := congrArg Fin.val h
  simp only [source,target,Fin.val_castAdd,Fin.val_natAdd] at he
  have hi := (focus i).isLt
  omega

def oneProgram (focus : Fin n → Fin t) (i : Fin n) : Program (t+n) 5 a :=
  BinaryDescriptorInstall.program a (source focus i) (target i) (distinct focus i)
def states : List (Fin n) → ℕ | [] => 1 | _::ops => 5+states ops
def listProgram (ht : 0 < t+n) (focus : Fin n → Fin t) :
    (ops : List (Fin n)) → Program (t+n) (states ops) a
  | [] => skip (t+n) a ht
  | i::ops => seq (oneProgram focus i) (listProgram ht focus ops)
def ops (n : ℕ) : List (Fin n) := List.ofFn id
def program (ht : 0 < t+n) (focus : Fin n → Fin t) := listProgram (a := a) ht focus (ops n)
def cost (ops : List (Fin n)) (bs : Fin n → List Bool) :=
  (ops.map (fun i => 2*(bs i).length+6)).sum

def filled (bs : Fin n → List Bool) : List (Fin n) → (Fin n → Option (List Bool)) →
    Fin n → Option (List Bool)
  | [],ds => ds
  | i::ops,ds => filled bs ops (Function.update ds i (some (bs i)))

private theorem append_set_target (caller : Tapes t a) (ds : Fin n → Option (List Bool))
    (i : Fin n) (xs : List Bool) :
    setTape (caller.append (bank ds)) (target i) (RadixZeroFill.encodedBinary xs) 1 =
      caller.append (bank (Function.update ds i (some xs))) := by
  apply congrArg₂ Tapes.mk <;> funext j <;> induction j using Fin.addCases with
  | left j =>
    have hn : Fin.castAdd n j ≠ target (t := t) i := by
      intro h; have hv := congrArg Fin.val h
      simp only [target,Fin.val_castAdd,Fin.val_natAdd] at hv
      have hj := j.isLt
      omega
    simp [Tapes.append,bank,hn]
  | right j =>
    by_cases hj : j = i
    · subst j; simp [Tapes.append,bank,target,RecursiveDimensionBank.head,RecursiveDimensionBank.tape]
    · have hn : Fin.natAdd t j ≠ target (t := t) i := by
        simpa [target,Fin.ext_iff] using hj
      simp [Tapes.append,bank,hj,target]

private theorem filled_frame (bs : Fin n → List Bool) (os : List (Fin n))
    (ds : Fin n → Option (List Bool)) (i : Fin n) (hi : i ∉ os) : filled bs os ds i = ds i := by
  induction os generalizing ds with
  | nil => rfl
  | cons j os ih =>
    have hn : i ≠ j := fun h => hi (List.mem_cons.mpr (Or.inl h))
    rw [filled,ih _ (fun h => hi (List.mem_cons_of_mem _ h)),Function.update_of_ne hn]

private theorem filled_slot (bs : Fin n → List Bool) (os : List (Fin n)) (hu : os.Nodup)
    (ds : Fin n → Option (List Bool)) (i : Fin n) (hi : i ∈ os) :
    filled bs os ds i = some (bs i) := by
  induction os generalizing ds with
  | nil => exact (List.not_mem_nil hi).elim
  | cons j os ih =>
    have hh := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [filled,filled_frame _ _ _ _ hh.1,Function.update_self]
    · exact ih hh.2 _ hi

theorem list_constructs (ht : 0 < t+n) (focus : Fin n → Fin t) (bs : Fin n → List Bool)
    (os : List (Fin n)) (hu : os.Nodup) (caller : Tapes t a)
    (hs : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (bs i))
    (hh : ∀ i, caller.head (focus i) = 1) (ds : Fin n → Option (List Bool))
    (hd : ∀ i ∈ os, ds i = none) :
    HoareTime (listProgram ht focus os) (fun z => z = caller.append (bank ds))
      (fun z => z = caller.append (bank (filled bs os ds))) (cost os bs) := by
  induction os generalizing ds with
  | nil => exact skip_hoare ht _
  | cons i os ih =>
    have hu' := List.nodup_cons.mp hu
    have h0 := BinaryDescriptorInstall.install_hoare (source focus i) (target i)
      (distinct focus i) (caller.append (bank ds)) (bs i)
      (by simpa [source,Tapes.append] using hs i)
      (by simpa [source,Tapes.append] using hh i)
      (by simp [target,Tapes.append,bank,hd i List.mem_cons_self,RecursiveDimensionBank.tape])
      (by simp [target,Tapes.append,bank,hd i List.mem_cons_self,RecursiveDimensionBank.head])
    rw [append_set_target] at h0
    have hn := ih hu'.2 (Function.update ds i (some (bs i))) (by
      intro j hj
      have hji : j ≠ i := fun h => hu'.1 (h ▸ hj)
      rw [Function.update_of_ne hji]
      exact hd j (List.mem_cons_of_mem _ hj))
    exact (h0.seq hn).consequence (fun _ h => h) (fun _ h => h)
      (by simp only [cost,List.map_cons,List.sum_cons]; omega)

private theorem ops_nodup : (ops n).Nodup := by
  simpa [ops,List.nodup_ofFn] using (Function.injective_id : Function.Injective (id : Fin n → Fin n))
private theorem ops_mem (i : Fin n) : i ∈ ops n := by simp [ops]

theorem constructs (ht : 0 < t+n) (focus : Fin n → Fin t) (bs : Fin n → List Bool)
    (caller : Tapes t a)
    (hs : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (bs i))
    (hh : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program ht focus) (fun z => z = caller.append (empty n))
      (fun z => z = caller.append (headerBank bs)) (cost (ops n) bs) := by
  have h := list_constructs ht focus bs (ops n) ops_nodup caller hs hh (fun _ => none)
    (by intro i hi; rfl)
  have hf : filled bs (ops n) (fun _ => none) = fun i => some (bs i) := by
    funext i
    exact filled_slot bs (ops n) ops_nodup _ i (ops_mem i)
  rw [hf] at h
  exact h

theorem cost_le (os : List (Fin n)) (bs : Fin n → List Bool) (L : ℕ)
    (hl : ∀ i ∈ os, (bs i).length ≤ L) : cost os bs ≤ os.length*(2*L+6) := by
  induction os with
  | nil => simp [cost]
  | cons i os ih =>
    have h0 := hl i List.mem_cons_self
    have hn := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    simp only [cost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

theorem cost_linear (bs : Fin n → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (bs i)) (hv : ∀ i, Counter.value (bs i) ≤ V) :
    cost (ops n) bs ≤ 10*n*V := by
  have hl (i : Fin n) : (bs i).length ≤ V+1 :=
    (GrowingCounterData.canonical_width _ (hc i)).trans
      (Nat.add_le_add_right ((Nat.log2_le_self _).trans (hv i)) 1)
  have h := cost_le (ops n) bs (V+1) (fun i _ => hl i)
  simp only [ops,List.length_ofFn] at h
  have hk : 2*(V+1)+6 ≤ 10*V := by omega
  simpa [ops,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h.trans (Nat.mul_le_mul_left n hk)

theorem constructs_linear (ht : 0 < t+n) (focus : Fin n → Fin t)
    (bs : Fin n → List Bool) (caller : Tapes t a)
    (hs : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (bs i))
    (hh : ∀ i, caller.head (focus i) = 1) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (bs i)) (hv : ∀ i, Counter.value (bs i) ≤ V) :
    HoareTime (program ht focus) (fun z => z = caller.append (empty n))
      (fun z => z = caller.append (headerBank bs)) (10*n*V) :=
  (constructs ht focus bs caller hs hh).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear bs V hV hc hv)

def cleanupSlots (t n : ℕ) : List (Fin (t+n)) := (ops n).map (target (t := t))
def cleanup (ht : 0 < t+n) := BinaryDescriptorCleanupList.program (a := a) ht (cleanupSlots t n)
def wordsAt (bs : Fin n → List Bool) : Fin (t+n) → List Bool := Fin.addCases (fun _ => []) bs

def cleanupCost (bs : Fin n → List Bool) :=
  BinaryDescriptorCleanupList.cost (cleanupSlots t n) (wordsAt (t := t) bs)

private theorem target_injective : Function.Injective (target (t := t) (n := n)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [target,Fin.val_natAdd] at hv
  omega

private theorem cleanupSlots_nodup : (cleanupSlots t n).Nodup :=
  List.Nodup.map target_injective ops_nodup

private theorem cleanup_descriptors (caller : Tapes t a) (bs : Fin n → List Bool)
    (i : Fin (t+n)) (hi : i ∈ cleanupSlots t n) :
    (caller.append (headerBank bs)).head i = 1 ∧
    (caller.append (headerBank bs)).tape i = BinaryDescriptorStack.descriptor (wordsAt bs i) := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  constructor
  · simp [target,Tapes.append,headerBank,bank,RecursiveDimensionBank.head]
  · simpa [target,Tapes.append,headerBank,bank,wordsAt,RecursiveDimensionBank.tape] using
      (BinaryDescriptorStackRoundtrip.descriptor_encoded (a := a) (bs j)).symm

private theorem cleanup_cleared (caller : Tapes t a) (bs : Fin n → List Bool) :
    BinaryDescriptorCleanupList.cleared (cleanupSlots t n) (caller.append (headerBank bs)) =
      caller.append (empty n) := by
  have hleft (i : Fin t) : Fin.castAdd n i ∉ cleanupSlots t n := by
    intro hi
    obtain ⟨j,_,hj⟩ := List.mem_map.mp hi
    have hv := congrArg Fin.val hj
    simp only [target,Fin.val_natAdd,Fin.val_castAdd] at hv
    have h := i.isLt
    omega
  have hright (i : Fin n) : target (t := t) i ∈ cleanupSlots t n :=
    List.mem_map.mpr ⟨i,ops_mem i,rfl⟩
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases with
    | left i => simpa [Tapes.append] using (BinaryDescriptorCleanupList.cleared_frame _ (caller.append (headerBank bs)) _ (hleft i)).1
    | right i => simpa [Tapes.append,empty,target] using (BinaryDescriptorCleanupList.cleared_slot _ cleanupSlots_nodup (caller.append (headerBank bs)) _ (hright i)).1
  · funext i
    induction i using Fin.addCases with
    | left i => simpa [Tapes.append] using (BinaryDescriptorCleanupList.cleared_frame _ (caller.append (headerBank bs)) _ (hleft i)).2
    | right i => simpa [Tapes.append,empty,target] using (BinaryDescriptorCleanupList.cleared_slot _ cleanupSlots_nodup (caller.append (headerBank bs)) _ (hright i)).2

theorem cleans (ht : 0 < t+n) (caller : Tapes t a) (bs : Fin n → List Bool) :
    HoareTime (cleanup ht) (fun z => z = caller.append (headerBank bs))
      (fun z => z = caller.append (empty n)) (cleanupCost (t := t) bs) := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare ht (cleanupSlots t n)
    cleanupSlots_nodup (wordsAt bs) (caller.append (headerBank bs)) (cleanup_descriptors caller bs)
  rw [cleanup_cleared] at h
  exact h

theorem cleanup_cost_linear (bs : Fin n → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (bs i)) (hv : ∀ i, Counter.value (bs i) ≤ V) :
    cleanupCost (t := t) bs ≤ 9*n*V := by
  have hl (i : Fin n) : (bs i).length ≤ V+1 :=
    (GrowingCounterData.canonical_width _ (hc i)).trans
      (Nat.add_le_add_right ((Nat.log2_le_self _).trans (hv i)) 1)
  have h := BinaryDescriptorCleanupList.cost_le (cleanupSlots t n) (wordsAt bs) (V+1) (by
    intro i hi
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    simpa [wordsAt,target] using hl j)
  simp only [cleanupSlots,List.length_map,ops,List.length_ofFn] at h
  have hk : 2*(V+1)+5 ≤ 9*V := by omega
  simpa [cleanupCost,cleanupSlots,ops,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
    h.trans (Nat.mul_le_mul_left n hk)

theorem cleans_linear (ht : 0 < t+n) (caller : Tapes t a) (bs : Fin n → List Bool)
    (V : ℕ) (hV : 0 < V) (hc : ∀ i, GrowingCounterData.Canonical (bs i))
    (hv : ∀ i, Counter.value (bs i) ≤ V) :
    HoareTime (cleanup ht) (fun z => z = caller.append (headerBank bs))
      (fun z => z = caller.append (empty n)) (9*n*V) :=
  (cleans ht caller bs).consequence (fun _ h => h) (fun _ h => h)
    (cleanup_cost_linear bs V hV hc hv)

end
end IntegerMultBounds.Machine.FixedHeaderBankCopy
