module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyChildLayout
public import IntegerMultBounds.MathlibTM2.M6.BitChildCorrection

/-! Read the ordinary recursive transpose in a single PR589 parent record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Address)
open FlatCoordinateLayout (rankEquiv)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Move the first digit past the remaining digits, then reverse those digits. -/
def reverseDigitSchedule : ℕ → List ℕ
  | 0 => []
  | n+1 => middleTailSchedule 1 n ++ reverseDigitSchedule n

theorem reverseDigitSchedule_inside {n i : ℕ} (used : i ∈ reverseDigitSchedule n) :
    i+1 < n := by
  induction n with
  | zero => simp [reverseDigitSchedule] at used
  | succ n ih =>
    rcases List.mem_append.mp used with h | h
    · have := middleTailSchedule_inside h
      omega
    · exact Nat.lt_succ_of_lt (ih h)

theorem reverseDigitSchedule_reverses {α : Type*} (digits suffix : List α) :
    (reverseDigitSchedule digits.length).foldl (fun xs i => swapAtomAt i xs)
      (digits++suffix) = digits.reverse++suffix := by
  induction digits generalizing suffix with
  | nil => rfl
  | cons x xs ih =>
    have move := middleTailSchedule_packs [x] xs suffix
    simp only [List.length_singleton,List.nil_append,List.append_assoc,List.cons_append] at move
    simp only [List.length_cons,reverseDigitSchedule,List.foldl_append,List.cons_append,
      move,ih,List.reverse_cons,List.append_assoc,List.nil_append]

def ordinaryChildPackSchedule (r g : ℕ) : List ℕ :=
  (reverseDigitSchedule r).map ((r+g+g)+·)

theorem ordinaryChildPackSchedule_inside {r g i : ℕ} (used : i ∈ ordinaryChildPackSchedule r g) :
    i+1 < (r+g)+(r+g) := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp used
  have := reverseDigitSchedule_inside hj
  omega

theorem ordinaryChildPackSchedule_fields {α : Type*} {r g : ℕ}
    (x : Fin ((r+g)+(r+g)) → α) (pre tail : List α)
    (hp : pre.length = r+g+g) (ht : tail.length = r) (layout : List.ofFn x = pre++tail) :
    List.ofFn ((ordinaryChildPackSchedule r g).foldl adjacentFields x) = pre++tail.reverse := by
  rw [fold_adjacentFields _ _ (fun _ => ordinaryChildPackSchedule_inside),layout]
  unfold ordinaryChildPackSchedule
  rw [← hp,← ht,List.foldl_map]
  change (reverseDigitSchedule tail.length).foldl (fun ys i => swapAtomAt (pre.length+i) ys) (pre++tail) = _
  rw [fold_swapAtomAt_prefix]
  simpa using congrArg (pre++·) (reverseDigitSchedule_reverses tail [])

noncomputable def ordinaryChildDescriptor (r g w W : ℕ) : Descriptor :=
  ⟨1,1,1,(w+1)*r,(prime^(w+1))^(g+g),W⟩

theorem ordinaryAtomWidth (r w : ℕ) : (prime^(w+1))^r = prime^((w+1)*r) := (pow_mul ..).symm

/-- Read a recursive cell in the parent record, splitting the middle field
into the two inactive slices and reversing the active tail digits. -/
noncomputable def ordinaryRecursivePosition (r g w W : ℕ)
    (i : Fin (volume prime (ordinaryChildDescriptor r g w W))) :
    Fin ((prime^(w+1))^((r+g)+(r+g))*W) :=
  let a := (CopyChildLayout.flatAddress _).symm i
  let unpack := fun k : Fin (prime^((w+1)*r)) => rankEquiv.symm (k.cast (ordinaryAtomWidth r w).symm)
  let gaps : Fin (g+g) → ZMod (prime^(w+1)) := rankEquiv.symm a.middle
  let fields := childFields (fun j : Fin g => gaps (j.castAdd g)) (fun j : Fin g => gaps (j.natAdd g))
    (unpack a.h,fun k => unpack a.d k.rev)
  FlatCoordinateLayout.index (Fin.append fields.1 fields.2) a.after

noncomputable def ordinaryChildAddress {r g w W : ℕ} (hg tg : Fin g → ZMod (prime^(w+1)))
    (h d : Fin r → ZMod (prime^(w+1))) (j : Fin W) : Address (ordinaryChildDescriptor r g w W) :=
  ⟨(0 : Fin 1),(0 : Fin 1),(0 : Fin 1),(rankEquiv h).cast (ordinaryAtomWidth r w),
    rankEquiv (Fin.append hg tg),(rankEquiv d).cast (ordinaryAtomWidth r w),j⟩

/-- The physical packing schedule puts every parent cell at its recursive tape offset. -/
theorem ordinaryChildPackSchedule_index {r g w W : ℕ} (hg tg : Fin g → ZMod (prime^(w+1)))
    (h d : Fin r → ZMod (prime^(w+1))) (j : Fin W) :
    let t := childFields hg tg (h,fun k => d k.rev)
    let packed := (ordinaryChildPackSchedule r g).foldl adjacentFields (Fin.append t.1 t.2)
    (FlatCoordinateLayout.index packed j).val =
      (RecursiveInterchangeScaling.index (ordinaryChildAddress hg tg h d j)).val := by
  intro t packed
  let fields := Fin.append (Fin.append h (Fin.append hg tg)) d
  have sizes : (r+g)+(r+g) = (r+(g+g))+r := by omega
  have castList {a b : ℕ} (eqn : a = b) (x : Fin b → ZMod (prime^(w+1))) :
      List.ofFn (fun i => x (i.cast eqn)) = List.ofFn x := by subst b; rfl
  have rev : List.ofFn (fun i => d i.rev) = (List.ofFn d).reverse := by
    apply List.ext_getElem
    · simp
    · intros
      simp [Fin.rev,Nat.sub_sub,Nat.add_comm]
  have order : packed = fun i => fields (i.cast sizes) := by
    apply List.ofFn_injective
    rw [castList]
    apply (ordinaryChildPackSchedule_fields _ (List.ofFn h ++ List.ofFn hg ++ List.ofFn tg)
      (List.ofFn (fun i => d i.rev)) (by simp [Nat.add_assoc]) (by simp) ?_).trans
    · simp [fields,List.ofFn_fin_append,rev,List.append_assoc]
    · simp only [t,childFields,List.ofFn_fin_append,castList,List.append_assoc]
  have castRank {a b : ℕ} (eqn : a = b) (x : Fin b → ZMod (prime^(w+1))) :
      (FlatCoordinateLayout.rank (fun i => x (i.cast eqn))).val = (FlatCoordinateLayout.rank x).val := by
    subst b; rfl
  rw [order,FlatCoordinateLayout.index_val,castRank,RecursiveInterchangeScaling.index_val]
  rw [show (FlatCoordinateLayout.rank fields).val = _ from ArbitraryWidthSliceTranspose.rank_append (Fin.append h (Fin.append hg tg)) d,
    show (FlatCoordinateLayout.rank (Fin.append h (Fin.append hg tg))).val = _ from ArbitraryWidthSliceTranspose.rank_append h (Fin.append hg tg)]
  simp only [ordinaryChildAddress,
    ordinaryChildDescriptor,RecursiveInterchangeLayout.index,Fin.val_zero,zero_mul,zero_add,
    ← ordinaryAtomWidth]
  rfl

/-- On the packer's tape bank the fieldwise invariant is exactly the read
contract of the ordinary recursive call. The reverse direction supplies the
unpacker with its input after the child has returned. -/
theorem ordinaryChildPackedRecord_iff {r g w W H J T A : ℕ} {α : Type}
    (bank : Fin 35 ↪ Fin T) (record : List (Fin (A+4))) (sym : α → Fin 4)
    (src dst : ℤ → Fin 4) (p q : ℤ) (S : Host.Stacks T A)
    (original : Fin ((prime^(w+1))^((r+g)+(r+g))*W) → α) :
    ColumnRecordReady bank H J record sym src dst p q original
      (fun x => (ordinaryChildPackSchedule r g).foldl adjacentFields x) S ↔
    ∃ word, RecordReady (b := prime) (w := w) (W := W) (d := (r+g)+(r+g))
      bank H J record sym src dst p q word S ∧
      ∀ (hg tg : Fin g → ZMod (prime^(w+1))) (h d : Fin r → ZMod (prime^(w+1))) (j : Fin W)
        (k : Fin ((prime^(w+1))^((r+g)+(r+g))*W)), k.val = (RecursiveInterchangeScaling.index (ordinaryChildAddress hg tg h d j)).val →
        let t := childFields hg tg (h,fun i => d i.rev)
        word k = original (FlatCoordinateLayout.index (Fin.append t.1 t.2) j) := by
  constructor
  · rintro ⟨word,layout,reads⟩
    refine ⟨word,layout,?_⟩
    intro hg tg h d j k pos t
    have cell := ordinaryChildPackSchedule_index hg tg h d j
    exact (congrArg word (Fin.ext (pos.trans cell.symm))).trans (reads (Fin.append t.1 t.2) j)
  · rintro ⟨word,layout,reads⟩
    refine ⟨word,layout,?_⟩
    intro x j
    let a := fun i : Fin (r+g) => x (i.castAdd (r+g))
    let b := fun i : Fin (r+g) => x (i.natAdd (r+g))
    obtain ⟨hg,tg,s,split⟩ := childFields_surjective (r := r) (g := g) a b
    let d := fun i : Fin r => s.2 i.rev
    let t := childFields hg tg (s.1,fun i => d i.rev)
    have fields : Fin.append t.1 t.2 = x := by
      simp only [t,d,Fin.rev_rev,Prod.eta,split]
      funext i
      cases i using Fin.addCases <;> simp only [a,b,Fin.append_left,Fin.append_right]
    rw [← fields]
    exact reads hg tg s.1 d j _ (ordinaryChildPackSchedule_index hg tg s.1 d j)

theorem ordinaryRecursivePosition_cell {r g w W : ℕ} (hg tg : Fin g → ZMod (prime^(w+1)))
    (h d : Fin r → ZMod (prime^(w+1))) (j : Fin W) :
    let fields := childFields hg tg (h,fun k => d k.rev)
    ordinaryRecursivePosition r g w W (RecursiveInterchangeScaling.index (ordinaryChildAddress hg tg h d j)) =
      FlatCoordinateLayout.index (Fin.append fields.1 fields.2) j := by
  intro fields
  change ordinaryRecursivePosition r g w W (CopyChildLayout.flatAddress _ (ordinaryChildAddress hg tg h d j)) = _
  unfold ordinaryRecursivePosition
  rw [Equiv.symm_apply_apply]
  simp only [ordinaryChildAddress,Equiv.symm_apply_apply,Fin.append_left,Fin.append_right]
  change (let s := childFields hg tg (rankEquiv.symm (rankEquiv h),fun k => rankEquiv.symm (rankEquiv d) k.rev)
          FlatCoordinateLayout.index (Fin.append s.1 s.2) j) = _
  simp only [Equiv.symm_apply_apply,fields]

private theorem parentCell_fields {r g w W : ℕ} (k : Fin ((prime^(w+1))^((r+g)+(r+g))*W)) :
    ∃ hg tg h d j, ordinaryRecursivePosition r g w W
      (RecursiveInterchangeScaling.index (ordinaryChildAddress hg tg h d j)) = k := by
  obtain ⟨⟨digits,j⟩,rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨x,rfl⟩ := (rankEquiv : (Fin ((r+g)+(r+g)) → ZMod (prime^(w+1))) ≃ _).surjective digits
  let h := fun i : Fin (r+g) => x (i.castAdd (r+g))
  let d := fun i : Fin (r+g) => x (i.natAdd (r+g))
  obtain ⟨hg,tg,s,split⟩ := childFields_surjective (r := r) (g := g) h d
  refine ⟨hg,tg,s.1,(fun i => s.2 i.rev),j,?_⟩
  rw [ordinaryRecursivePosition_cell]
  simp only [Fin.rev_rev,Prod.eta,split]
  apply congrArg (fun y => FlatCoordinateLayout.index y j)
  funext i
  cases i using Fin.addCases <;> simp only [h,d,Fin.append_left,Fin.append_right]

/-- Every parent symbol has exactly one recursive address, including when
there are no active digits or no spectators. -/
noncomputable def ordinaryChildLayoutEquiv (r g w W : ℕ) :
    Fin (volume prime (ordinaryChildDescriptor r g w W)) ≃ Fin ((prime^(w+1))^((r+g)+(r+g))*W) :=
  Equiv.ofBijective (ordinaryRecursivePosition r g w W) ((Fintype.bijective_iff_surjective_and_card _).2
    ⟨fun k => by
      obtain ⟨hg,tg,h,d,j,cell⟩ := parentCell_fields k
      exact ⟨_,cell⟩,by
      simp only [Fintype.card_fin,volume,ordinaryChildDescriptor,one_mul,← ordinaryAtomWidth,pow_add]
      ring⟩)

theorem ordinaryChildVolume (r g w W : ℕ) :
    volume prime (ordinaryChildDescriptor r g w W) = (prime^(w+1))^((r+g)+(r+g))*W := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (ordinaryChildLayoutEquiv r g w W)

/-- Packing materializes the recursively ordered word on the record bank. -/
theorem ordinaryPackedWord_iff {r g w W H J T A : ℕ} {α : Type}
    (bank : Fin 35 ↪ Fin T) (record : List (Fin (A+4))) (sym : α → Fin 4)
    (src dst : ℤ → Fin 4) (p q : ℤ) (S : Host.Stacks T A)
    (original : Fin ((prime^(w+1))^((r+g)+(r+g))*W) → α) :
    ColumnRecordReady bank H J record sym src dst p q original
      (fun x => (ordinaryChildPackSchedule r g).foldl adjacentFields x) S ↔
    RecordReady (b := prime) (w := w) (W := W) (d := (r+g)+(r+g))
      bank H J record sym src dst p q
      (fun k => original (ordinaryRecursivePosition r g w W (k.cast (ordinaryChildVolume ..).symm))) S := by
  rw [ordinaryChildPackedRecord_iff]
  constructor
  · rintro ⟨word,layout,reads⟩
    convert layout using 1
    funext k
    let i := k.cast (ordinaryChildVolume r g w W).symm
    obtain ⟨hg,tg,h,d,j,cell⟩ := parentCell_fields (ordinaryRecursivePosition r g w W i)
    have same : RecursiveInterchangeScaling.index (ordinaryChildAddress hg tg h d j) = i :=
      (ordinaryChildLayoutEquiv r g w W).injective cell
    have read := reads hg tg h d j k (congrArg Fin.val same.symm)
    change original (ordinaryRecursivePosition _ _ _ _ i) = word k
    rw [← same,ordinaryRecursivePosition_cell]
    exact read.symm
  · intro layout
    refine ⟨_,layout,?_⟩
    intro hg tg h d j k pos t
    have eqn : k.cast (ordinaryChildVolume r g w W).symm =
        RecursiveInterchangeScaling.index (ordinaryChildAddress hg tg h d j) := Fin.ext pos
    rw [eqn,ordinaryRecursivePosition_cell]

theorem ordinaryRecursiveTranspose_read {r g w W : ℕ} {α : Type*} :
    let v := ordinaryChildDescriptor r g w W
    let pos := ordinaryRecursivePosition r g w W
    let M := prime^(w+1)
    ∀ (before after : Fin (M^((r+g)+(r+g))*W) → α),
      (∀ i, after (pos i) = Shared50RecursiveNodeRows.transpose (one_dvd v.rows) (before ∘ pos) i) →
      ∀ (hg tg : Fin g → ZMod M) (h d : Fin r → ZMod M) (j : Fin W),
        let addr := fun h d => let t := childFields hg tg (h,fun k => d k.rev)
                               FlatCoordinateLayout.index (Fin.append t.1 t.2) j
        after (addr d h) = before (addr h d) := by
  intro v pos M before after run hg tg h d j addr
  have cell (x y : Fin r → ZMod M) : pos (RecursiveInterchangeScaling.index (ordinaryChildAddress hg tg x y j)) = addr x y := ordinaryRecursivePosition_cell hg tg x y j
  change after (addr d h) = before (addr h d)
  rw [← cell d h,← cell h d,run]
  exact Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd v.rows)
    (before ∘ pos) (ordinaryChildAddress hg tg h d j)

/-- Express the recursive output on the parent tape, using the inverse of
the same layout that supplied the child input. -/
noncomputable def ordinaryChildOutput {r g w W : ℕ} {α : Type*}
    (before : Fin ((prime^(w+1))^((r+g)+(r+g))*W) → α) :=
  let e := ordinaryChildLayoutEquiv r g w W
  Shared50RecursiveNodeRows.transpose (one_dvd (ordinaryChildDescriptor r g w W).rows)
    (before ∘ e) ∘ e.symm

theorem ordinaryChildOutput_eq_iff {r g w W : ℕ} {α : Type*}
    (before after : Fin ((prime^(w+1))^((r+g)+(r+g))*W) → α) :
    after = ordinaryChildOutput (r := r) (g := g) (w := w) before ↔
      ∀ i, after (ordinaryRecursivePosition r g w W i) =
        Shared50RecursiveNodeRows.transpose (one_dvd (ordinaryChildDescriptor r g w W).rows)
          (before ∘ ordinaryRecursivePosition r g w W) i := by
  let e := ordinaryChildLayoutEquiv r g w W
  let output := Shared50RecursiveNodeRows.transpose (one_dvd (ordinaryChildDescriptor r g w W).rows) (before ∘ e)
  change after = output ∘ e.symm ↔ ∀ i, after (e i) = output i
  constructor
  · rintro rfl i
    simp
  · intro run
    funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    simpa using run i

open Stack Host
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states

/-- Place one whole packing pass on the shared column bank. The caller can
run its recursive program between two such passes with all other tapes live. -/
theorem placedPackSchedule_exec [M8.Machine.Net] {P U : Type} {T d w W : ℕ}
    (ports : Fin (N+35) ↪ Fin T) (is : List ℕ) (fits : ∀ i ∈ is, i+1 < d)
    (body : P → Pr P T columnCapacity prime U) (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ) (hW : 0 < W)
    (original : Fin ((prime^(w+1))^d*W) → ZMod 2)
    (addr : (Fin d → ZMod (prime^(w+1))) → Fin d → ZMod (prime^(w+1))) :
    let bank := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let M := prime^(w+1)
    let ready := ColumnRecordReady (bank.trans ports) M.size W.size record SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original
    let clean := fun D : Stacks T prime => ∀ k : Fin (N+35), 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []
    ready addr S → clean S → ∃ z F n, z.user = v.user ∧
      n ≤ 1+((is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1) ∧
      Exec body (statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule d is))
        (mk v S) n (mk z F) ∧ ready (fun x => is.foldl adjacentFields (addr x)) F ∧ clean F ∧
        ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro bank M ready clean start free
  obtain ⟨u,D,n,user,cost,run,done,clear⟩ := packSchedule_exec is fits M.size W.size
    (Nat.size_le.mp le_rfl) (Nat.size_le.mp le_rfl) hW (P := Empty) Empty.elim
    (stateLiftDown swapStates_pos (embDn ports v)) (embStk ports S) record dest q original addr
    ((columnRecordReady_project bank ..).2 ((columnRecordReady_project (bank.trans ports) ..).1 start)) free
  obtain ⟨z,_,same,placed⟩ := statePlaced_exec_normalized ports ports.injective swapStates_fit
    swapStates_pos Empty.elim (body' := body) (fun e => nomatch e) v S run
  let F := embOvr ports D.get S
  have eq : embStk ports F = D := embStk_ovr ports.injective _ _
  rw [← eq] at done clear
  exact ⟨z,F,_,same.trans user,Nat.add_le_add_left cost 1,placed,
    (columnRecordReady_project (bank.trans ports) ..).2 ((columnRecordReady_project bank ..).1 done),clear,
    fun _ off => embOvr_off D.get S off⟩

/-- Surround a transpose on the contiguous recursive word with the two tape
routes. The return read is in the original parent's weighted-child layout. -/
theorem ordinaryChildRoute_exec [M8.Machine.Net] {P U : Type} {T : ℕ}
    (ports : Fin (N+35) ↪ Fin T) (body : P → Pr P T columnCapacity prime U) (r g : ℕ) (positive : 0 < r+g) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let is := ordinaryChildPackSchedule r g
      let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
      let pass := fun js => statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule d js)
      let clean := fun (S : Stacks T prime) => ∀ k : Fin (N+35), 35 ≤ k.val → S.L (ports k) = [] ∧ S.R (ports k) = []
      ∀ (v : HS T columnCapacity prime U) (S : Stacks T prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (original : Fin (M^d*W) → ZMod 2)
        (input : (Fin d → ZMod M) → IntegerMultBounds.Swap.Shear.State (Fin (r+g)) (ZMod M))
        (child : Pr P T columnCapacity prime U) (budget : ℕ),
      let saved := fun D : Stacks T prime => ∀ j, (∀ i, ports i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j
      let desc := ordinaryChildDescriptor r g w W
      let pos := ordinaryRecursivePosition r g w W
      let offset := fun (k : Fin (M^d*W)) => k.cast (ordinaryChildVolume r g w W).symm
      let ready := RecordReady (b := prime) (w := w) (W := W) (d := d) bank M.size W.size
        record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      let columns := ColumnRecordReady bank M.size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      (∀ (before : Fin (M^d*W) → ZMod 2) u D, ready (before ∘ pos ∘ offset) D → clean D → saved D → ∃ y G t, y.user = u.user ∧ t ≤ budget ∧
        Exec body child (mk u D) t (mk y G) ∧
        ready (Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (before ∘ pos) ∘ offset) G ∧ clean G ∧ saved G) →
      columns original (fun x => Fin.append (input x).1 (input x).2) S → clean S → ∃ z F n, z.user = v.user ∧
        n ≤ budget + 2*(1+(setup+swaps*swapVolumeRate w)*(M^d*W)) ∧
        Exec body (.seq (pass is) (.seq child (pass is.reverse))) (mk v S) n (mk z F) ∧
        columns original (fun x => let t := Cover.Weighted.child r (fun _ => 1) (fun _ => 1) (input x)
                                   Fin.append t.1 t.2) F ∧ clean F ∧ saved F := by
  obtain ⟨setup,swaps,bound⟩ := packTime_le (P := Empty) (U := U) Empty.elim
    ((r+g)+(r+g)) (ordinaryChildPackSchedule r g) (by omega)
  refine ⟨setup,swaps,?_⟩
  intro w W hW d M is bank pass clean v S record dest q original input child budget saved desc pos offset ready columns call start free
  obtain ⟨before,layout,reads⟩ := start
  let after := ordinaryChildOutput (r := r) (g := g) (w := w) before
  have cells := (ordinaryChildOutput_eq_iff (r := r) (g := g) (w := w) before after).1 rfl
  have fits : ∀ i ∈ is, i+1 < d := fun _ => ordinaryChildPackSchedule_inside
  obtain ⟨u,D,n,hu,hn,pack,packed,clear,kept⟩ := placedPackSchedule_exec ports is fits body v S record dest q hW
    before id ⟨before,layout,fun _ _ => rfl⟩ free
  obtain ⟨y,G,k,hy,hk,run,returned,available,live⟩ := call before u D ((ordinaryPackedWord_iff ..).1 packed) clear kept
  have changed : columns after (fun x => is.foldl adjacentFields x) G := by
    apply (ordinaryPackedWord_iff ..).2
    simp only [cells]
    exact returned
  obtain ⟨z,F,m,hz,hm,unpack,⟨word,done,placed⟩,empty,frame⟩ := placedPackSchedule_exec ports is.reverse
    (fun i hi => fits i (List.mem_reverse.mp hi)) body y G record dest q hW after _ changed available
  simp only [reverse_adjacentFields] at placed
  simp only [List.map_reverse,List.sum_reverse] at hm
  have price := bound w W hW
  refine ⟨z,F,n+(k+m),hz.trans (hy.trans hu),?_,.seq pack (.seq run unpack),⟨word,done,?_⟩,empty,?_⟩
  · dsimp only [is,d,M] at *
    omega
  · intro x j
    apply (placed _ j).trans
    apply Eq.trans _ (reads x j)
    apply goodChild_effect (fun _ => 1) (fun _ => 1) before after
    intro hg tg s j
    have cell := ordinaryRecursiveTranspose_read before after cells hg tg s.1 (fun i => s.2 i.rev) j
    simpa only [Cover.Weighted.child,Fin.isLt,ite_true,one_mul,Fin.rev_rev] using cell
  · intro j off
    exact ⟨(frame j off).1.trans (live j off).1,(frame j off).2.trans (live j off).2⟩


end IntegerMultBounds.MathlibTM2.M6.BitNode
