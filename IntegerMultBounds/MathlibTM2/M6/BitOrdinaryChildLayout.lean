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

/-- Surround a transpose on the contiguous recursive word with the two tape
routes. The return read is in the original parent's weighted-child layout. -/
theorem ordinaryChildRoute_exec [M8.Machine.Net] {P U : Type} [Fintype P]
    (body : P → Pr P (N+35) Q prime U) (r g : ℕ) (positive : 0 < r+g) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let is := ordinaryChildPackSchedule r g
      let bank := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let clean := fun (S : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → S.L k = [] ∧ S.R k = []
      ∀ (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (input : Fin (M^d*W) → ZMod 2) (child : Pr P (N+35) Q prime U) (budget : ℕ),
      let desc := ordinaryChildDescriptor r g w W
      let pos := ordinaryRecursivePosition r g w W
      let offset := fun (k : Fin (M^d*W)) => k.cast (ordinaryChildVolume r g w W).symm
      let ready := RecordReady (b := prime) (w := w) (W := W) (d := d) bank M.size W.size
        record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      let columns := ColumnRecordReady bank M.size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      (∀ u D, ready (input ∘ pos ∘ offset) D → clean D → ∃ y G t, y.user = u.user ∧ t ≤ budget ∧
        Exec body child (mk u D) t (mk y G) ∧
        ready (Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (input ∘ pos) ∘ offset) G ∧ clean G) →
      ready input S → clean S → ∃ z F n, z.user = v.user ∧
        n ≤ budget + 2*((setup+swaps*swapVolumeRate w)*(M^d*W)) ∧
        Exec body (.seq (packSchedule d is) (.seq child (packSchedule d is.reverse))) (mk v S) n (mk z F) ∧
        columns (ordinaryChildOutput (r := r) (g := g) (w := w) input) id F ∧ clean F := by
  obtain ⟨setup,swaps,route⟩ := withPacking_exec body ((r+g)+(r+g)) (ordinaryChildPackSchedule r g)
    (by omega) (fun _ => ordinaryChildPackSchedule_inside)
  refine ⟨setup,swaps,?_⟩
  intro w W hW d M is bank clean v S record dest q input child budget desc pos offset ready columns call start free
  apply route w W hW v S record dest q input _ id child budget _ ⟨input,start,fun _ _ => rfl⟩ free
  intro u D packed clear
  obtain ⟨y,G,t,user,cost,run,returned,empty⟩ := call u D ((ordinaryPackedWord_iff ..).1 packed) clear
  refine ⟨y,G,t,user,cost,run,(ordinaryPackedWord_iff ..).2 ?_,empty⟩
  have cells := (ordinaryChildOutput_eq_iff (r := r) (g := g) (w := w) input _).1 rfl
  simp only [cells]
  exact returned

end IntegerMultBounds.MathlibTM2.M6.BitNode
