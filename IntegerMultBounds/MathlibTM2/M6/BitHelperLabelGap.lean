module

public import IntegerMultBounds.MathlibTM2.Cover.LabelExchange
public import IntegerMultBounds.MathlibTM2.M6.BitPhaseRun
public import IntegerMultBounds.MathlibTM2.M6.BitHelperPacking

/-! Adjacent field exchanges on the PR589 helper tape preserve its interposed label block. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.RevMachine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Descriptor for adjacent field digits. The label precedes the pair,
lies between its digits, or follows it, according to the swap position. -/
noncomputable def helperAdjacentView (w L W : ℕ) (i : Fin 127) : Descriptor :=
  let M := prime^w
  ⟨1,1,M^i.val * (if 16 ≤ i.val then L else 1),w,
    if i.val = 15 then L else 1,
    M^(126-i.val)*(if i.val < 15 then L else 1)*W⟩

theorem helperAdjacent_volume (w L W : ℕ) (i : Fin 127) :
    volume prime (helperAdjacentView w L W i) = (prime^w)^16*(L*((prime^w)^112*W)) := by
  let M := prime^w
  have fields : M^i.val*M*M*M^(126-i.val) = M^16*M^112 := by
    rw [← pow_succ,← pow_succ,← pow_add,← pow_add]
    congr 1
    omega
  change 1*1*(M^i.val*(if 16 ≤ i.val then L else 1))*M*(if i.val = 15 then L else 1)*M*(M^(126-i.val)*(if i.val < 15 then L else 1)*W) = _
  change _ = M^16*(L*(M^112*W))
  calc
    _ = (M^i.val*M*M*M^(126-i.val))*L*W := by
      by_cases left : i.val < 15
      · simp [left,show ¬16 ≤ i.val by omega,show i.val ≠ 15 by omega]; ring
      · by_cases edge : i.val = 15
        · simp [edge]; ring
        · simp [left,edge,show 16 ≤ i.val by omega]; ring
    _ = _ := by rw [fields]; ring

/-- Result word of a scheduled leaf on the caller's volume. -/
noncomputable def helperPackingStep {w L W : ℕ} {v : Descriptor}
    (size : volume prime v = (prime^w)^16*(L*((prime^w)^112*W)))
    (word : Fin (volume prime v) → ZMod 2) (n : ℕ) :=
  if h : n < 127 then RevSemantics.leafOut (helperAdjacentView w L W ⟨n,h⟩)
    ((helperAdjacent_volume ..).trans size.symm) word else word

/-- Each scheduled result is the endpoint of the leaf machine on prepared headers. -/
theorem helperPackingStep_runs [M8.Machine.Net] {T w L W : ℕ} {v : Descriptor}
    (size : volume prime v = (prime^w)^16*(L*((prime^w)^112*W))) (pos : v.Positive)
    (i : Fin 127) (io : Fin T) (roles : Tapes T prime) (word : Fin (volume prime v) → ZMod 2)
    (head : roles.head io = 0) (stored : roles.tape io = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord word)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let hdr := Routines.hdr (helperAdjacentView w L W i)
    GraphContract.Runs (LeafCore.core io) (CommonBank.bank roles hdr f p node scalar ctr st)
      (CommonBank.bank (SharedPlacementAlphabet.setTape roles io
        (M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (helperPackingStep size word i.val)) 0)
        hdr f p node scalar ctr st)
      (LeafCore.coreCost (volume prime v) w) := by
  simp only [helperPackingStep,dite_eq_left i.isLt]
  exact LabelExchange.leafOut_runs ((helperAdjacent_volume w L W i).trans size.symm)
    pos io roles word head stored f p node scalar ctr st

/-- A swap inside the live block preserves the entire label and exterior address. -/
theorem helperLive_swap {α : Type*} {w L W : ℕ} {i : Fin 127} (inside : i.val < 15)
    {x y : ℕ → α} (swap : LabelView.Swapped prime (helperAdjacentView w L W i) x y)
    (pre : Fin ((prime^w)^i.val)) (h d : Fin (prime^w))
    (tail : Fin ((prime^w)^(14-i.val))) (label : Fin L)
    (exterior : Fin ((prime^w)^112)) (j : Fin W) :
    let M := prime^w
    let cell := fun a b : Fin M =>
      (((((pre.val*M+a.val)*M+b.val)*M^(14-i.val)+tail.val)*L+label.val)*M^112+exterior.val)*W+j.val
    y (cell h d) = x (cell d h) := by
  intro M cell
  let v := helperAdjacentView w L W i
  let after := ((tail.val*L+label.val)*M^112+exterior.val)*W+j.val
  have powers : M^(126-i.val) = M^(14-i.val)*M^112 := by
    rw [← pow_add]; congr 1; omega
  have shape : v.afterD = M^(14-i.val)*L*M^112*W := by
    simp only [v,helperAdjacentView,ite_eq_left inside]
    change M^(126-i.val)*L*W = _
    rw [powers]; ring
  have bound : after < v.afterD := by
    rw [shape]
    exact LabelShift.pack_lt (LabelShift.pack_lt (LabelShift.pack_lt tail.isLt label.isLt) exterior.isLt) j.isLt
  have middle : v.between = 1 := ite_eq_right (by omega)
  have before : pre.val < v.beforeH := by
    simp [v,helperAdjacentView,show ¬ 16 ≤ i.val by omega]
  have addr (a b : Fin M) :
      RecursiveInterchangeLayout.index prime v 0 0 pre.val a.val 0 b.val after = cell a b := by
    simp only [RecursiveInterchangeLayout.index,shape,middle,Nat.zero_mul,Nat.zero_add,Nat.mul_one,Nat.add_zero]
    change ((pre.val*M+a.val)*M+b.val)*(M^(14-i.val)*L*M^112*W)+after = _
    dsimp only [cell,after]
    ring
  rw [← addr,← addr]
  exact swap 0 Nat.zero_lt_one 0 Nat.zero_lt_one _ before _ h.isLt 0 (by change 0 < v.between; rw [middle]; decide) _ d.isLt _ bound

/-- A swap inside the exterior block preserves the live digits and cover label. -/
theorem helperExterior_swap {α : Type*} {w L W : ℕ} {i : Fin 127} (inside : 16 ≤ i.val)
    {x y : ℕ → α} (swap : LabelView.Swapped prime (helperAdjacentView w L W i) x y)
    (live : Fin ((prime^w)^16)) (label : Fin L) (pre : Fin ((prime^w)^(i.val-16)))
    (h d : Fin (prime^w)) (tail : Fin ((prime^w)^(126-i.val))) (j : Fin W) :
    let M := prime^w
    let cell := fun a b : Fin M =>
      (((((live.val*L+label.val)*M^(i.val-16)+pre.val)*M+a.val)*M+b.val)*M^(126-i.val)+tail.val)*W+j.val
    y (cell h d) = x (cell d h) := by
  intro M cell
  let v := helperAdjacentView w L W i
  let before := (live.val*L+label.val)*M^(i.val-16)+pre.val
  let after := tail.val*W+j.val
  have shape : v.beforeH = M^16*L*M^(i.val-16) := by
    change M^i.val*(if 16 ≤ i.val then L else 1) = _
    rw [ite_eq_left inside,show M^i.val = M^16*M^(i.val-16) by rw [← pow_add]; congr 1; omega]
    ring
  have lead : before < v.beforeH := by
    rw [shape]
    exact LabelShift.pack_lt (LabelShift.pack_lt live.isLt label.isLt) pre.isLt
  have trailing : v.afterD = M^(126-i.val)*W := by
    simp [v,helperAdjacentView,show ¬ i.val < 15 by omega,M]
  have bound : after < v.afterD := by
    rw [trailing]; exact LabelShift.pack_lt tail.isLt j.isLt
  have middle : v.between = 1 := ite_eq_right (by omega)
  have addr (a b : Fin M) :
      RecursiveInterchangeLayout.index prime v 0 0 before a.val 0 b.val after = cell a b := by
    simp only [RecursiveInterchangeLayout.index,trailing,middle,Nat.zero_mul,Nat.zero_add,Nat.mul_one,Nat.add_zero]
    change ((before*M+a.val)*M+b.val)*(M^(126-i.val)*W)+after = _
    dsimp only [cell,before,after]
    ring
  rw [← addr,← addr]
  exact swap 0 Nat.zero_lt_one 0 Nat.zero_lt_one _ lead _ h.isLt 0
    (by change 0 < v.between; rw [middle]; decide) _ d.isLt _ bound

/-- Decompose both ranks of an adjacent interchange with the same prefix and suffix. -/
private theorem adjacentRanks {M n : ℕ} [NeZero M] (digits : Fin n → ZMod M)
    (i : ℕ) (fits : i+1 < n) :
    let a : Fin n := ⟨i,by omega⟩
    let b : Fin n := ⟨i+1,fits⟩
    ∃ (pre : Fin (M^i)) (tail : Fin (M^(n-2-i))),
      let cell := fun h d : ZMod M => ((pre.val*M+h.val)*M+d.val)*M^(n-2-i)+tail.val
      (FlatCoordinateLayout.rank digits).val = cell (digits a) (digits b) ∧
      (FlatCoordinateLayout.rank (digits ∘ Equiv.swap a b)).val = cell (digits b) (digits a) := by
  intro a b
  have lt : a < b := by change i < i+1; omega
  obtain ⟨p,hp,m,hm,s,hs,packed⟩ := FlatCoordinateLayout.rank_split_pair digits a b lt
  have gap : b.val-a.val-1 = 0 := by change i+1-i-1 = 0; omega
  have suffix : FlatCoordinateLayout.suffixFields b = n-2-i := by
    change n-1-(i+1) = n-2-i; omega
  have swapped := FlatCoordinateLayout.index_swap digits a b lt (0 : Fin 1) p m s packed
  rw [gap,pow_zero] at hm
  have zero : m = 0 := by omega
  refine ⟨⟨p,hp⟩,⟨s,suffix ▸ hs⟩,?_,?_⟩
  · simpa only [gap,pow_zero,suffix,zero,Nat.mul_one,Nat.add_zero] using packed
  · simpa only [FlatCoordinateLayout.index_val,gap,pow_zero,suffix,zero,Nat.mul_one,
      Fin.val_zero,Nat.add_zero] using swapped

/-- Physical offset of a helper point, including the label at the live/exterior cut. -/
noncomputable def helperLabelCell {M L W : ℕ} [NeZero M] (live : Fin 16 → ZMod M)
    (label : Fin L) (exterior : Fin 112 → ZMod M) (j : Fin W) : ℕ :=
  (((FlatCoordinateLayout.rank live).val*L+label.val)*M^112+
    (FlatCoordinateLayout.rank exterior).val)*W+j.val

/-- The slot-packing address is the address read by the invocation for this label. -/
theorem helperLabelCell_invocation {w B W : ℕ} (g : LabelPadding.Label 64 w)
    (z : LabelEntry.Cell (copyLabelLayout w B ((prime^w)^112*W)) B)
    (live : Fin 16 → ZMod (prime^w)) (exterior : Fin 112 → ZMod (prime^w)) (j : Fin W)
    (after : z.after.val = (FlatCoordinateLayout.index exterior j).val) :
    let label : Fin (B*prime^(64*(w*64))) :=
      ⟨z.b.val*prime^(64*(w*64))+(LabelAddress.address g).val,
        LabelShift.pack_lt z.b.isLt (by simpa only [← pow_mul,show w*(64*64) = 64*(w*64) by omega]
          using (LabelAddress.address g).isLt)⟩
    (FlatCoordinateLayout.index live (labelSpectator g z)).val = helperLabelCell live label exterior j := by
  intro label
  simp only [FlatCoordinateLayout.index_val,labelSpectator,helperLabelCell,label,after]
  ring

theorem helperLabelCell_live {α : Type*} {w L W : ℕ} {i : Fin 127} (inside : i.val < 15)
    {x y : ℕ → α} (swap : LabelView.Swapped prime (helperAdjacentView w L W i) x y)
    (live : Fin 16 → ZMod (prime^w)) (label : Fin L)
    (exterior : Fin 112 → ZMod (prime^w)) (j : Fin W) :
    let a : Fin 16 := ⟨i.val,by omega⟩
    let b : Fin 16 := ⟨i.val+1,by omega⟩
    y (helperLabelCell (live ∘ Equiv.swap a b) label exterior j) =
      x (helperLabelCell live label exterior j) := by
  intro a b
  obtain ⟨pre,tail,initial,final⟩ := adjacentRanks live i.val (by omega)
  unfold helperLabelCell
  rw [initial,final]
  exact helperLive_swap inside swap pre ((ZMod.finEquiv _).symm (live b))
    ((ZMod.finEquiv _).symm (live a)) tail label (FlatCoordinateLayout.rank exterior) j
    |> fun h => by simpa only [FlatCoordinateLayout.finEquiv_symm_val] using h

theorem helperLabelCell_exterior {α : Type*} {w L W : ℕ} {i : Fin 127} (inside : 16 ≤ i.val)
    {x y : ℕ → α} (swap : LabelView.Swapped prime (helperAdjacentView w L W i) x y)
    (live : Fin 16 → ZMod (prime^w)) (label : Fin L)
    (exterior : Fin 112 → ZMod (prime^w)) (j : Fin W) :
    let a : Fin 112 := ⟨i.val-16,by omega⟩
    let b : Fin 112 := ⟨i.val-16+1,by omega⟩
    y (helperLabelCell live label (exterior ∘ Equiv.swap a b) j) =
      x (helperLabelCell live label exterior j) := by
  intro a b
  let M := prime^w
  obtain ⟨pre,tail,initial,final⟩ := adjacentRanks exterior (i.val-16) (by omega)
  have sub : 112-2-(i.val-16) = 126-i.val := by omega
  let tail' : Fin (M^(126-i.val)) := ⟨tail.val,by rw [← sub]; exact tail.isLt⟩
  have run := helperExterior_swap inside swap (FlatCoordinateLayout.rank live) label pre
    ((ZMod.finEquiv _).symm (exterior b)) ((ZMod.finEquiv _).symm (exterior a)) tail' j
  simp only [FlatCoordinateLayout.finEquiv_symm_val] at run
  have size : M^(i.val-16)*M*M*M^(126-i.val) = M^112 := by
    rw [← pow_succ,← pow_succ,← pow_add]
    exact congrArg (M^·) (by omega)
  unfold helperLabelCell
  rw [initial,final]
  convert run using 2 <;> dsimp only [tail'] <;>
    simp only [sub] <;>
    dsimp only [M] at size <;> rw [← size] <;> ring

/-- The boundary exchange updates the last live coordinate and the first exterior
coordinate simultaneously, leaving the interposed label at its original address. -/
theorem helperLabelCell_boundary {α : Type*} {w L W : ℕ} {x y : ℕ → α}
    (swap : LabelView.Swapped prime (helperAdjacentView w L W 15) x y)
    (live : Fin 16 → ZMod (prime^w)) (label : Fin L)
    (exterior : Fin 112 → ZMod (prime^w)) (j : Fin W) :
    y (helperLabelCell (Function.update live 15 (exterior 0)) label
      (Function.update exterior 0 (live 15)) j) = x (helperLabelCell live label exterior j) := by
  let M := prime^w
  let pre := FlatCoordinateLayout.prefixIndex live 15
  let tail := (FlatCoordinateLayout.rank exterior).val % M^111
  have lead : pre < M^15 := FlatCoordinateLayout.prefix_lt live 15
  have bound : tail < M^111 := Nat.mod_lt _ (pow_pos (NeZero.pos M) _)
  have first : FlatCoordinateLayout.prefixIndex exterior 0 = 0 := by
    have h := FlatCoordinateLayout.prefix_lt exterior 0
    change _ < M^0 at h
    simpa using h
  have lastRank (z : ZMod M) : (FlatCoordinateLayout.rank (Function.update live 15 z)).val =
      pre*M+z.val := by
    have h := FlatCoordinateLayout.index_update live 15 z (0 : Fin 1)
    simpa only [pow_zero,Nat.mod_one,Nat.add_zero,Nat.one_mul,Nat.mul_one,Fin.val_zero,FlatCoordinateLayout.index_val,FlatCoordinateLayout.suffixSize,
      FlatCoordinateLayout.suffix,show FlatCoordinateLayout.suffixFields (15 : Fin 16) = 0 by rfl,pre] using h
  have firstRank (z : ZMod M) : (FlatCoordinateLayout.rank (Function.update exterior 0 z)).val =
      z.val*M^111+tail := by
    have h := FlatCoordinateLayout.index_update exterior 0 z (0 : Fin 1)
    simpa only [Nat.zero_mul,Nat.zero_add,Nat.add_zero,Nat.mul_one,Fin.val_zero,FlatCoordinateLayout.index_val,FlatCoordinateLayout.suffixSize,
      FlatCoordinateLayout.suffix,show FlatCoordinateLayout.suffixFields (0 : Fin 112) = 111 by rfl,
      first,tail,M] using h
  have liveRank := lastRank (live 15)
  have extRank := firstRank (exterior 0)
  rw [Function.update_eq_self] at liveRank extRank
  let v := helperAdjacentView w L W 15
  have shape : v = ⟨1,1,M^15,w,L,M^111*W⟩ := by simp [v,helperAdjacentView,M]
  rw [show helperAdjacentView w L W 15 = _ from shape] at swap
  have h := swap 0 Nat.zero_lt_one 0 Nat.zero_lt_one pre lead _ (ZMod.val_lt (exterior 0))
    _ label.isLt _ (ZMod.val_lt (live 15)) (tail*W+j.val) (LabelShift.pack_lt bound j.isLt)
  unfold helperLabelCell
  rw [lastRank,firstRank,liveRank,extRank]
  simp only [RecursiveInterchangeLayout.index,Nat.zero_mul,Nat.add_zero,Nat.zero_add] at h
  change y _ = x _ at h
  convert h using 2 <;> dsimp only [M] <;> rw [pow_succ (prime^w) 111] <;> ring

/-- All 127 leaf views implement the same adjacent-coordinate action on a
128-digit helper address, with the label fixed at the cut. -/
noncomputable def helperFieldCell {M L W : ℕ} [NeZero M] (digits : Fin 128 → ZMod M)
    (label : Fin L) (j : Fin W) : ℕ :=
  helperLabelCell (digits ∘ Fin.castAdd 112) label (digits ∘ Fin.natAdd 16) j

theorem helperFieldCell_swap {α : Type*} {w L W : ℕ} (i : Fin 127) {x y : ℕ → α}
    (swap : LabelView.Swapped prime (helperAdjacentView w L W i) x y)
    (digits : Fin 128 → ZMod (prime^w)) (label : Fin L) (j : Fin W) :
    let a : Fin 128 := ⟨i.val,by omega⟩
    let b : Fin 128 := ⟨i.val+1,by omega⟩
    y (helperFieldCell (digits ∘ Equiv.swap a b) label j) = x (helperFieldCell digits label j) := by
  intro a b
  let live : Fin 16 → ZMod (prime^w) := digits ∘ Fin.castAdd 112
  let exterior : Fin 112 → ZMod (prime^w) := digits ∘ Fin.natAdd 16
  unfold helperFieldCell
  rcases lt_trichotomy i.val 15 with left | edge | right <;> first
    | convert helperLabelCell_live left swap live label exterior j using 3
    | have e : i = 15 := Fin.ext edge
      subst i
      convert helperLabelCell_boundary swap live label exterior j using 3
    | convert helperLabelCell_exterior right swap live label exterior j using 3
  all_goals
    clear swap
    funext t
    simp only [live,exterior,Function.comp_apply,Equiv.swap_apply_def,Function.update_apply]
    split_ifs <;> first
      | rfl
      | apply congrArg digits
        apply Fin.ext
        simp only [Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero,a,b] at *
        omega

/-- On a common caller volume, each scheduled leaf returns the word consumed by
the next leaf. The address invariant holds for the complete slot permutation. -/
theorem helperLabelPacking (src dst : Option (Fin 56)) :
    ∃ is : List ℕ, (∀ i ∈ is, i+1 < 128) ∧
      ∀ {w L W : ℕ} {v : Descriptor}
        (size : volume prime v = (prime^w)^16*(L*((prime^w)^112*W))),
      ∀ word c s (label : Fin L) (j : Fin W),
        ext (is.foldl (helperPackingStep size) word) (helperFieldCell (helperSlotField c dst w s) label j) =
          ext word (helperFieldCell (helperSlotField c src w s) label j) := by
  let perm := (helperFieldOrder dst).trans (helperFieldOrder src).symm
  obtain ⟨is,fits,acts⟩ := fieldSchedule perm
  refine ⟨is,fits,?_⟩
  intro w L W v size
  have fold (js : List ℕ) (valid : ∀ i ∈ js, i+1 < 128)
      (word : Fin (volume prime v) → ZMod 2) (digits : Fin 128 → ZMod (prime^w))
      (label : Fin L) (j : Fin W) :
      ext (js.foldl (helperPackingStep size) word) (helperFieldCell (js.foldl Fallback.adjacentFields digits) label j) =
        ext word (helperFieldCell digits label j) := by
    induction js generalizing word digits with
    | nil => rfl
    | cons n js ih =>
      have fits := valid n (by simp)
      have inside : n < 127 := by omega
      rw [List.foldl_cons,List.foldl_cons,ih (fun k hk => valid k (by simp [hk]))]
      have swapped := LabelExchange.leafOut_swapped
        ((helperAdjacent_volume w L W ⟨n,inside⟩).trans size.symm) word
      simpa only [helperPackingStep,dite_eq_left inside,Fallback.adjacentFields,dite_eq_left fits] using
        helperFieldCell_swap ⟨n,inside⟩ swapped digits label j
  intro word c s label j
  have read := fold is fits word (helperSlotField c src w s) label j
  rw [acts,helperDigits_reindex] at read
  exact read

end IntegerMultBounds.MathlibTM2.M6.BitNode
