module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryChildLayout

/-! Stable packing of the two active blocks of a remainder row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open Cover.Fallback

/-- Move D across the middle spectators, then move HD across the prefix. -/
def intervalPackSchedule (p r m : ℕ) : List ℕ :=
  (middleTailSchedule m r).map ((p+r)+·) ++ middleTailSchedule p (r+r)

theorem intervalPackSchedule_inside {p r m i : ℕ} (used : i ∈ intervalPackSchedule p r m) :
    i+1 < p+r+m+r := by
  rcases List.mem_append.mp used with h | h
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    have := middleTailSchedule_inside hj
    omega
  · have := middleTailSchedule_inside h
    omega

/-- On an interval of a 64-axis node, the number of adjacent exchanges is
bounded independently of the atom width and of the inherited row count. -/
theorem intervalPackSchedule_length {lo hi : ℕ} (ordered : lo ≤ hi) (fits : hi ≤ 64) :
    (intervalPackSchedule lo (hi-lo) (64-hi+lo)).length ≤ 3072 := by
  simp only [intervalPackSchedule,List.length_append,List.length_map,middleTailSchedule_length]
  have gap : lo ≤ 64-(hi-lo) := by omega
  have mid : 64-hi+lo = 64-(hi-lo) := by omega
  rw [mid]
  have h := Nat.mul_le_mul_left ((hi-lo)+(hi-lo)) gap
  have sum : 64-(hi-lo)+(hi-lo) = 64 := by omega
  generalize hi-lo = r at h sum ⊢
  generalize 64-r = g at h sum ⊢
  zify at h sum ⊢
  nlinarith [sq_nonneg ((r : ℤ)-32), congrArg (fun n : ℤ => n*r) sum]


theorem intervalPackSchedule_fields {α : Type*} {n : ℕ} (x : Fin n → α)
    (pre h mid d suffix : List α) (width : d.length = h.length)
    (layout : List.ofFn x = pre++h++mid++d++suffix) :
    List.ofFn ((intervalPackSchedule pre.length h.length mid.length).foldl adjacentFields x) =
      h++d++pre++mid++suffix := by
  have size := congrArg List.length layout
  simp only [List.length_ofFn,List.length_append,width] at size
  rw [fold_adjacentFields _ _ (fun i used => by have := intervalPackSchedule_inside used; omega),
    layout,intervalPackSchedule,List.foldl_append,List.foldl_map]
  have first := fold_swapAtomAt_prefix (pre++h) (middleTailSchedule mid.length d.length)
    (mid++d++suffix)
  rw [middleTailSchedule_packs] at first
  have last := middleTailSchedule_packs pre (h++d) (mid++suffix)
  simp only [List.length_append,width,List.append_assoc] at first last ⊢
  rw [first,last]

open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open FlatCoordinateLayout in
/-- The packed phase tape and the active-first recursive descriptor assign the
same physical offset to the two interval fields and their four spectators. -/
theorem intervalPacked_index (axes : ℕ) {w W lo hi : ℕ}
    (a b : Fin lo → ZMod (prime^(w+1))) (h d : Fin (hi-lo) → ZMod (prime^(w+1)))
    (u v : Fin (axes-hi) → ZMod (prime^(w+1))) (j : Fin W) :
    (CopyChildLayout.packActive (phaseIntervalChild lo hi (w+1) W axes)
      (RecursiveInterchangeScaling.index (intervalAddress axes a b h d u v j))).val =
      (index (Fin.addCases (Fin.addCases h d) (Fin.addCases a (Fin.addCases (Fin.addCases u b) v))) j).val := by
  rw [CopyChildLayout.packActive_index,FlatCoordinateLayout.index_val]
  let M := prime^(w+1)
  change ((j.val+W*(rank v).val)+(M^(axes-hi)*W)*((rank (Fin.addCases u b)).val+
    M^(axes-hi+lo)*((rank a).val+M^lo*(0+1*0))))+
    CopyChildLayout.spectators (phaseIntervalChild lo hi (w+1) W axes)*
      ((rank d).val+prime^((hi-lo)*(w+1))*(rank h).val) = _
  have width : prime^((hi-lo)*(w+1)) = M^(hi-lo) := by dsimp only [M]; rw [← pow_mul,Nat.mul_comm]
  rw [width]
  simp only [CopyChildLayout.spectators,phaseIntervalChild,one_mul,mul_zero,add_zero,
    ArbitraryWidthSliceTranspose.rank_append,pow_add]
  dsimp only [M]
  ring

open FlatCoordinateLayout in
/-- The coordinate order guaranteed by the packing program identifies the
actual tape index, even when the two digit counts are associated differently. -/
theorem intervalPacked_offset {w W lo hi axes n : ℕ}
    (a b : Fin lo → ZMod (prime^(w+1))) (h d : Fin (hi-lo) → ZMod (prime^(w+1)))
    (u v : Fin (axes-hi) → ZMod (prime^(w+1))) (j : Fin W)
    (y : Fin n → ZMod (prime^(w+1)))
    (packed : List.ofFn y = List.ofFn h ++ List.ofFn d ++ List.ofFn a ++ List.ofFn u ++
      List.ofFn b ++ List.ofFn v) :
    (index y j).val = (CopyChildLayout.packActive _
      (RecursiveInterchangeScaling.index (intervalAddress axes a b h d u v j))).val := by
  rw [intervalPacked_index]
  let digits := Fin.append (Fin.append h d) (Fin.append a (Fin.append (Fin.append u b) v))
  have same : List.ofFn y = List.ofFn digits := by
    simpa only [digits,List.ofFn_fin_append,List.append_assoc] using packed
  have size := congrArg List.length same
  simp only [List.length_ofFn] at size
  subst n
  exact congrArg (fun z => (index z j).val) (List.ofFn_injective same)

private theorem splitDigits {α : Type*} {n p q : ℕ} (size : p+q = n) (x : Fin n → α) :
    ∃ (a : Fin p → α) (b : Fin q → α), List.ofFn x = List.ofFn a ++ List.ofFn b := by
  subst n
  refine ⟨fun i => x (i.castAdd q),fun i => x (i.natAdd p),?_⟩
  rw [← List.ofFn_fin_append,Fin.append_castAdd_natAdd]

private theorem intervalDigits {α : Type*} {lo hi : ℕ} (ordered : lo ≤ hi) (fits : hi ≤ 64)
    (x : Fin 128 → α) :
    ∃ (a b : Fin lo → α) (h d : Fin (hi-lo) → α) (u v : Fin (64-hi) → α),
      List.ofFn x = List.ofFn a ++ List.ofFn h ++ List.ofFn u ++ List.ofFn b ++ List.ofFn d ++ List.ofFn v := by
  obtain ⟨left,right,halves⟩ := splitDigits (by decide : 64+64 = 128) x
  have half (y : Fin 64 → α) := splitDigits (by omega : (lo+(hi-lo))+(64-hi) = 64) y
  obtain ⟨ah,u,l⟩ := half left
  obtain ⟨bd,v,r⟩ := half right
  obtain ⟨a,h,l'⟩ := splitDigits rfl ah
  obtain ⟨b,d,r'⟩ := splitDigits rfl bd
  exact ⟨a,b,h,d,u,v,by simp only [halves,l,r,l',r',List.append_assoc]⟩

open FlatCoordinateLayout in
private theorem index_ofFn {M W m n : ℕ} [NeZero M] (x : Fin m → ZMod M) (y : Fin n → ZMod M)
    (eqn : List.ofFn x = List.ofFn y) (j : Fin W) : (index x j).val = (index y j).val := by
  have size := congrArg List.length eqn
  simp only [List.length_ofFn] at size
  subst n
  rw [List.ofFn_injective eqn]

open RecursiveInterchangeLayout (Descriptor volume)

/-- Address a packed child by its physical tape volume. -/
noncomputable def packedChildPosition {V : ℕ} (child : Descriptor) (size : volume prime child = V) :
    Fin (volume prime child) ≃ Fin V :=
  (CopyChildLayout.packActive child).trans (finCongr (by
    have card := Fintype.card_congr (CopyChildLayout.packActive child)
    simp only [Fintype.card_fin] at card
    exact card.symm.trans size))

variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states

/-- Unpack one returned row on a placed record bank.  The returned word is
read at the forward packing offset; every tape outside the bank is preserved. -/
theorem intervalReturn_exec {T capacity : ℕ} (fitsStates : Q ≤ capacity)
    (ports : Fin (N+35) ↪ Fin T) (body : P → Pr P T capacity prime U)
    (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
      let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
      let clean := fun D : Stacks T prime => ∀ k : Fin (N+35), 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []
      ∀ (u : HS T capacity prime U) (S : Stacks T prime) record dest q
        (output : Fin (volume prime (phaseIntervalChild lo hi (w+1) W 64)) → ZMod 2),
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      let ready := RecordReady (b := prime) (w := w) (W := W) (d := 128) bank M.size W.size
        record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      ready (output ∘ position.symm) S → clean S → ∃ z F n, z.user = u.user ∧
        n ≤ 1+(setup+swaps*swapVolumeRate w)*(M^128*W) ∧
        Exec body (statePlacedNormalized ports fitsStates swapStates_pos Empty.elim (packSchedule 128 is.reverse))
          (mk u S) n (mk z F) ∧ ready (fun i => output (i.cast size.symm)) F ∧ clean F ∧
        ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
  have inside (i) (used : i ∈ is.reverse) : i+1 < 128 := by
    have := intervalPackSchedule_inside (List.mem_reverse.mp used)
    omega
  obtain ⟨setup,swaps,price⟩ := packTime_le (P := Empty) (U := U) Empty.elim 128 is (by decide)
  refine ⟨setup,swaps,?_⟩
  intro w W hW M schedule bank clean u S record dest q output size position ready stored free
  obtain ⟨z,F,n,user,cost,exec,⟨word,out,read⟩,clear,frame⟩ := placedPackSchedule_exec fitsStates ports
    is.reverse inside body u S record dest q hW (output ∘ position.symm) id ⟨_,stored,fun _ _ => rfl⟩ free
  refine ⟨z,F,n,user,?_,exec,?_,clear,frame⟩
  · exact cost.trans (Nat.add_le_add_left (by simpa only [List.map_reverse,List.sum_reverse] using price w W hW) 1)
  · suffices eq : word = fun i => output (i.cast size.symm) from eq ▸ out
    funext i
    obtain ⟨⟨digits,j⟩,rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨x,rfl⟩ := (FlatCoordinateLayout.rankEquiv : (Fin 128 → ZMod M) ≃ _).surjective digits
    obtain ⟨a,b,h,d,u,v,layout⟩ := intervalDigits ordered fits x
    have entry : (FlatCoordinateLayout.index x j).cast (intervalChild_volume ordered fits (w+1) W).symm =
        RecursiveInterchangeScaling.index (intervalAddress 64 a b h d u v j) := by
      apply Fin.ext
      rw [Fin.val_cast,intervalAddress_index]
      apply index_ofFn
      change List.ofFn x = List.ofFn (Fin.append (Fin.append (Fin.append a h) u) (Fin.append (Fin.append b d) v))
      simpa only [List.ofFn_fin_append,List.append_assoc] using layout
    let mid := List.ofFn u ++ List.ofFn b
    have order := intervalPackSchedule_fields x (List.ofFn a) (List.ofFn h) mid (List.ofFn d)
      (List.ofFn v) (by simp) (by simpa only [mid,List.append_assoc] using layout)
    have moved : FlatCoordinateLayout.index (is.foldl adjacentFields x) j =
        position ((FlatCoordinateLayout.index x j).cast size.symm) := by
      apply Fin.ext
      change _ = (CopyChildLayout.packActive _ ((FlatCoordinateLayout.index x j).cast _)).val
      rw [entry]
      apply intervalPacked_offset a b h d u v j
      simpa only [mid,List.length_append,List.length_ofFn,is,List.append_assoc] using order
    change word (FlatCoordinateLayout.index x j) = output ((FlatCoordinateLayout.index x j).cast size.symm)
    simpa only [id_eq,reverse_adjacentFields,Function.comp_apply,moved,Equiv.symm_apply_apply]
      using read (is.foldl adjacentFields x) j

/-- Run a child on the stable active-first row, charging the incoming and
outgoing exchanges and restoring the original record layout. -/
theorem withIntervalPacking_exec [Fintype P] (body : P → Pr P (N+35) Q prime U)
    (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let d := 128
      let M := prime^(w+1)
      let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
      let bank := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let clean := fun (S : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → S.L k = [] ∧ S.R k = []
      ∀ (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (input output : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M)
        (child : Pr P (N+35) Q prime U) (budget : ℕ),
      let ready := ColumnRecordReady bank (Nat.size M) (Nat.size W) record SparseRoleCircuit.encode
        (fun _ => blank) dest 0 q
      (∀ (packed : (Fin d → ZMod M) → Fin d → ZMod M),
        (∀ x (pre h mid tail suffix : List (ZMod M)), pre.length = lo → h.length = hi-lo →
          mid.length = 64-hi+lo → tail.length = hi-lo →
          List.ofFn (addr x) = pre++h++mid++tail++suffix →
          List.ofFn (packed x) = h++tail++pre++mid++suffix) →
        ∀ u D, ready input packed D → clean D → ∃ y G t, y.user = u.user ∧ t ≤ budget ∧
        Exec body child (mk u D) t (mk y G) ∧ ready output packed G ∧ clean G) →
      ready input addr S → clean S → ∃ z F n, z.user = v.user ∧
        n ≤ budget + 2*((setup+swaps*swapVolumeRate w)*(M^d*W)) ∧
        Exec body (.seq (packSchedule d is) (.seq child (packSchedule d is.reverse)))
          (mk v S) n (mk z F) ∧ ready output addr F ∧ clean F := by
  let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
  have inside (i) (used : i ∈ is) : i+1 < 128 := by
    have := intervalPackSchedule_inside used
    omega
  obtain ⟨setup,swaps,run⟩ := withPacking_exec body 128 is (by decide) inside
  refine ⟨setup,swaps,?_⟩
  intro w W hW d M schedule bank clean v S record dest q input output addr child budget ready call
  apply run w W hW v S record dest q input output addr child budget
  apply call
  intro x pre h mid tail suffix hp hh hm ht layout
  simpa only [is,hp,hh,hm] using
    intervalPackSchedule_fields (addr x) pre h mid tail suffix (ht.trans hh.symm) layout

end IntegerMultBounds.MathlibTM2.M6.BitNode
