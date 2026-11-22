module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryChildCost
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledChildQueue
public import IntegerMultBounds.MathlibTM2.Cover.LabelCallerHeaders
public import IntegerMultBounds.MathlibTM2.Host.UnaryBinaryHalving
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece

/-! Interpret the ordinary PR589 owner tapes at a common live label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Matrix
open Shared50ModularControl (prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open Cover LabelTraversal FlatCoordinateLayout

open Stack Host

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open Cover.Fallback in
def phasePackSchedule (lo hi : ℕ) : List ℕ :=
  let r := hi-lo
  middleTailSchedule lo r ++ (middleTailSchedule (lo+(8-hi+lo)) r).map (r+·)

open Cover.Fallback in
theorem phasePackSchedule_inside {lo hi i : ℕ} (ordered : lo ≤ hi) (bounded : hi ≤ 8)
    (used : i ∈ phasePackSchedule lo hi) : i+1 < 16 := by
  rcases List.mem_append.mp used with head | tail
  · have := middleTailSchedule_inside head
    omega
  · obtain ⟨j,mem,rfl⟩ := List.mem_map.mp tail
    have := middleTailSchedule_inside mem
    omega

open Cover.Fallback in
/-- Pack both active fields ahead of the spectators by adjacent exchanges,
preserving the order within each field and within the spectator suffix. -/
theorem phasePackSchedule_fields {α : Type*} {lo hi : ℕ} (pre h mid d suffix : List α)
    (prefixSize : pre.length = lo) (hSize : h.length = hi-lo)
    (middleSize : mid.length = 8-hi+lo) (dSize : d.length = hi-lo) :
    (phasePackSchedule lo hi).foldl (fun xs i => swapAtomAt i xs) (pre++h++mid++d++suffix) =
      h++d++pre++mid++suffix := by
  simp only [phasePackSchedule,List.foldl_append,List.foldl_map]
  have first := middleTailSchedule_packs pre h (mid++d++suffix)
  have last := middleTailSchedule_packs (pre++mid) d suffix
  simp only [prefixSize,hSize,List.append_assoc] at first
  simp only [List.length_append,prefixSize,middleSize,dSize,List.append_assoc] at last
  simp only [List.append_assoc] at *
  rw [first,← hSize,fold_swapAtomAt_prefix,hSize,last]

open Cover.Fallback in
/-- Run the interval packing schedule on a live column record. The two active
fields become the first digits of the physical output word. -/
theorem phaseIncomingPack_exec [M8.Machine.Net] {P U : Type} {T Q lo hi : ℕ} (capacity : rowSwapBlock.states ≤ Q)
    (ordered : lo ≤ hi) (bounded : hi ≤ 8) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (body : P → Pr P T Q prime U) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
    let M := prime^(w+1)
    let is := phasePackSchedule lo hi
    let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
    let clean := fun D : Stacks T prime => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []
    ∀ (v : HS T Q prime U) (S : Stacks T prime) record dest q (before : Fin (M^16*W) → ZMod 2),
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
      SparseRoleCircuit.encode (fun _ => blank) dest 0 q
    stored before S → clean S → ∃ z F n word, z.user = v.user ∧
      n ≤ 1+(setup+swaps*swapVolumeRate w)*(M^16*W) ∧
      Exec body (statePlacedNormalized ports capacity swapStates_pos Empty.elim (packSchedule 16 is))
        (mk v S) n (mk z F) ∧ stored word F ∧ clean F ∧
      (∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      ∀ (x y : Fin 16 → ZMod M) pre h mid d suffix, pre.length = lo → h.length = hi-lo →
        mid.length = 8-hi+lo → d.length = hi-lo → List.ofFn x = pre++h++mid++d++suffix →
        List.ofFn y = h++d++pre++mid++suffix → ∀ j, word (index y j) = before (index x j) := by
  obtain ⟨setup,swaps,price⟩ := packTime_le (P := Empty) (U := U) Empty.elim 16 (phasePackSchedule lo hi) (by decide)
  refine ⟨setup,swaps,?_⟩
  intro w W hW M is bank clean v S record dest q before stored ready free
  have fits : ∀ i ∈ is, i+1 < 16 := fun _ => phasePackSchedule_inside ordered bounded
  obtain ⟨z,F,n,user,time,run,⟨word,out,reads⟩,clear,off⟩ :=
    placedPackSchedule_exec capacity ports is fits body v S record dest q hW before id ⟨before,ready,fun _ _ => rfl⟩ free
  refine ⟨z,F,n,word,user,time.trans (Nat.add_le_add_left (price w W hW) 1),run,out,clear,off,?_⟩
  intro x y pre h mid d suffix hp hh hm hd hx hy j
  have eqn : is.foldl adjacentFields x = y := by
    apply List.ofFn_injective
    rw [fold_adjacentFields is x fits,hx,hy]
    exact phasePackSchedule_fields pre h mid d suffix hp hh hm hd
  rw [← eqn]
  exact reads x j

/-- The packed phase tape and the active-first recursive descriptor assign the
same physical offset to the two interval fields and their four spectators. -/
theorem phasePacked_index {w W lo hi : ℕ}
    (a b : Fin lo → ZMod (prime^(w+1))) (h d : Fin (hi-lo) → ZMod (prime^(w+1)))
    (u v : Fin (8-hi) → ZMod (prime^(w+1))) (j : Fin W) :
    (CopyChildLayout.packActive (phaseIntervalChild lo hi (w+1) W)
      (RecursiveInterchangeScaling.index (phaseIntervalAddress a b h d u v j))).val =
      (index (Fin.addCases (Fin.addCases h d) (Fin.addCases a (Fin.addCases (Fin.addCases u b) v))) j).val := by
  rw [CopyChildLayout.packActive_index,FlatCoordinateLayout.index_val]
  let M := prime^(w+1)
  change ((j.val+W*(rank v).val)+(M^(8-hi)*W)*((rank (Fin.addCases u b)).val+
    M^(8-hi+lo)*((rank a).val+M^lo*(0+1*0))))+
    CopyChildLayout.spectators (phaseIntervalChild lo hi (w+1) W)*
      ((rank d).val+prime^((hi-lo)*(w+1))*(rank h).val) = _
  have width : prime^((hi-lo)*(w+1)) = M^(hi-lo) := by dsimp only [M]; rw [← pow_mul,Nat.mul_comm]
  rw [width]
  simp only [CopyChildLayout.spectators,phaseIntervalChild,one_mul,zero_mul,mul_zero,zero_add,add_zero,
    ArbitraryWidthSliceTranspose.rank_append,pow_add]
  dsimp only [M]
  ring

open IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- A phase interval has one physical row. Regroup its spectators into the
scheduled child's rows while keeping both active fields and the transpose. -/
theorem scheduledPhaseCoordinates (node : Descriptor) (i : Fin nodeChildren5.length)
    (p : ℕ × ℕ) (checked : Geometry.Moves.CheckedPair p) (w B rows : ℕ)
    (rank : nodeChildren5[i.val] = Geometry.moveRank p.1 p.2)
    (width : node.width = 64*w) (split : node.rows = 142080*rows)
    (label : node.beforeH = B*prime^(64*(w*64))) :
    let K := (prime^w)^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*(w*64))*K
    let a := Geometry.Dimensions.value p.1
    let b := Geometry.Dimensions.value p.2
    let packed := phaseIntervalChild (min a b) (max a b) w W
    let child := scheduledChild prime node i
    ∃ e : Fin (volume prime packed) ≃ Fin (volume prime child),
      (∀ j, (CopyChildLayout.packActive child (e j)).val = (CopyChildLayout.packActive packed j).val) ∧
      ∀ {α : Type} (x : Fin (volume prime child) → α),
        Shared50RecursiveNodeRows.transpose (one_dvd packed.rows) (x ∘ e) =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x ∘ e := by
  intro K W a b packed child
  obtain ⟨pw,pv⟩ := phaseChild_parent_measures node w B rows p checked width split label
  obtain ⟨cw,cv⟩ := scheduledChild_measures prime node ⟨w,width⟩ ⟨rows,split⟩ i
  change packed.width*64 = _ at pw
  change child.width*64 = _ at cw
  rw [rank] at cw
  have sameWidth : packed.width = child.width := by omega
  change volume prime packed*142080 = _ at pv
  change volume prime child*142080 = _ at cv
  have sameVolume : volume prime packed = volume prime child := by omega
  have count (d : Descriptor) : volume prime d = prime^d.width*prime^d.width*CopyChildLayout.spectators d := by
    unfold volume CopyChildLayout.spectators
    ring
  rw [count,count,sameWidth] at sameVolume
  have size := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _)
    (pow_pos Shared50ModularControl.prime_prime.pos _)) sameVolume
  let f := CopyChildLayout.changeLayout packed child sameWidth size
  let e := (CopyChildLayout.flatAddress packed).symm.trans (f.trans (CopyChildLayout.flatAddress child))
  refine ⟨e,?_,fun x => funext (transpose_changeLayout packed child sameWidth size x)⟩
  intro j
  let addr := (CopyChildLayout.flatAddress packed).symm j
  have src : RecursiveInterchangeScaling.index addr = j := (CopyChildLayout.flatAddress packed).apply_symm_apply j
  exact (CopyChildLayout.packActive_change packed child sameWidth size addr).trans
    (congrArg (fun z => (CopyChildLayout.packActive packed z).val) src)

private theorem digits_of_length {α : Type*} {n : ℕ} (xs : List α) (size : xs.length = n) :
    ∃ x : Fin n → α, List.ofFn x = xs := by
  subst n
  exact ⟨xs.get,List.ofFn_get xs⟩

private theorem index_eq_of_digits {M n m W : ℕ} [NeZero M]
    (x : Fin n → ZMod M) (y : Fin m → ZMod M) (same : List.ofFn x = List.ofFn y) (j : Fin W) :
    (index x j).val = (index y j).val := by
  have sizes := congrArg List.length same
  simp only [List.length_ofFn] at sizes
  subst m
  rw [List.ofFn_injective same]

open IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Read an actual scheduled child transpose at the addresses produced by
phase packing, including all exterior digits and the trailing spectator. -/
theorem scheduledPhasePacked_swap (node : Descriptor) (i : Fin nodeChildren5.length)
    (p : ℕ × ℕ) (checked : Geometry.Moves.CheckedPair p) (paid : 0 < Geometry.moveRank p.1 p.2)
    (w B rows : ℕ) (rank : nodeChildren5[i.val] = Geometry.moveRank p.1 p.2)
    (width : node.width = 64*(w+1)) (split : node.rows = 142080*rows)
    (label : node.beforeH = B*prime^(64*((w+1)*64))) :
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    let lo := min (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    let hi := max (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    let child := scheduledChild prime node i
    ∃ position : Fin (volume prime child) ≃ Fin (M^16*W),
      (∀ k, (position k).val = (CopyChildLayout.packActive child k).val) ∧
      ∀ {α : Type} (word changed : Fin (M^16*W) → α),
        (∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) k) →
        ∀ (x y : Fin 16 → ZMod M) h d rest, h.length = hi-lo → d.length = hi-lo →
          List.ofFn x = h++d++rest → List.ofFn y = d++h++rest → ∀ j, changed (index y j) = word (index x j) := by
  intro M K W lo hi child
  let packed := phaseIntervalChild lo hi (w+1) W
  obtain ⟨e,route,action⟩ := scheduledPhaseCoordinates node i p checked (w+1) B rows rank width split label
  obtain ⟨lt,bound⟩ := phaseInterval_bounds checked paid
  have size := Fintype.card_congr (e.trans (CopyChildLayout.packActive child))
  simp only [Fintype.card_fin] at size
  have count : volume prime packed = M^16*W := phaseIntervalChild_volume lt.le bound _ _
  let position := (CopyChildLayout.packActive child).trans (finCongr (size.symm.trans count))
  refine ⟨position,fun _ => rfl,?_⟩
  intro α word changed returned x y h d rest hh hd hx hy j
  obtain ⟨h,rfl⟩ := digits_of_length h hh
  obtain ⟨d,rfl⟩ := digits_of_length d hd
  have sizeRest := congrArg List.length hx
  simp only [List.length_ofFn,List.length_append] at sizeRest
  change lo < hi at lt
  change hi ≤ 8 at bound
  obtain ⟨suffix,rfl⟩ := digits_of_length rest (show rest.length = lo+((8-hi+lo)+(8-hi)) by omega)
  let a := fun k : Fin lo => suffix (k.castAdd _)
  let tail := fun k : Fin ((8-hi+lo)+(8-hi)) => suffix (k.natAdd lo)
  let mid := fun k : Fin (8-hi+lo) => tail (k.castAdd (8-hi))
  let v := fun k : Fin (8-hi) => tail (k.natAdd (8-hi+lo))
  let u := fun k : Fin (8-hi) => mid (k.castAdd lo)
  let b := fun k : Fin lo => mid (k.natAdd (8-hi))
  have parts : Fin.append a (Fin.append (Fin.append u b) v) = suffix := by
    rw [show Fin.append u b = mid from Fin.append_castAdd_natAdd,
      show Fin.append mid v = tail from Fin.append_castAdd_natAdd]
    exact Fin.append_castAdd_natAdd
  let digits := fun h d : Fin (hi-lo) → ZMod M => Fin.append (Fin.append h d) (Fin.append a (Fin.append (Fin.append u b) v))
  let addr := fun h d => RecursiveInterchangeScaling.index (phaseIntervalAddress a b h d u v j)
  have loc (h d : Fin (hi-lo) → ZMod M) (z : Fin 16 → ZMod M)
      (layout : List.ofFn z = List.ofFn h++List.ofFn d++List.ofFn suffix) : index z j = position (e (addr h d)) := by
    apply Fin.ext
    have lists : List.ofFn z = List.ofFn (digits h d) := by
      simp only [digits,parts,List.ofFn_fin_append,layout]
    exact (index_eq_of_digits z (digits h d) lists j).trans
      ((phasePacked_index a b h d u v j).symm.trans (route (addr h d)).symm)
  rw [loc d h y hy,loc h d x hx,returned]
  have eqn := congrFun (action (word ∘ position)) (addr d h)
  exact eqn.symm.trans (intervalAddress_transpose 8 ((word ∘ position) ∘ e) a b h d u v j)

private theorem phaseTranspose_of_reads {α : Type*} {lo hi w W : ℕ}
    (ordered : lo ≤ hi) (bound : hi ≤ 8) (before after : Fin ((prime^(w+1))^16*W) → α)
    (reads : ∀ s j, after (index (AffineFieldCoordinates.embed (IntegerMultBounds.Swap.Shear.run (intervalSwaps lo hi) s)) j) =
      before (index (AffineFieldCoordinates.embed s) j)) :
    let size := phaseIntervalChild_volume ordered bound (w+1) W
    after = fun i => Shared50RecursiveNodeRows.transpose (v := phaseIntervalChild lo hi (w+1) W)
      (one_dvd _) (fun j => before (j.cast size)) (i.cast size.symm) := by
  intro size
  funext k
  obtain ⟨⟨s,j⟩,rfl⟩ := (copyAddress (Q := prime^(w+1)) (W := W)).symm.surjective k
  let D : Matrix (Fin 8) (Fin 8) (ZMod (prime^(w+1))) := diagonal fun i => if lo ≤ i.val ∧ i.val < hi then 1 else 0
  have idem : D*D = D := by
    unfold D
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  let t := IntegerMultBounds.Swap.Shear.run (intervalSwaps lo hi) s
  have back : IntegerMultBounds.Swap.Shear.run (intervalSwaps lo hi) t = s := by
    simpa only [t,intervalSwaps_run,D] using M8.Global.exchange_involutive idem s
  rw [copyAddress_index,← back]
  exact (reads t j).trans (phaseChild_interval ordered bound before t j).symm

open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Pack a live phase record, call the child once, and restore the parent's
digit order. The child exchanges the two leading active fields. -/
theorem phasePackedCall_exec [M8.Machine.Net] {P U : Type} {T Q : ℕ} (capacity : rowSwapBlock.states ≤ Q)
    (p : ℕ × ℕ) (checked : Geometry.Moves.CheckedPair p) (paid : 0 < Geometry.moveRank p.1 p.2)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (body : P → Pr P T Q prime U) (f : P) :
    let lo := min (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    let hi := max (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    ∃ setup swaps : ℕ, ∀ (node : Descriptor) (i : Fin nodeChildren5.length) (w B rows : ℕ),
    nodeChildren5[i.val] = Geometry.moveRank p.1 p.2 → node.width = 64*(w+1) →
    node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    0 < W →
    let desc := scheduledChild prime node i
    ∃ position : Fin (volume prime desc) ≃ Fin (M^16*W),
    (∀ k, (position k).val = (CopyChildLayout.packActive desc k).val) ∧
    let is := phasePackSchedule lo hi
    let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
    let clean := fun D : Stacks T prime => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []
    let pack := fun js => statePlacedNormalized ports capacity swapStates_pos Empty.elim (packSchedule 16 js)
    ∀ (v : HS T Q prime U) (S : Stacks T prime) record dest q (before : Fin (M^16*W) → ZMod 2) budget,
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
      SparseRoleCircuit.encode (fun _ => blank) dest 0 q
    (desc.width < node.width → ∀ (u : HS T Q prime U) D word, stored word D → clean D →
      ∃ z F n changed, Exec body (body f) (mk u D) n (mk z F) ∧ n ≤ budget ∧ z.user = u.user ∧
        stored changed F ∧ clean F ∧ (∀ j, (∀ i, ports i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
        ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (word ∘ position) k) →
    let size := phaseIntervalChild_volume (phaseInterval_bounds checked paid).1.le
      (phaseInterval_bounds checked paid).2 (w+1) W
    let after := fun k => Shared50RecursiveNodeRows.transpose (v := phaseIntervalChild lo hi (w+1) W)
      (one_dvd _) (fun j => before (j.cast size)) (Fin.cast size.symm k)
    stored before S → clean S → ∃ z F n, z.user = v.user ∧
      n ≤ budget+4+(setup+swaps*swapVolumeRate w)*(M^16*W) ∧
      Exec body ((pack is).seq ((Prog.call f).seq (pack is.reverse))) (mk v S) n (mk z F) ∧
      stored after F ∧ clean F ∧ ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro lo hi
  obtain ⟨lt,bounded⟩ := phaseInterval_bounds checked paid
  have ordered : lo ≤ hi := lt.le
  obtain ⟨a,b,enter⟩ := phaseIncomingPack_exec capacity ordered bounded ports body
  obtain ⟨c,e,price⟩ := packTime_le (P := Empty) (U := U) Empty.elim 16 (phasePackSchedule lo hi).reverse (by decide)
  refine ⟨a+c,b+e,?_⟩
  intro node i w B rows rank width split label M K W hW desc
  obtain ⟨position,offset,action⟩ := scheduledPhasePacked_swap node i p checked paid w B rows rank width split label
  refine ⟨position,offset,?_⟩
  have smaller : desc.width < node.width := by
    have r := nodeChildren5_le i
    have scaled := Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt r (by decide : 42 < 64)) (Nat.succ_pos w)
    simpa only [desc,scheduledChild,rankDescriptor,width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)] using scaled
  intro is bank clean pack v S record dest q before budget stored child size expected ready free
  obtain ⟨u,D,t,word,userA,timeA,runA,readyA,freeA,offA,readsA⟩ := (enter w W hW v S record dest q before ready free)
  obtain ⟨z,G,m,changed,run,time,user,readyB,freeB,off,returned⟩ := child smaller u D _ readyA freeA
  have swap := action word changed returned
  have fits : ∀ i ∈ is, i+1 < 16 := fun _ => phasePackSchedule_inside ordered bounded
  obtain ⟨y,F,n,userB,timeB,runB,⟨after,out,reads⟩,clear,offB⟩ :=
    placedPackSchedule_exec capacity ports is.reverse (fun i hi => fits i (List.mem_reverse.mp hi)) body z G
      record dest q hW changed id ⟨changed,readyB,fun _ _ => rfl⟩ freeB
  refine ⟨y,F,_,userB.trans (user.trans userA),?_,Exec.seq runA (Exec.seq (Exec.call run) runB),?_,clear,?_⟩
  · have back := timeB.trans (Nat.add_le_add_left (price w W hW) 1)
    simp only [M,Nat.add_mul] at timeA back ⊢
    omega
  · suffices after = expected by simpa only [← this] using out
    apply phaseTranspose_of_reads ordered bounded
    intro s j
    let x := AffineFieldCoordinates.embed s
    let y := AffineFieldCoordinates.embed (IntegerMultBounds.Swap.Shear.run (intervalSwaps lo hi) s)
    obtain ⟨pre,h,mid,d,suffix,hp,hh,hm,hd,hx,hy⟩ := phaseInterval_digits ordered bounded s
    change List.ofFn x = _ at hx
    change List.ofFn y = _ at hy
    let route := fun z : Fin 16 → ZMod M => is.foldl adjacentFields z
    have left : List.ofFn (route x) = h++d++pre++mid++suffix := by
      rw [show List.ofFn (route x) = _ from fold_adjacentFields is x fits,hx]
      exact phasePackSchedule_fields pre h mid d suffix hp hh hm hd
    have right : List.ofFn (route y) = d++h++pre++mid++suffix := by
      rw [show List.ofFn (route y) = _ from fold_adjacentFields is y fits,hy]
      exact phasePackSchedule_fields pre d mid h suffix hp hd hm hh
    have moved := swap (route x) (route y) h d (pre++mid++suffix) hh hd
      (by simpa only [List.append_assoc] using left) (by simpa only [List.append_assoc] using right) j
    have back := reads (route y) j
    simp only [id_eq,route,reverse_adjacentFields] at back
    exact back.trans (moved.trans (readsA x (route x) pre h mid d suffix hp hh hm hd hx left j))

  · intro j hj
    obtain ⟨l,r⟩ := offA j hj
    obtain ⟨l',r'⟩ := off j hj
    obtain ⟨l'',r''⟩ := offB j hj
    exact ⟨l''.trans (l'.trans l),r''.trans (r'.trans r)⟩

open Cover.Fallback in
private theorem owners_of_returned_record {T k w d W H J : ℕ}
    (slots : Fin k ↪ Fin T) (src : Fin k) (bank : Fin 35 ↪ Fin T) (shared : slots src = bank 24)
    (data : Fin k → Fin ((prime^(w+1))^d*W) → ZMod 2) (y : Fin ((prime^(w+1))^d*W) → ZMod 2)
    {S G : Stacks T prime} {record dest q}
    (initial : RepT (phaseOwners data) (embStk slots S).L (embStk slots S).R)
    (finalRecord : RecordReady (b := prime) (w := w) (d := d) (W := W) bank H J record
      SparseRoleCircuit.encode (fun _ => blank) dest 0 q y G)
    (outside : ∀ i, i ≠ src → G.L (slots i) = S.L (slots i) ∧ G.R (slots i) = S.R (slots i)) :
    RepT (phaseOwners (Function.update data src y)) (embStk slots G).L (embStk slots G).R := by
  intro i l
  by_cases eq : i = src
  · subst i
    have cell := finalRecord.src l
    simp only [phaseOwners,Function.update_self,embStk,Function.comp_apply,sub_zero,shared]
    have read := (encodedOwnerCell y l).symm
    simp only [List.map_ofFn] at read
    exact read.trans (by simpa only [sub_zero] using cell.symm)
  · obtain ⟨l',r'⟩ := outside i eq
    simpa only [phaseOwners,Function.update_of_ne eq,embStk,Function.comp_apply,l',r'] using initial i l

-- The separate fifteen-field COPY host proof can be restored from 2e053b99.

theorem placedHoare_exec {k q T Q b : ℕ} {P U : Type}
    (machine : Program k q prime) (bank : Fin k ↪ Fin T) (fits : q ≤ Q)
    (body : P → Pr P T Q prime U) {X Y : Tapes k prime}
    (run : HoareTime machine (fun x => x = X) (fun y => y = Y) b)
    (u : HS T Q prime U) (S : Stacks T prime) (ready : RepT X (embStk bank S).L (embStk bank S).R) :
    ∃ z F n, Exec body (embProg bank (Empty.elim : Empty → P) (foreign (liftQ machine fits)))
      (mk u S) n (mk z F) ∧ n ≤ b*(k+5)+6 ∧ z.user = u.user ∧
      RepT Y (embStk bank F).L (embStk bank F).R ∧
      ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨v,A,_,rfl,full,user,_,_,_,n,time,exec⟩ := foreign_exec (body := (Empty.elim : Empty → _))
    (liftQ _ fits) (HoareTime.liftQ fits run) (embDn bank u) (embStk bank S) _ rfl ready
  obtain ⟨z,F,placed,_,same,view,off⟩ := exec_emb (ι := (Empty.elim : Empty → P))
    (body' := body) bank.injective (fun f => f.elim) exec u rfl S rfl
  subst A
  exact ⟨z,F,n,placed,time,same.trans user,full,off⟩

open M8.RevMachine RecursiveInterchangeLayout IntegerMultBounds.Networks.Certificates.PR589 in
/-- Execute either chart route of a COPY window on its assigned host tapes. The
returned bank includes the route controls and the untouched owners. -/
theorem copyRoute_host [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (enter : Bool) (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) :
    let io := fun j : ℕ => ownerTape n r d (Fin.ofNat 661 j)
    let src := io life.source
    ∃ (route : Graph.Block (142081+24) prime) (C : ℕ), Blocks.Leading route ∧
    ∀ {T Q : ℕ} {P U : Type} (ports : Fin route.tapes ↪ Fin T) (fits : route.states ≤ Q)
      (body : P → Pr P T Q prime U) (v : Descriptor) (w B : ℕ), 0 < w → 0 < B →
      v.beforeH = B*prime^(64*(w*64)) → v.Positive →
    let V := volume prime v
    let A := registerChart w n life.source
    let bank := fun x => SharedBankStageInput.raw
      (LabelCall.bank (copyOwners (v := v) x) v (M8.Stage2Machine.Straight.words (LabelSchedule.base v w))) route.tapes
    ∀ (x : Fin 142081 → Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime),
      RepT (bank x) (embStk ports S).L (embStk ports S).R →
      ∃ y z F t, Exec body (embProg ports (Empty.elim : Empty → P) (foreign (liftQ route.program fits)))
          (mk u S) t (mk z F) ∧
        t ≤ (C*V+(63+252*life.targets.length)*LeafCore.coreCost V (w*64)+life.targets.length+1)*(route.tapes+5)+6 ∧
        z.user = u.user ∧ RepT (bank y) (embStk ports F).L (embStk ports F).R ∧
        LabelPermutation.Transport v B w (fun g => g*(if enter then A.transpose else A)) (ext (x src)) (ext (y src)) ∧
        (∀ j ∈ life.targets, LabelPermutation.Transport v B w
          (fun g => g*registerChart w n j) (ext (x (io j))) (ext (y (io j)))) ∧
        (∀ k, k ≠ src → k ∉ life.targets.map io → y k = x k) ∧
        ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro io src
  obtain ⟨route,C,leading,run⟩ := copyWindow_routes n r d enter life scheduled
  refine ⟨route,C,leading,?_⟩
  intro T Q P U ports fits body v w B hw hB shape pos V A bank x u S ready
  obtain ⟨y,source,targets,unchanged,exec⟩ := run v w B hw hB shape pos x
  obtain ⟨z,F,t,placed,time,user,done,off⟩ := placedHoare_exec _ ports fits body exec u S ready
  exact ⟨y,z,F,t,placed,time,user,done,source,targets,unchanged,off⟩

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Put the nine COPY programs on the same owner tapes, with a distinct private
tape for every other local slot. This also separates equal-sized workspaces. -/
theorem copyWindowBanks {I : Type} [Fintype I] {k : ℕ} (tapes : I → ℕ)
    (owner : ∀ i, Fin k ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (shared : Fin k ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
      (∀ i j, bank i (owner i j) = shared j) ∧
      (∀ X : Stacks k prime, ∀ initial : (i : I) → Stacks (tapes i) prime,
        ∃ S : Stacks T prime, embStk shared S = X ∧ ∀ i l, (∀ j, owner i j ≠ l) →
          S.L (bank i l) = (initial i).L l ∧ S.R (bank i l) = (initial i).R l) ∧
      ∀ i l, (∀ j, owner i j ≠ l) →
        (∀ j, shared j ≠ bank i l) ∧ ∀ m, m ≠ i → ∀ j, bank m j ≠ bank i l := by
  classical
  let J := (i : I) × {l : Fin (tapes i) // ∀ j, owner i j ≠ l}
  let N := Fintype.card J
  let slot (i) (l : Fin (tapes i)) : Fin (k+N) :=
    if h : ∃ j, owner i j = l then h.choose.castAdd N
    else ((Fintype.equivFin J) ⟨i,l,fun j eq => h ⟨j,eq⟩⟩).natAdd k
  have selected (i j) : slot i (owner i j) = j.castAdd N := by
    have h : ∃ x, owner i x = owner i j := ⟨j,rfl⟩
    simp only [slot,dif_pos h,(owner i).injective h.choose_spec]
  have unused (i l) (off : ∀ j, owner i j ≠ l) :
      slot i l = ((Fintype.equivFin J) ⟨i,l,off⟩).natAdd k := by
    simp only [slot,dif_neg (show ¬ ∃ j, owner i j = l from fun ⟨j,h⟩ => off j h)]
  have sep (i l) (off : ∀ j, owner i j ≠ l) (j : Fin k) : j.castAdd N ≠ slot i l := by
    rw [unused i l off]
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  let bank (i) : Fin (tapes i) ↪ Fin (k+N) := ⟨slot i,by
    intro l m eq
    by_cases hl : ∃ j, owner i j = l
    · obtain ⟨j,rfl⟩ := hl
      rw [selected] at eq
      by_cases hm : ∃ h, owner i h = m
      · obtain ⟨h,rfl⟩ := hm
        rw [selected] at eq
        exact congrArg (owner i) ((Fin.castAddEmb N).injective eq)
      · exact False.elim (sep i m (fun h e => hm ⟨h,e⟩) j eq)
    · have off := fun j e => hl (Exists.intro j e)
      by_cases hm : ∃ h, owner i h = m
      · obtain ⟨h,rfl⟩ := hm
        rw [selected] at eq
        exact False.elim (sep i l off h eq.symm)
      · rw [unused i l off,unused i m (fun h e => hm ⟨h,e⟩)] at eq
        have same := (Fintype.equivFin J).injective ((Fin.natAdd_injective N k) eq)
        exact Fin.ext (congrArg (fun p : J => p.2.val.val) same)⟩
  refine ⟨k+N,Fin.castAddEmb N,bank,selected,?_,?_⟩
  · intro X initial
    let collect (get : ∀ i, Fin (tapes i) → List (Fin (prime+4))) (p : Fin N) :=
      let j := (Fintype.equivFin J).symm p
      get j.1 j.2.val
    let S : Stacks (k+N) prime := ⟨X.inp,X.out,Fin.addCases X.L (collect (fun i => (initial i).L)),
      Fin.addCases X.R (collect (fun i => (initial i).R))⟩
    refine ⟨S,?_,?_⟩
    · cases X
      simp [S,embStk,Function.comp_def]
    · intro i l off
      change S.L (slot i l) = _ ∧ S.R (slot i l) = _
      rw [unused i l off]
      have decode := (Fintype.equivFin J).symm_apply_apply (⟨i,l,off⟩ : J)
      simp only [S,Fin.addCases_right,collect]
      exact ⟨congrArg (fun p : J => (initial p.1).L p.2.val) decode,
        congrArg (fun p : J => (initial p.1).R p.2.val) decode⟩
  intro i l off
  refine ⟨sep i l off,?_⟩
  intro m ne j
  change slot m j ≠ slot i l
  by_cases mapped : ∃ x, owner m x = j
  · obtain ⟨x,rfl⟩ := mapped
    rw [selected]
    exact sep i l off x
  · rw [unused m j (fun x eq => mapped ⟨x,eq⟩),unused i l off]
    intro eq
    have slots := (Fin.natAdd_injective N k) eq
    exact ne (congrArg Sigma.fst ((Fintype.equivFin J).injective slots))

open Cover.Fallback in
/-- Append the two chart workspaces to the running COPY machine. Only the
specified owner ports of either chart coincide with the original machine. -/
theorem copyChartPlacement {T k m n : ℕ} (owners : Fin k ↪ Fin T)
    (entry : Fin k ↪ Fin m) (leave : Fin k ↪ Fin n) :
    let parent := (Fin.castAddEmb (n := T) m).trans (Fin.castAddEmb n)
    ∃ (a : Fin m ↪ Fin ((T+m)+n)) (b : Fin n ↪ Fin ((T+m)+n)),
      (∀ i, a (entry i) = parent (owners i) ∧ b (leave i) = parent (owners i)) ∧
      (∀ j, (∀ i, owners i ≠ j) → (∀ l, a l ≠ parent j) ∧ (∀ l, b l ≠ parent j)) ∧
      (∀ j, (∀ i, leave i ≠ j) → (∀ l, a l ≠ b j) ∧ (∀ l, parent l ≠ b j)) ∧
      ∀ j, (∀ i, entry i ≠ j) → (∀ l, b l ≠ a j) ∧ (∀ l, parent l ≠ a j) := by
  intro parent
  have install {t s : ℕ} (shared : Fin k ↪ Fin t) (slots : Fin k ↪ Fin s) :
      ∃ e : Fin s ↪ Fin (t+s), (∀ i, e (slots i) = (shared i).castAdd s) ∧
        ∀ j, (∀ i, slots i ≠ j) → e j = j.natAdd t := by
    let lift : Fin s ↪ Fin (k+s) := ⟨SharedBank.slot slots,SharedBank.slot_injective slots⟩
    refine ⟨lift.trans (appendPrivate shared s),?_,?_⟩
    · intro i
      change appendPrivate shared s (SharedBank.slot slots (slots i)) = _
      rw [SharedBank.slot_selected _ slots.injective,appendPrivate_shared]
    · intro j off
      have absent : ¬ ∃ i, slots i = j := fun ⟨i,h⟩ => off i h
      change appendPrivate shared s (SharedBank.slot slots j) = _
      rw [SharedBank.slot,dif_neg absent,appendPrivate_work]
  obtain ⟨left,leftOwner,leftPrivate⟩ := install owners entry
  obtain ⟨right,rightOwner,rightPrivate⟩ := install (owners.trans (Fin.castAddEmb m)) leave
  have sep {u v : ℕ} (i : Fin u) (j : Fin v) : i.castAdd v ≠ j.natAdd u := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  refine ⟨left.trans (Fin.castAddEmb n),right,fun i => ⟨congrArg (Fin.castAdd n) (leftOwner i),rightOwner i⟩,?_,?_,?_⟩
  · intro j off
    constructor
    · intro l
      apply (Fin.castAddEmb n).injective.ne
      by_cases h : ∃ i, entry i = l
      · obtain ⟨i,rfl⟩ := h
        rw [leftOwner]
        exact (Fin.castAddEmb m).injective.ne (off i)
      · rw [leftPrivate l (fun i eq => h ⟨i,eq⟩)]
        exact (sep j l).symm
    · intro l
      by_cases h : ∃ i, leave i = l
      · obtain ⟨i,rfl⟩ := h
        rw [rightOwner]
        exact parent.injective.ne (off i)
      · rw [rightPrivate l (fun i eq => h ⟨i,eq⟩)]
        exact (sep _ l).symm
  · intro j off
    rw [rightPrivate j off]
    exact ⟨fun l => sep (left l) j,fun l => sep (l.castAdd m) j⟩
  · intro j off
    have against (l : Fin T) : parent l ≠ (left j).castAdd n := by
      apply (Fin.castAddEmb n).injective.ne
      rw [leftPrivate j off]
      exact sep l j
    refine ⟨?_,against⟩
    intro l
    by_cases h : ∃ i, leave i = l
    · obtain ⟨i,rfl⟩ := h
      rw [rightOwner]
      exact against (owners i)
    · rw [rightPrivate l (fun i eq => h ⟨i,eq⟩)]
      exact (sep (left j) l).symm

open M8.RevMachine RecursiveInterchangeLayout in
/-- Reassemble a chart bank from the current owner tapes and the saved chart controls. -/
private theorem copyRoute_ready {k T : ℕ} (route : Graph.Block (k+24) prime) (leading : Blocks.Leading route)
    (ports : Fin route.tapes ↪ Fin T) (v : Descriptor) (d : Fin 22 → Option (List Bool))
    (x y : Tapes k prime) (S F : Stacks T prime) :
    let bank := fun x => SharedBankStageInput.raw (LabelCall.bank x v d) route.tapes
    let slot := fun i => route.slots (Fin.castAdd 24 i)
    RepT (bank x) (embStk ports S).L (embStk ports S).R →
    RepT y (embStk (fun i => ports (slot i)) F).L (embStk (fun i => ports (slot i)) F).R →
    (∀ j, (∀ i, slot i ≠ j) → F.L (ports j) = S.L (ports j) ∧ F.R (ports j) = S.R (ports j)) →
    RepT (bank y) (embStk ports F).L (embStk ports F).R := by
  intro bank slot initial owners keep j h
  by_cases shared : ∃ i, slot i = j
  · obtain ⟨i,rfl⟩ := shared
    have payload := copyRoute_payload route leading y v d
    have tape := congrArg (fun b : Tapes k prime => b.tape i h) payload
    have head := congrArg (fun b : Tapes k prime => b.head i) payload
    change (bank y).head (slot i) = y.head i at head
    rw [head]
    exact tape.trans (owners i h)
  · obtain ⟨l,r⟩ := keep j (fun i eq => shared ⟨i,eq⟩)
    have eq := routePrivate route leading y x v d
    have tape := congrArg (fun b : Tapes route.tapes prime => b.tape j h) eq
    have head := congrArg (fun b : Tapes route.tapes prime => b.head j) eq
    change (SharedBank.strip (bank y) slot).tape j h = (SharedBank.strip (bank x) slot).tape j h at tape
    change (SharedBank.strip (bank y) slot).head j = (SharedBank.strip (bank x) slot).head j at head
    simp only [SharedBank.strip,shared,ite_false] at tape head
    simpa only [embStk,Function.comp_apply,tape,head,l,r] using initial j h

open M8.RevMachine RecursiveInterchangeLayout IntegerMultBounds.Networks.Certificates.PR589 in
/-- Run the two physical chart programs around a common-chart COPY execution. Only
owner tapes are shared with the return chart, whose saved controls survive the body. -/
theorem routedCopyWindow_host [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) :
    ∃ (enter leave : Graph.Block (142081+24) prime) (C E : ℕ), Blocks.Leading enter ∧ Blocks.Leading leave ∧
    ∀ {T Q : ℕ} {P U : Type} (a : Fin enter.tapes ↪ Fin T) (b : Fin leave.tapes ↪ Fin T)
      (fan : Fin (142081+2) ↪ Fin T) (fitsA : enter.states ≤ Q) (fitsB : leave.states ≤ Q)
      (body : P → Pr P T Q prime U) (inner : Pr P T Q prime U) (keep : Fin T → Prop) (budget w B K : ℕ),
    0 < w → 0 < B → 0 < K →
    let v := copyLabelLayout w B K
    let V := volume prime v
    let headers := M8.Stage2Machine.Straight.words (LabelSchedule.base v w)
    let bank := fun x => LabelCall.bank (copyOwners (v := v) x) v headers
    let slot := fun i => leave.slots (Fin.castAdd 24 i)
    let owner := fun i => b (slot i)
    let privateEntry := fun j => ∀ i : Fin 142081, enter.slots (i.castAdd 24) ≠ j
    let privateSlot := fun j => ∀ i, slot i ≠ j
    let price := fun c t => (c*V+(63+252*life.targets.length)*LeafCore.coreCost V (w*64)+life.targets.length+1)*(t+5)+6
    (∀ i, a (enter.slots (Fin.castAdd 24 i)) = fan (Fin.castAdd 2 i)) →
    (∀ i : Fin 2, ∀ j, a j ≠ fan (i.natAdd 142081)) →
    (∀ i, owner i = fan (Fin.castAdd 2 i)) →
    (∀ i : Fin 2, ∀ j, b j ≠ fan (i.natAdd 142081)) →
    (∀ j, privateSlot j → ∀ k, a k ≠ b j) →
    (∀ j, privateEntry j → ∀ k, b k ≠ a j) →
    ∀ (x : Fin 142081 → Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime),
    RepT (SharedBankStageInput.raw (bank x) enter.tapes) (embStk a S).L (embStk a S).R →
    RepT (SharedBankStageInput.raw (bank x) leave.tapes) (embStk b S).L (embStk b S).R →
    let size := copyLabel_volume w B K
    let flatten := fun (X : Fin 142081 → Fin V → ZMod 2) k i => X k (Fin.cast size.symm i)
    let fanReady := fun X (D : Stacks T prime) => RepT (PointwiseRoleGate.bank (a := prime)
      (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded (flatten X)) (FlatCoordinateSchedule.bits V))
      (embStk fan D).L (embStk fan D).R
    fanReady x S →
    (∀ entered v' D, entered (Fin.last 142080) = x (Fin.last 142080) → fanReady entered D →
      (∀ j, (∀ i, a i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
      let data := flatten entered
      ∃ y z F t, Exec body inner (mk v' D) t (mk z F) ∧ t ≤ budget ∧ z.user = v'.user ∧
        fanReady (fun k i => y k (Fin.cast size i)) F ∧
        CopyFanoutEffect n r d life scheduled w B K data y ∧
        (∀ j, privateEntry j → F.L (a j) = D.L (a j) ∧ F.R (a j) = D.R (a j)) ∧
        (∀ j, privateSlot j → F.L (b j) = D.L (b j) ∧ F.R (b j) = D.R (b j)) ∧
        ∀ j, keep j → (∀ i, a i ≠ j) → (∀ i, b i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) →
    ∃ out z F t, Exec body ((embProg a (Empty.elim : Empty → P) (foreign (liftQ enter.program fitsA))).seq
        (inner.seq (embProg b (Empty.elim : Empty → P) (foreign (liftQ leave.program fitsB)))))
        (mk u S) t (mk z F) ∧ t ≤ price C enter.tapes+budget+price E leave.tapes ∧ z.user = u.user ∧
      RepT (SharedBankStageInput.raw (bank out) leave.tapes) (embStk b F).L (embStk b F).R ∧
      RepT (SharedBankStageInput.raw (bank out) enter.tapes) (embStk a F).L (embStk a F).R ∧
      fanReady out F ∧ CopyWindowEffect n r d life w B K x out ∧
      ∀ j, keep j → (∀ i, a i ≠ j) → (∀ i, b i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨enter,C,enterLeading,entry⟩ := copyRoute_host n r d true life scheduled
  obtain ⟨leave,E,leading,exitRun⟩ := copyRoute_host n r d false life scheduled
  refine ⟨enter,leave,C,E,enterLeading,leading,?_⟩
  intro T Q P U a b fan fitsA fitsB body inner keep budget w B K hw hB hK v V headers bank slot owner privateEntry privateSlot price shared controls sharedB controlsB apart apartB
    x u S left right size flatten fanReady initial run
  have pos : v.Positive := ⟨pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _,Nat.zero_lt_one,
    Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _),Nat.zero_lt_one,hK⟩
  obtain ⟨entered,v',D,t,first,timeA,userA,loaded,source,targets,others,offA⟩ :=
    entry a fitsA body v w B hw hB rfl pos x u S left
  have eq (X : Fin 142081 → Fin V → ZMod 2) : (fun k i => flatten X k (Fin.cast size i)) = X := by
    funext k i
    simp [flatten]
  have transfer (route : Graph.Block (142081+24) prime) (leading : Blocks.Leading route)
      (ports : Fin route.tapes ↪ Fin T) (shared : ∀ i, ports (route.slots (Fin.castAdd 24 i)) = fan (Fin.castAdd 2 i))
      (old new : Fin 142081 → Fin V → ZMod 2) (S D : Stacks T prime)
      (initial : fanReady old S) (loaded : RepT (SharedBankStageInput.raw (bank new) route.tapes) (embStk ports D).L (embStk ports D).R)
      (controls : ∀ j : Fin 2, D.L (fan (j.natAdd 142081)) = S.L (fan (j.natAdd 142081)) ∧
        D.R (fan (j.natAdd 142081)) = S.R (fan (j.natAdd 142081))) : fanReady new D := by
    dsimp only [fanReady] at initial ⊢
    rw [copyOwners_controls size (flatten old),eq] at initial
    rw [copyOwners_controls size (flatten new),eq]
    intro j z
    induction j using Fin.addCases with
    | left j =>
      have payload := copyRoute_payload route leading (copyOwners (v := v) new) v headers
      let tape := SharedBankStageInput.raw (bank new) route.tapes
      let site := route.slots (Fin.castAdd 24 j)
      have cell : tape.tape site z = (copyOwners new).tape j z := congrArg (fun b : Tapes 142081 prime => b.tape j z) payload
      have head : tape.head site = (copyOwners new).head j := congrArg (fun b : Tapes 142081 prime => b.head j) payload
      have read := loaded site z
      change tape.tape site z = readAt blank (D.L (ports site)) (D.R (ports site)) (z-tape.head site) at read
      rw [cell,head,show ports site = _ from shared j] at read
      simpa only [Tapes.append,Fin.addCases_left,embStk,Function.comp_apply] using read
    | right j =>
      obtain ⟨l,r⟩ := controls j
      simpa only [Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,l,r] using initial (j.natAdd 142081) z
  have fanInput := transfer enter enterLeading a shared x entered S D initial loaded (fun j => offA _ (controls j))
  have retainedTmp : entered (Fin.last 142080) = x (Fin.last 142080) := by
    apply others _ (Fin.castSucc_ne_last _).symm
    intro member
    obtain ⟨j,_,eq⟩ := List.mem_map.mp member
    exact Fin.castSucc_ne_last _ eq
  obtain ⟨y,h,G,m,middle,time,user,fanMiddle,fanout,entryOff,off,offM⟩ := run entered v' D retainedTmp fanInput offA
  let added := fun k i => y k (Fin.cast (copyLabel_volume w B K) i)
  have project (X : Fin 142081 → Fin V → ZMod 2) (G : Stacks T prime) (fanMid : fanReady X G) :
      RepT (copyOwners (v := v) X) (embStk (fun i : Fin 142081 => fan (i.castAdd 2)) G).L
        (embStk (fun i : Fin 142081 => fan (i.castAdd 2)) G).R := by
    dsimp only [fanReady] at fanMid
    rw [copyOwners_controls size (flatten X),eq X] at fanMid
    intro j z
    simpa only [Tapes.append,Fin.addCases_left,embStk,Function.comp_apply] using fanMid (j.castAdd 2) z
  have owners : RepT (copyOwners (v := v) added) (embStk owner G).L (embStk owner G).R := by
    intro j z
    simpa only [embStk,Function.comp_apply,sharedB] using project added G fanMiddle j z
  have prepared := copyRoute_ready leave leading b v headers (copyOwners x) (copyOwners added) S G right owners (by
    intro j hj
    obtain ⟨l,r⟩ := off j hj
    obtain ⟨la,ra⟩ := offA _ (apart _ hj)
    exact ⟨l.trans la,r.trans ra⟩)
  obtain ⟨out,z,F,l,last,timeB,userB,done,returned,back,unchanged,offB⟩ :=
    exitRun b fitsB body v w B hw hB rfl pos added h G prepared
  have finalFan := transfer leave leading b sharedB added out G F fanMiddle done (fun j => offB _ (controlsB j))
  have finalEntry := copyRoute_ready enter enterLeading a v headers (copyOwners entered) (copyOwners out) D F loaded
    (by
      intro j z
      simpa only [embStk,Function.comp_apply,shared] using project out F finalFan j z)
    (by
      intro j hj
      obtain ⟨lm,rm⟩ := entryOff j hj
      obtain ⟨lb,rb⟩ := offB _ (apartB _ hj)
      exact ⟨lb.trans lm,rb.trans rm⟩)
  refine ⟨out,z,F,_,Exec.seq first (Exec.seq middle last),by dsimp only [price,V] at *; omega,
    userB.trans (user.trans userA),done,finalEntry,finalFan,copyWindowEffect_of_routes n r d life scheduled w B K x entered out y
      ⟨source,targets,others⟩ fanout ⟨returned,back,unchanged⟩,?_⟩
  intro j hj ha hb
  obtain ⟨la,ra⟩ := offA j ha
  obtain ⟨lm,rm⟩ := offM j hj ha hb
  obtain ⟨lb,rb⟩ := offB j hb
  exact ⟨lb.trans (lm.trans la),rb.trans (rm.trans ra)⟩

private theorem word_of_involutive_scatter {I A J R : Type*} (addr : I ≃ A × J)
    (move : A → A) (invol : Function.Involutive move) (x y : I → R)
    (scatter : ∀ s j, y (addr.symm (move s,j)) = x (addr.symm (s,j))) :
    y = fun i => x (addr.symm (move (addr i).1,(addr i).2)) := by
  funext i
  obtain ⟨⟨s,j⟩,rfl⟩ := addr.symm.surjective i
  simpa only [invol s,Equiv.apply_symm_apply] using scatter (move s) j

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Copy the retained source onto the temporary, run the host conversion once, add the
converted word to the scheduled targets, and clear the temporary for the next window. -/
theorem copyFanout_host (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) :
    let src := ownerTape n r d ⟨life.source,(Copy.source_bounds life scheduled).2⟩
    let tmp := Fin.last 142080
    let regs := life.targets.attach.map fun j =>
      (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
    let targets := regs.map (ownerTape n r d)
    ∃ (q s : ℕ) (load : Program (142081+2) q prime) (finish : Program (142081+2) s prime),
    ∀ {T Q w W : ℕ} {P U : Type} (ports : Fin (142081+2) ↪ Fin T) (fitsLoad : q ≤ Q) (fitsFinish : s ≤ Q)
      (body : P → Pr P T Q prime U) (convert : Pr P T Q prime U) (budget : ℕ) (keep : Fin T → Prop)
      (data : Fin 142081 → Fin ((prime^(w+1))^16*W) → ZMod 2) (hW : 0 < W)
      (u : HS T Q prime U) (S : Stacks T prime),
    let V := (prime^(w+1))^16*W
    let addr := copyAddress (Q := prime^(w+1)) (W := W)
    let move := AffineFieldProgram.run (selectedWord (w+1) (life.sourceFrame,0))
    let common := fun i => data src (addr.symm (move (addr i).1,(addr i).2))
    let bank := fun X => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V)
    let ready := fun X (D : Stacks T prime) => RepT (bank X) (embStk ports D).L (embStk ports D).R
    let outside := fun (D F : Stacks T prime) => ∀ j, (∀ i, ports i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j
    let output := Function.update (fun j i => if j ∈ targets then data j i + common i else data j i) tmp 0
    ready data S →
    (∀ v D, ready (Function.update data tmp (data src)) D → outside S D →
      ∃ z F t y, Exec body convert (mk v D) t (mk z F) ∧ t ≤ budget ∧ z.user = v.user ∧
        ready (Function.update data tmp y) F ∧
        (∀ s j, y (addr.symm (move s,j)) = data src (addr.symm (s,j))) ∧
        ∀ j, keep j → (∀ i, ports i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) →
    ∃ z F t, Exec body ((embProg ports (Empty.elim : Empty → P) (foreign (liftQ load fitsLoad))).seq
        (convert.seq (embProg ports (Empty.elim : Empty → P) (foreign (liftQ finish fitsFinish)))))
      (mk u S) t (mk z F) ∧ t ≤ budget+76*(life.targets.length+2)*V*142088+12 ∧
      z.user = u.user ∧ ready output F ∧
      ∀ j, keep j → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro src tmp regs targets
  let gate : PointwiseRoleGate.Gate 142081 := ⟨src,tmp,Fin.castSucc_ne_last _⟩
  let copy := fun (s _ : Fin (prime+4)) => s
  let erase := fun (_ _ : Fin (prime+4)) => SparseRoleCircuit.encode (a := prime) 0
  obtain ⟨_,adds,addRun⟩ := copyAdds_hoare (a := prime) n r d life scheduled
  refine ⟨_,_,PointwiseRoleGate.program gate copy,seq adds (PointwiseRoleGate.program gate erase),?_⟩
  intro T Q w W P U ports fitsLoad fitsFinish body convert budget keep data hW u S V addr move common bank ready outside output start mid
  have hV : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  let bs := FlatCoordinateSchedule.bits V
  have count := FlatCoordinateSchedule.bits_value V
  have write (X : Fin 142081 → Fin V → ZMod 2) (op : Fin (prime+4) → Fin (prime+4) → Fin (prime+4))
      (value : Fin V → ZMod 2) (action : ∀ i, op (SparseRoleCircuit.encode (X src i))
        (SparseRoleCircuit.encode (X tmp i)) = SparseRoleCircuit.encode (value i)) :
      HoareTime (PointwiseRoleGate.program gate op) (fun w => w = bank X)
        (fun w => w = bank (Function.update X tmp value)) (14*V+14*bs.length+33) := by
    have step := PointwiseRoleGate.gate_hoare gate op (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) bs count
    have eq : PointwiseRoleGate.applyGate gate op (SparseRoleCircuit.encoded X) =
        SparseRoleCircuit.encoded (Function.update X tmp value) := by
      funext j i
      by_cases h : j = tmp
      · subst j
        simpa [PointwiseRoleGate.applyGate,gate,SparseRoleCircuit.encoded] using action i
      · simp [PointwiseRoleGate.applyGate,gate,SparseRoleCircuit.encoded,h]
    rw [eq] at step
    exact step
  obtain ⟨v,D,t,enter,timeA,userA,loaded,off⟩ := placedHoare_exec _ ports fitsLoad body
    (write data copy (data src) (fun _ => rfl)) u S start
  obtain ⟨y,G,m,word,run,time,user,moved,action,offM⟩ := mid v D loaded off
  have same : word = common := word_of_involutive_scatter addr move
    (((copyAddress_word (w+1)).2 life scheduled).2.1) (data src) word action
  subst word
  let X := Function.update data tmp common
  let added := fun j i => if j ∈ targets then X j i + X tmp i else X j i
  have add := addRun X (fun _ _ => blank) (fun _ => 0) bs count
  change HoareTime adds (fun w => w = bank X) (fun w => w = bank added) _ at add
  have finish := add.seq (write added erase 0 (fun _ => rfl))
  have cleaned : Function.update added tmp 0 = output := by
    funext j i
    by_cases eq : j = tmp <;> simp [eq,added,X,output]
  rw [cleaned] at finish
  obtain ⟨z,F,l,leave,timeB,userB,done,offB⟩ := placedHoare_exec _ ports fitsFinish body finish y G moved
  refine ⟨z,F,_,Exec.seq enter (Exec.seq run leave),?_,userB.trans (user.trans userA),done,?_⟩
  · have price := SparseRoleCircuit.cost_linear (life.targets.length+2) V bs count (FlatCoordinateSchedule.bits_canonical V) hV
    have bound := Nat.mul_le_mul_right 142088 price
    simp only [V,Nat.add_mul,Nat.mul_add] at bound timeA timeB ⊢
    omega
  · intro j kept hj
    obtain ⟨l,r⟩ := off j hj
    obtain ⟨lm,rm⟩ := offM j kept hj
    obtain ⟨lb,rb⟩ := offB j hj
    exact ⟨lb.trans (lm.trans l),rb.trans (rm.trans r)⟩

open Cover.Fallback in
/-- Allocate the two basis workspaces after the parent bank. The only tape
shared by either pass and the parent is the chosen payload. -/
theorem phaseBasisPlacement {T : ℕ} (owner : Fin T) (m n : ℕ) :
    let parent := (Fin.castAddEmb (n := T) m).trans (Fin.castAddEmb n)
    ∃ (a : Fin (1+m) ↪ Fin ((T+m)+n)) (b : Fin (1+n) ↪ Fin ((T+m)+n)),
      a ((0 : Fin 1).castAdd m) = parent owner ∧ b ((0 : Fin 1).castAdd n) = parent owner ∧
      (∀ j, j ≠ owner → ∀ k, a k ≠ parent j) ∧
      ∀ j : Fin n, (∀ k, a k ≠ b (j.natAdd 1)) ∧ (∀ k, parent k ≠ b (j.natAdd 1)) := by
  intro parent
  let slot : Fin 1 ↪ Fin T := ⟨fun _ => owner,fun _ _ _ => Subsingleton.elim _ _⟩
  let a := (appendPrivate slot m).trans (Fin.castAddEmb n)
  let b := appendPrivate (slot.trans (Fin.castAddEmb m)) n
  have apart {l r : ℕ} (i : Fin l) (j : Fin r) : i.castAdd r ≠ j.natAdd l := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  refine ⟨a,b,?_,?_,?_,?_⟩
  · exact congrArg (Fin.castAdd n) (appendPrivate_shared slot 0)
  · exact appendPrivate_shared _ _
  · intro j ne k
    apply (Fin.castAddEmb n).injective.ne
    induction k using Fin.addCases with
    | left i => rw [appendPrivate_shared]; exact (Fin.castAddEmb m).injective.ne ne.symm
    | right i => rw [appendPrivate_work]; exact (apart j i).symm
  · intro j
    rw [show b (j.natAdd 1) = j.natAdd (T+m) from appendPrivate_work _ _]
    exact ⟨fun k => apart _ _,fun k => apart _ _⟩

open Cover.Fallback in
/-- Place the record and both basis passes around an existing owner bank. All four
programs meet on the temporary. Every other owner and both fanout controls are separate. -/
theorem copyWorkspacePlacement {t k : ℕ} (record : Fin t) (tmp : Fin k) (m n : ℕ) :
    let T := ((t+(k+2))+m)+n
    ∃ (ports : Fin t ↪ Fin T) (fan : Fin (k+2) ↪ Fin T) (a : Fin (1+m) ↪ Fin T)
      (b : Fin (1+n) ↪ Fin T),
      let slots := (Fin.castAddEmb 2).trans fan
      slots tmp = ports record ∧ a ((0 : Fin 1).castAdd _) = ports record ∧
      b ((0 : Fin 1).castAdd _) = ports record ∧
      (∀ j, ports j ≠ ports record → ∀ l, a l ≠ ports j) ∧
      (∀ j : Fin n, (∀ l, a l ≠ b (j.natAdd 1)) ∧ (∀ l, ports l ≠ b (j.natAdd 1))) ∧
      (∀ j, j ≠ tmp → (∀ l, a l ≠ slots j) ∧ (∀ l, ports l ≠ slots j) ∧ (∀ l, b l ≠ slots j)) ∧
      ∀ j : Fin 2, (∀ l, a l ≠ fan (j.natAdd k)) ∧ (∀ l, ports l ≠ fan (j.natAdd k)) ∧
        (∀ l, b l ≠ fan (j.natAdd k)) := by
  intro T
  let source := tmp.castAdd 2
  let recBank := payloadPlacement record source
  let fanBank := Fin.natAddEmb t (m := k+2)
  let parent := (Fin.castAddEmb (n := t+(k+2)) m).trans (Fin.castAddEmb n)
  have shared : recBank record = fanBank source := payloadPlacement_shared _ _
  obtain ⟨a,b,sa,sb,apart,priv⟩ := phaseBasisPlacement (fanBank source) m n
  refine ⟨recBank.trans parent,fanBank.trans parent,a,b,?_,?_,?_,?_,?_,?_⟩
  · exact congrArg parent shared.symm
  · exact sa.trans (congrArg parent shared.symm)
  · exact sb.trans (congrArg parent shared.symm)
  · intro j ne
    apply apart
    intro eq
    exact ne (congrArg parent (eq.trans shared.symm))
  · intro j
    exact ⟨(priv j).1,fun l => (priv j).2 (recBank l)⟩
  · have away (j : Fin (k+2)) (ne : j ≠ source) :
        (∀ l, a l ≠ parent (fanBank j)) ∧ (∀ l, parent (recBank l) ≠ parent (fanBank j)) ∧
        (∀ l, b l ≠ parent (fanBank j)) := by
      refine ⟨apart _ (fanBank.injective.ne ne),fun l => parent.injective.ne (payloadPlacement_off _ _ j ne l),?_⟩
      intro l
      induction l using Fin.addCases with
      | left l =>
        have eq : l = 0 := Subsingleton.elim _ _
        subst l
        rw [sb]
        exact parent.injective.ne (fanBank.injective.ne ne.symm)
      | right l => exact ((priv l).2 _).symm
    constructor
    · intro j ne
      exact away _ ((Fin.castAdd_injective ..).ne ne)
    · intro j
      apply away
      intro eq
      have h := congrArg Fin.val eq
      change k+j.val = tmp.val at h
      omega

/-- The designated private tapes agree with some initialized machine state. -/
def PrivateStock {T A : ℕ} (used : Fin T → Prop) (initialized : Stacks T A → Prop) (S : Stacks T A) : Prop :=
  ∃ D, initialized D ∧ ∀ j, used j → S.L j = D.L j ∧ S.R j = D.R j

private theorem PrivateStock.frame {T A : ℕ} {used : Fin T → Prop} {initialized : Stacks T A → Prop}
    {S F : Stacks T A} (ready : PrivateStock used initialized S)
    (same : ∀ j, used j → F.L j = S.L j ∧ F.R j = S.R j) : PrivateStock used initialized F := by
  obtain ⟨D,init,stored⟩ := ready
  refine ⟨D,init,?_⟩
  intro j hj
  exact ⟨(same j hj).1.trans (stored j hj).1,(same j hj).2.trans (stored j hj).2⟩

/-- Allocate a finite family of MOVE workspaces. Each local program runs in its
own procedure table and preserves every other workspace's initialization. -/
theorem moveFamily_host {I : Type} [Fintype I] {k : ℕ} (tapes : I → ℕ)
    (ports : ∀ i, Fin k ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin k ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ (used : ∀ i, Fin (tapes i) → Prop) (init : ∀ i, Stacks (tapes i) prime → Prop),
    (∀ i l, used i l → ∀ j, ports i j ≠ l) →
    (∀ i, ∃ S, PrivateStock (used i) (init i) S) →
    let ready := fun S => ∀ i, PrivateStock (used i) (init i) (embStk (bank i) S)
    (∀ X, ∃ S, embStk fan S = X ∧ ready S) ∧
    (∀ S F, ready S → (∀ j, (∀ l, fan l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) → ready F) ∧
    ∀ {P U : Type} {Q : ℕ} (localBody : ∀ i, P → Pr P (tapes i) Q prime U),
    let proc := fun (i : I) (f : P) => (i,f)
    let body := fun f : I × P => embProg (bank f.1) (proc f.1) (localBody f.1 f.2)
    ∀ i code u S z F t, ready S →
      Exec (localBody i) code (mk (embDn (bank i) u) (embStk (bank i) S)) t (mk z F) →
      PrivateStock (used i) (init i) F →
      ∃ v G, Exec body (embProg (bank i) (proc i) code) (mk u S) t (mk v G) ∧
        v.user = z.user ∧ embStk fan G = embStk (ports i) F ∧ ready G := by
  obtain ⟨T,fan,bank,shared,collect,off⟩ := copyWindowBanks tapes ports
  refine ⟨T,fan,bank,shared,?_⟩
  intro used init privatePorts seed ready
  constructor
  · intro X
    choose initial initialized using seed
    obtain ⟨S,base,placed⟩ := collect X initial
    exact ⟨S,base,fun i => PrivateStock.frame (initialized i) (fun l hl => placed i l (privatePorts i l hl))⟩
  constructor
  · intro S F ready same i
    exact PrivateStock.frame (ready i) (fun l hl => same _ ((off i l (privatePorts i l hl)).1))
  intro P U Q localBody proc body i code u S z F t start run done
  obtain ⟨v,G,exec,_,user,localView,frame⟩ := exec_emb (ι := proc i) (body' := body) (bank i).injective
    (fun _ => rfl) run u rfl S rfl
  refine ⟨v,G,exec,user,?_,?_⟩
  · rw [← localView]
    simp only [embStk,Function.comp_def,shared]
  intro j
  by_cases same : j = i
  · subst j
    rwa [localView]
  · exact PrivateStock.frame (start j) (fun l hl => frame _ ((off j l (privatePorts j l hl)).2 i (Ne.symm same)))

open M8.Machine.Segments SharedPlacementAlphabet in
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord) in
open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Pack a live phase record, call the child once, and restore the parent's
digit order. Both basis passes share the payload port with the recursive call. -/
theorem scheduledPhasePacked_host [M8.Machine.Net]
    (p : ℕ × ℕ) (checked : Geometry.Moves.CheckedPair p) (paid : 0 < Geometry.moveRank p.1 p.2) :
    let lo := min (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    let hi := max (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    ∃ (C : Matrix (Fin 8) (Fin 8) ℚ) (rev : CopyBasisPass C.adjugate) (fwd : CopyBasisPass C),
    ∀ {P U : Type} {T Q k : ℕ} (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (body : P → Pr P T Q prime U) (f : P) (capacity : rowSwapBlock.states ≤ Q),
    ∃ setup swaps : ℕ, ∀ (node : Descriptor) (i : Fin nodeChildren5.length) (w B rows : ℕ),
    nodeChildren5[i.val] = Geometry.moveRank p.1 p.2 → node.width = 64*(w+1) →
    node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    0 < W →
    let desc := scheduledChild prime node i
    ∃ position : Fin (volume prime desc) ≃ Fin (M^16*W),
    (∀ k, (position k).val = (CopyChildLayout.packActive desc k).val) ∧
    let is := phasePackSchedule lo hi
    let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
    let clean := fun D : Stacks T prime => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []
    let pack := fun js => statePlacedNormalized ports capacity swapStates_pos Empty.elim (packSchedule 16 js)
    let middle := (pack is).seq ((Prog.call f).seq (pack is.reverse))
    let V := M^16*W
    let view := phaseIntervalChild lo hi (w+1) W
    let size := phaseIntervalChild_volume (phaseInterval_bounds checked paid).1.le (phaseInterval_bounds checked paid).2 (w+1) W
    let word := fun y : Fin V → ZMod 2 => sourceWord (v := view) (fun k => y (k.cast size))
    let caller := fun y => (⟨fun _ => 0,fun _ => word y⟩ : Tapes 1 prime)
    let input := fun stages y => (caller y).append (basisWorkspace stages y)
    let A := description _ rev.good
    let B := description _ fwd.good
    let machine := fun stages => Placement.placed (FlatCoordinateCleanSchedule.program stages)
      (sharedPlacement (0 : Fin 1) (segmentSource stages))
    let basisRate := fun stages => FlatCoordinateCleanSchedule.constant stages*(1+FlatCoordinateCleanSchedule.tapeCount stages+5)
    ∀ (a : Fin (1+FlatCoordinateCleanSchedule.tapeCount A) ↪ Fin T)
      (b : Fin (1+FlatCoordinateCleanSchedule.tapeCount B) ↪ Fin T) (fitsA : _ ≤ Q) (fitsB : _ ≤ Q),
    a ((0 : Fin 1).castAdd _) = bank 24 → b ((0 : Fin 1).castAdd _) = bank 24 →
    (∀ j, ports j ≠ bank 24 → ∀ k, a k ≠ ports j) →
    (∀ j : Fin (FlatCoordinateCleanSchedule.tapeCount B), (∀ k, a k ≠ b (j.natAdd 1)) ∧ (∀ k, ports k ≠ b (j.natAdd 1))) →
    ∀ (fan : Fin (k+2) ↪ Fin T) (src : Fin k),
    let slots := (Fin.castAddEmb 2).trans fan
    slots src = bank 24 →
    (∀ j, j ≠ src → (∀ l, a l ≠ slots j) ∧ (∀ l, ports l ≠ slots j) ∧ (∀ l, b l ≠ slots j)) →
    (∀ i : Fin 2, (∀ l, a l ≠ fan (i.natAdd k)) ∧ (∀ l, ports l ≠ fan (i.natAdd k)) ∧
      (∀ l, b l ≠ fan (i.natAdd k))) →
    let live := fun X (D : Stacks T prime) => RepT (PointwiseRoleGate.bank (a := prime)
      (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V))
      (embStk fan D).L (embStk fan D).R
    ∀ record dest q budget,
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
      SparseRoleCircuit.encode (fun _ => blank) dest 0 q
    let keep := fun j => (∀ l, a l ≠ j) ∧ (∀ l, ports l ≠ j) ∧ (∀ l, b l ≠ j)
    let stock := PrivateStock (fun j => j ≠ bank 24 ∧ ¬ keep j) (fun prepared => ∃ old,
      RepT (input A old) (embStk a prepared).L (embStk a prepared).R ∧
      RepT (input B old) (embStk b prepared).L (embStk b prepared).R ∧ stored old prepared ∧ clean prepared)
    (desc.width < node.width → ∀ (u : HS T Q prime U) D word, stored word D → clean D →
      ∃ z F n changed, Exec body (body f) (mk u D) n (mk z F) ∧ n ≤ budget ∧ z.user = u.user ∧
        stored changed F ∧ clean F ∧ (∀ j, (∀ i, ports i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
        ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (word ∘ position) k) →
    ∀ (data : Fin k → Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime), live data S → stock S →
    ∃ y z G n, Exec body
        ((embProg a (Empty.elim : Empty → P) (foreign (liftQ (machine A) fitsA))).seq
          (middle.seq (embProg b (Empty.elim : Empty → P) (foreign (liftQ (machine B) fitsB)))))
        (mk u S) n (mk z G) ∧ n ≤ budget+(basisRate A+basisRate B+setup+16+swaps*swapVolumeRate w)*V ∧
      z.user = u.user ∧ live (Function.update data src y) G ∧ stock G ∧
      (∀ j, (∀ k, a k ≠ j) → (∀ k, ports k ≠ j) → (∀ k, b k ≠ j) → G.L j = S.L j ∧ G.R j = S.R j) ∧
      ∀ s j, y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) p) s)) j) =
        data src (index (AffineFieldCoordinates.embed s) j) := by
  intro lo hi
  obtain ⟨C,shape,rev,fwd⟩ := modular_move_profile.choose_spec.1 p checked
  refine ⟨C,rev,fwd,?_⟩
  intro P U T Q k ports body f capacity
  obtain ⟨setup,swaps,prepare⟩ := phasePackedCall_exec capacity p checked paid ports body f
  refine ⟨setup,swaps,?_⟩
  intro node i w B rows rank width split label M K W hW desc
  obtain ⟨position,offset,route⟩ := prepare node i w B rows rank width split label hW
  refine ⟨position,offset,?_⟩
  intro is bank clean pack middle V view size word caller input
  intro A B' machine basisRate a b fitsA fitsB srcA srcB apart priv fan src slots shared outside controlsOff live record dest q budget stored keep stock child data u S initialLive
  rintro ⟨prepared,⟨old,initialA,initialB,initialRecord,initialClean⟩,kept⟩
  let x := data src
  have slot (j : Fin k) : slots j = fan (j.castAdd 2) := by apply congrArg fan; apply Fin.ext; rfl
  have enc (Y : Fin k → Fin V → ZMod 2) (i : Fin k) : SparseRoleCircuit.encoded (a := prime) Y i =
      fun j => SparseRoleCircuit.encode (Y i j) := rfl
  have initial : RepT (phaseOwners data) (embStk slots S).L (embStk slots S).R := by
    intro i j
    simpa only [phaseOwners,embStk,Function.comp_apply,slot,PointwiseRoleGate.bank,Tapes.append,
      Fin.addCases_left,enc] using initialLive (i.castAdd 2) j
  have portKeep (k) (ne : ports k ≠ bank 24) := kept _ ⟨ne,fun h => h.2.1 k rfl⟩
  have cell (j : ℤ) : putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (x i)) j =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) j := by
    simpa only [phaseOwners,x,embStk,Function.comp_apply,shared,sub_zero] using initial src j
  have encoded (j : ℤ) := encodedOwnerCell x j
  simp only [List.map_ofFn] at encoded
  have start : stored x S := initialRecord.returnPayload
    (fun k ne => portKeep _ (bank.injective.ne ne)) (fun j => by
      simpa only [sub_zero] using (encoded j).trans (cell j))
  have free : clean S := by
    intro k hk
    have ne : ports k ≠ bank 24 := ports.injective.ne (fun eq => by
      have v := congrArg Fin.val eq; change k.val = 24 at v; omega)
    obtain ⟨l,r⟩ := portKeep k ne
    exact ⟨l.trans (initialClean k hk).1,r.trans (initialClean k hk).2⟩
  have basis (stages : List (FlatCoordinateSchedule.Op 16))
      (e : Fin (1+FlatCoordinateCleanSchedule.tapeCount stages) ↪ Fin T)
      (site : e ((0 : Fin 1).castAdd _) = bank 24) (uses : ∀ k, ¬ keep (e k))
      (prior : RepT (input stages old) (embStk e prepared).L (embStk e prepared).R) :
      RepT (input stages x) (embStk e S).L (embStk e S).R := by
    intro k j
    induction k using Fin.addCases with
    | left k =>
      have eq : k = 0 := Subsingleton.elim _ _
      subst k
      simp only [input,caller,Tapes.append,Fin.addCases_left,sub_zero,embStk,Function.comp_apply,site]
      dsimp only [word]
      rw [swap_source_word]
      apply Eq.trans _ ((encoded j).trans (cell j))
      congr 2
      exact List.ofFn_congr (phaseIntervalChild_volume (phaseInterval_bounds checked paid).1.le
        (phaseInterval_bounds checked paid).2 (w+1) W) _
    | right k =>
      have ne : e (k.natAdd 1) ≠ bank 24 := by
        rw [← site]
        apply e.injective.ne
        intro eq
        have h := congrArg Fin.val eq
        simp only [Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero] at h
        omega
      obtain ⟨l,r⟩ := kept _ ⟨ne,uses _⟩
      simpa only [input,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,l,r,
        basisWorkspace_eq stages x old] using prior (k.natAdd 1) j
  have readyA := basis A a srcA (fun k h => h.1 k rfl) initialA
  have readyB := basis B' b srcB (fun k h => h.2.2 k rfl) initialB
  obtain ⟨loaded,first,enter⟩ := phaseBasis_host view size _ rev.good hW (rev.legal _) x
  obtain ⟨v,F,t,runA,timeA,userA,full,_,offA⟩ := enter a fitsA body u S readyA
  have encoded (payload : Fin V → ZMod 2) (z : ℤ) : word payload z =
      RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ payload)) z) := by
    dsimp only [word]
    rw [swap_source_word]
    congr 2
    exact List.ofFn_congr size _
  have ready : stored loaded F := start.returnPayload (fun k ne => offA (bank k)
    (apart _ (bank.injective.ne ne))) (by
      intro z
      have cell := full ((0 : Fin 1).castAdd _) z
      simp only [Tapes.append,Fin.addCases_left,setTape,Function.update_self,sub_zero] at cell
      change word loaded z = readAt blank (F.L (a _)) (F.R (a _)) z at cell
      rw [← srcA]
      simpa only [encoded,sub_zero] using cell)
  have clear : clean F := by
    intro k hk
    have ne : ports k ≠ bank 24 := ports.injective.ne (fun eq => by have := congrArg Fin.val eq; change k.val = 24 at this; omega)
    obtain ⟨l,r⟩ := offA _ (apart _ ne)
    exact ⟨l.trans (free k hk).1,r.trans (free k hk).2⟩
  obtain ⟨h,D,m,userM,timeM,exec,returned,freeM,offM⟩ := route v F record dest q loaded budget child ready clear
  let mid := fun k => Shared50RecursiveNodeRows.transpose (v := view) (one_dvd _) (fun j => loaded (j.cast size)) (Fin.cast size.symm k)
  have next : RepT (input B' mid) (embStk b D).L (embStk b D).R := by
    intro k z
    induction k using Fin.addCases with
    | left k =>
      have eq : k = 0 := Subsingleton.elim _ _
      subst k
      simpa only [input,caller,Tapes.append,Fin.addCases_left,sub_zero,embStk,Function.comp_apply,srcB,encoded]
        using (show word mid z = readAt blank (D.L (b ((0 : Fin 1).castAdd _))) (D.R (b ((0 : Fin 1).castAdd _))) z from by
          rw [srcB,encoded]; simpa only [sub_zero] using (returned.src z).symm)
    | right k =>
      obtain ⟨la,ra⟩ := offA _ (priv k).1
      obtain ⟨lm,rm⟩ := offM _ (priv k).2
      have cell := readyB (k.natAdd 1) z
      simp only [input,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply] at cell ⊢
      rw [basisWorkspace_eq B' mid x,lm,rm,la,ra]
      exact cell
  obtain ⟨y,last,leave⟩ := phaseBasis_host view size _ fwd.good hW (fwd.legal _) mid
  obtain ⟨z,G,n,runB,timeB,userB,done,_,offB⟩ := leave b fitsB body h D next
  have backOff (k) (ne : ports k ≠ bank 24) : G.L (ports k) = D.L (ports k) ∧ G.R (ports k) = D.R (ports k) := by
    apply offB
    intro j
    induction j using Fin.addCases with
    | left j =>
      have eq : j = 0 := Subsingleton.elim _ _
      subst j
      exact srcB ▸ ne.symm
    | right j => exact fun h => (priv j).2 k h.symm
  have finalRecord : stored y G := returned.returnPayload (fun k ne => backOff _ (bank.injective.ne ne)) (by
    intro k
    have cell := done ((0 : Fin 1).castAdd _) k
    simp only [Tapes.append,Fin.addCases_left,setTape,Function.update_self,sub_zero] at cell
    change word y k = readAt blank (G.L (b _)) (G.R (b _)) k at cell
    rw [← srcB]
    simpa only [encoded,sub_zero] using cell)
  have untouched (j) (ha : ∀ k, a k ≠ j) (hm : ∀ k, ports k ≠ j) (hb : ∀ k, b k ≠ j) :
      G.L j = S.L j ∧ G.R j = S.R j := by
    obtain ⟨l,r⟩ := offA j ha
    obtain ⟨l',r'⟩ := offM j hm
    obtain ⟨l'',r''⟩ := offB j hb
    exact ⟨l''.trans (l'.trans l),r''.trans (r'.trans r)⟩
  have owners : RepT (phaseOwners (Function.update data src y)) (embStk slots G).L (embStk slots G).R := by
    apply owners_of_returned_record slots src bank shared data y initial finalRecord
    intro i eq
    obtain ⟨ha,hm,hb⟩ := outside i eq
    exact untouched (slots i) ha hm hb
  have readyForward : RepT (input B' y) (embStk b G).L (embStk b G).R := by
    intro k z
    induction k using Fin.addCases with
    | left k =>
      obtain rfl : k = 0 := Subsingleton.elim _ _
      simpa only [input,caller,Tapes.append,Fin.addCases_left,setTape,Function.update_self,sub_zero] using done ((0 : Fin 1).castAdd _) z
    | right k =>
      simp only [input,Tapes.append,Fin.addCases_right]
      rw [basisWorkspace_eq B' y mid]
      simpa only [Tapes.append,Fin.addCases_right] using done (k.natAdd 1) z
  have readyReverse : RepT (input A y) (embStk a G).L (embStk a G).R := by
    intro k z
    induction k using Fin.addCases with
    | left k =>
      obtain rfl : k = 0 := Subsingleton.elim _ _
      simpa only [input,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,srcA,srcB] using readyForward ((0 : Fin 1).castAdd _) z
    | right k =>
      let j := k.natAdd 1
      have ne : a j ≠ bank 24 := by
        rw [← srcA]
        apply a.injective.ne
        intro eq
        have h := congrArg Fin.val eq
        simp [j] at h
      have offPorts : ∀ i, ports i ≠ a j := by
        intro i eq
        exact apart i (eq ▸ ne) j eq.symm
      have offForward : ∀ i, b i ≠ a j := by
        intro i
        induction i using Fin.addCases with
        | left i =>
          obtain rfl : i = 0 := Subsingleton.elim _ _
          exact srcB ▸ ne.symm
        | right i => exact ((priv i).1 j).symm
      obtain ⟨l,r⟩ := offM _ offPorts
      obtain ⟨l',r'⟩ := offB _ offForward
      simp only [input,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply]
      change _ = readAt blank (G.L (a j)) (G.R (a j)) _
      rw [l',r',l,r,basisWorkspace_eq A y x]
      simpa only [Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,j] using full (k.natAdd 1) z
  have result : live (Function.update data src y) G := by
    intro i j
    induction i using Fin.addCases with
    | left i =>
      simpa only [phaseOwners,embStk,Function.comp_apply,slot,PointwiseRoleGate.bank,Tapes.append,
        Fin.addCases_left,enc] using owners i j
    | right i =>
      obtain ⟨ha,hp,hb⟩ := controlsOff i
      obtain ⟨l,r⟩ := untouched _ ha hp hb
      simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,l,r]
        using initialLive (i.natAdd k) j
  refine ⟨y,z,G,_,Exec.seq runA (Exec.seq exec runB),?_,userB.trans (userM.trans userA),result,⟨G,⟨y,readyReverse,readyForward,finalRecord,?_⟩,fun _ _ => ⟨rfl,rfl⟩⟩,untouched,?_⟩
  · change t ≤ FlatCoordinateCleanSchedule.constant A*V*(1+FlatCoordinateCleanSchedule.tapeCount A+5)+6 at timeA
    change n ≤ FlatCoordinateCleanSchedule.constant B'*V*(1+FlatCoordinateCleanSchedule.tapeCount B'+5)+6 at timeB
    change m ≤ budget+4+(setup+swaps*swapVolumeRate w)*V at timeM
    have pos : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
    rw [Nat.mul_right_comm] at timeA timeB
    dsimp only [basisRate]
    simp only [Nat.add_mul] at timeM ⊢
    omega
  · intro k hk
    have ne : ports k ≠ bank 24 := ports.injective.ne (fun eq => by have := congrArg Fin.val eq; change k.val = 24 at this; omega)
    obtain ⟨l,r⟩ := backOff k ne
    exact ⟨l.trans (freeM k hk).1,r.trans (freeM k hk).2⟩
  · intro s j
    unfold selectedWord selectedRaw
    rw [shape,rationalMoveWord_run,last]
    exact (phaseChild_interval (phaseInterval_bounds checked paid).1.le (phaseInterval_bounds checked paid).2 loaded _ j).trans (first s j)

private theorem disjointStackBanks {t m n T a : ℕ} (p : Fin t ↪ Fin T) (q : Fin m ↪ Fin T) (r : Fin n ↪ Fin T)
    (pq : ∀ i j, p i ≠ q j) (pr : ∀ i j, p i ≠ r j) (qr : ∀ i j, q i ≠ r j)
    (X : Stacks t a) (Y : Stacks m a) (Z : Stacks n a) :
    ∃ D : Stacks T a, (∀ i, D.L (p i) = X.L i ∧ D.R (p i) = X.R i) ∧
      (∀ j, D.L (q j) = Y.L j ∧ D.R (q j) = Y.R j) ∧ (∀ j, D.L (r j) = Z.L j ∧ D.R (r j) = Z.R j) := by
  let all := fun {β : Type} (x : Fin t → β) (y : Fin m → β) (z : Fin n → β) (empty : β) =>
    embExt p x (embExt q y (embExt r z (fun _ => empty)))
  refine ⟨⟨[],[],all X.L Y.L Z.L [],all X.R Y.R Z.R []⟩,?_,?_,?_⟩
  · intro i
    simp [all,embExt_apply p.injective]
  · intro j
    simp [all,embExt_off _ _ (fun i => pq i j),embExt_apply q.injective]
  · intro j
    simp [all,embExt_off _ _ (fun i => pr i j),embExt_off _ _ (fun i => qr i j),embExt_apply r.injective]

open Cover.Fallback SharedPlacementAlphabet in
/-- Concrete host stacks for a basis pass, with the payload kept on the caller's tape. -/
private theorem basisWorkspaceStacks {w W : ℕ} (stages : List (FlatCoordinateSchedule.Op 16))
    (x : Fin ((prime^w)^16*W) → ZMod 2) :
    ∃ S : Stacks (FlatCoordinateCleanSchedule.tapeCount stages) prime, RepT (basisWorkspace (w := w) (W := W) stages x) S.L S.R := by
  classical
  let bits := fun i => SparseRoleCircuit.encode (a := 0) (x i)
  let common := FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W) bits
  have four (i : Fin 4) : ∃ L R, ∀ z, common.tape i z = readAt blank L R (z-common.head i) := by
    change Fin (2+2) at i
    induction i using Fin.addCases with
    | left i =>
      simp only [common,FlatCoordinateShiftSharedBank.common,Tapes.append,Fin.addCases_left]
      fin_cases i
      · refine ⟨[],payloadWord bits,fun z => ?_⟩
        change M8.AtomBank.arrTape bits z = readAt blank [] _ (z-0)
        simpa only [sub_zero] using payload_reads bits z
      · refine ⟨[],[],fun z => ?_⟩
        change blank = readAt blank [] [] (z-0)
        simp [readAt_nil_left,wordTape_nil]
    | right i =>
      simp only [common,FlatCoordinateShiftSharedBank.common,Tapes.append,Fin.addCases_right]
      have header (bs : List Bool) (z : ℤ) : RadixZeroFill.encodedBinary (q := prime) bs z =
          readAt blank [separator] (bs.map bitSymbol) (z-1) := by rw [encodedBinary_eq,readAt_single]
      fin_cases i
      · exact ⟨_,_,header (FlatCoordinateSchedule.bits w)⟩
      · exact ⟨_,_,header (FlatCoordinateSchedule.bits W)⟩
  have tape (i : Fin (FlatCoordinateCleanSchedule.tapeCount stages)) :
      ∃ L R, ∀ z, (basisWorkspace (w := w) (W := W) stages x).tape i z = readAt blank L R (z-(basisWorkspace (w := w) (W := W) stages x).head i) := by
    by_cases src : i = segmentSource stages
    · exact ⟨[],[],fun z => by simp [basisWorkspace,setTape,src,readAt_nil_left,wordTape_nil]⟩
    · by_cases h : i.val < 4
      · simp only [basisWorkspace,setTape,Function.update_of_ne src,SharedBankStageInput.raw,dite_eq_left h]
        exact four ⟨i.val,h⟩
      · exact ⟨[],[],fun z => by simp [basisWorkspace,setTape,Function.update_of_ne src,SharedBankStageInput.raw,h,
          readAt_nil_left,wordTape_nil]⟩
  choose L R rep using tape
  exact ⟨⟨[],[],L,R⟩,rep⟩

open M8.RevMachine RecursiveInterchangeLayout SharedPlacementAlphabet Cover.Fallback in
theorem copyChartStacks (v : Descriptor) (d : Fin 22 → Option (List Bool)) (k t : ℕ) :
    let common := LabelCall.bank (copyOwners (T := k) (v := v) 0) v d
    ∃ S : Stacks t prime, RepT (SharedBankStageInput.raw common t) S.L S.R := by
  intro common
  have binary (bs : List Bool) (z : ℤ) : RadixZeroFill.encodedBinary (q := prime) bs z =
      readAt blank [separator] (bs.map bitSymbol) (z-1) := by rw [encodedBinary_eq,readAt_single]
  have represented (i : Fin (k+24)) : ∃ L R, ∀ z, common.tape i z = readAt blank L R (z-common.head i) := by
    induction i using Fin.addCases with
    | left i =>
      let bits := fun _ : Fin (volume prime v) => SparseRoleCircuit.encode (a := 0) (0 : ZMod 2)
      refine ⟨[],payloadWord bits,fun z => ?_⟩
      simp only [common,LabelCall.bank,Tapes.append,Fin.addCases_left,copyOwners,sub_zero,swap_source_word]
      exact payload_reads bits z
    | right i =>
      change Fin (2+22) at i
      induction i using Fin.addCases with
      | left j =>
        simp only [common,LabelCall.bank,Tapes.append,Fin.addCases_right,Fin.addCases_left]
        exact ⟨_,_,binary (![Routines.hdr v 0,Routines.hdr v 1] j)⟩
      | right j =>
        simp only [common,LabelCall.bank,Tapes.append,Fin.addCases_right,Headers.bank]
        cases h : d j with
        | none => exact ⟨[],[],fun z => by simp [CounterDimensions.descriptorTape,CounterDimensions.descriptorHead,readAt_nil_left,wordTape_nil]⟩
        | some bs => exact ⟨_,_,binary bs⟩
  have raw (i : Fin t) : ∃ L R, ∀ z, (SharedBankStageInput.raw common t).tape i z =
      readAt blank L R (z-(SharedBankStageInput.raw common t).head i) := by
    by_cases inside : i.val < k+24
    · simpa only [SharedBankStageInput.raw,dif_pos inside] using represented ⟨i.val,inside⟩
    · exact ⟨[],[],fun z => by simp [SharedBankStageInput.raw,inside,readAt_nil_left,wordTape_nil]⟩
  choose L R reads using raw
  exact ⟨⟨[],[],L,R⟩,reads⟩

open Cover.Fallback in
private theorem moveRecordStacks [M8.Machine.Net] {w W : ℕ} (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (destL destR : List (Fin (prime+4)))
    (readDest : ∀ z, readAt blank destL destR (z-q) = RadixToBinary.binaryEncoding.encode (dest z)) :
    let M := prime^(w+1)
    let bank := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    ∃ S : Stacks (rowSwapBlock.tapes+35) prime,
      RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record SparseRoleCircuit.encode
        (fun _ => blank) dest 0 q (fun _ => 0) S ∧
      ∀ l : Fin (rowSwapBlock.tapes+35), 35 ≤ l.val → S.L l = [] ∧ S.R l = [] := by
  intro M bank
  let bits := fun _ : Fin (M^16*W) => SparseRoleCircuit.encode (a := 0) (0 : ZMod 2)
  let left := fun l : Fin (rowSwapBlock.tapes+35) => if l.val = 25 then destL else []
  let right := fun l : Fin (rowSwapBlock.tapes+35) =>
    if l.val = 2 then binSyms M.size M else if l.val = 24 then payloadWord bits else
    if l.val = 25 then destR else if l.val = 27 then binSyms W.size W else if l.val = 28 then binSyms 1 1 else
    if l.val = 32 then binSyms M.size (1 : ZMod M).val else if l.val = 33 then List.replicate w blank else
    if l.val = 34 then record else []
  refine ⟨⟨[],[],left,right⟩,⟨rfl,rfl,rfl,rfl,by change (List.replicate w _).length = w; simp,rfl,?_,?_,?_⟩,?_⟩
  · intro i hi
    have v : (bank i).val = i.val := rfl
    have outside : ∀ j ∈ shearWork, j.val ≠ 2 ∧ j.val ≠ 24 ∧ j.val ≠ 25 ∧ j.val ≠ 27 ∧ j.val ≠ 28 ∧
        j.val ≠ 32 ∧ j.val ≠ 33 ∧ j.val ≠ 34 := by decide +kernel
    obtain ⟨h₂,h₂₄,h₂₅,h₂₇,h₂₈,h₃₂,h₃₃,h₃₄⟩ := outside i hi
    simp [left,right,v,h₂,h₂₄,h₂₅,h₂₇,h₂₈,h₃₂,h₃₃,h₃₄]
  · intro z
    change readAt blank [] (payloadWord bits) (z-0) = _
    rw [sub_zero]
    exact (payload_reads bits z).symm
  · exact readDest
  · intro i hi
    simp [left,right,show ∀ n < 35, i.val ≠ n by omega]

open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord) in
open Cover.Fallback RecursiveInterchangeLayout in
private theorem basisRecordSeed [M8.Machine.Net] {w W T : ℕ}
    (A B' : List (FlatCoordinateSchedule.Op 16)) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (a : Fin (1+FlatCoordinateCleanSchedule.tapeCount A) ↪ Fin T)
    (b : Fin (1+FlatCoordinateCleanSchedule.tapeCount B') ↪ Fin T) :
    let recordPort : Fin (rowSwapBlock.tapes+35) := (Fin.castLEEmb swapHostFits) ((Fin.castLEEmb (by decide : 35 ≤ 59)) 24)
    a ((0 : Fin 1).castAdd _) = ports recordPort → b ((0 : Fin 1).castAdd _) = ports recordPort →
    (∀ j, ports j ≠ ports recordPort → ∀ l, a l ≠ ports j) →
    (∀ j : Fin (FlatCoordinateCleanSchedule.tapeCount B'), (∀ l, a l ≠ b (j.natAdd 1)) ∧ (∀ l, ports l ≠ b (j.natAdd 1))) →
    ∀ (view : Descriptor) (size : volume prime view = (prime^(w+1))^16*W) record dest q (L R : List (Fin (prime+4))),
    (∀ z, readAt blank L R (z-q) = RadixToBinary.binaryEncoding.encode (dest z)) →
    let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
    let M := prime^(w+1)
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
    let input := fun stages (y : Fin (M^16*W) → ZMod 2) =>
      (⟨fun _ => 0,fun _ => sourceWord (v := view) (fun k => y (k.cast size))⟩ : Tapes 1 prime).append (basisWorkspace stages y)
    ∃ D : Stacks T prime, RepT (input A 0) (embStk a D).L (embStk a D).R ∧
      RepT (input B' 0) (embStk b D).L (embStk b D).R ∧ stored 0 D ∧
      ∀ l : Fin (rowSwapBlock.tapes+35), 35 ≤ l.val → D.L (ports l) = [] ∧ D.R (ports l) = [] := by
  intro recordPort srcA srcB apart privateB view size record dest q L R readDest bank M stored input
  obtain ⟨X,recX,freeX⟩ := moveRecordStacks (w := w) (W := W) record dest q L R readDest
  obtain ⟨Y,repY⟩ := basisWorkspaceStacks (w := w+1) (W := W) A 0
  obtain ⟨Z,repZ⟩ := basisWorkspaceStacks (w := w+1) (W := W) B' 0
  let pa := (Fin.natAddEmb 1).trans a
  let pb := (Fin.natAddEmb 1).trans b
  have paOff (i j) : ports i ≠ pa j := by
    by_cases eq : ports i = ports recordPort
    · rw [eq,← srcA]
      exact a.injective.ne (by intro h; have := congrArg Fin.val h; simp [pa] at this; omega)
    · exact (apart i eq _).symm
  obtain ⟨D,placed,reverseBank,forwardBank⟩ := disjointStackBanks ports pa pb paOff
    (fun i j => (privateB j).2 i) (fun i j => (privateB j).1 _) X Y Z
  have recordRead : stored 0 D := by
    let localBank := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    have same (j : Fin 35) : D.L (bank j) = X.L (localBank j) ∧ D.R (bank j) = X.R (localBank j) := placed _
    exact ⟨(same 2).2.trans recX.modulus,(same 27).2.trans recX.width,(same 28).2.trans recX.one,
      (same 32).2.trans recX.padded,(congrArg List.length (same 33).2).trans recX.clock,(same 34).2.trans recX.archive,
      fun j hj => ⟨(same j).1.trans (recX.scratch j hj).1,(same j).2.trans (recX.scratch j hj).2⟩,
      fun z => by rw [(same 24).1,(same 24).2]; exact recX.src z,
      fun z => by rw [(same 25).1,(same 25).2]; exact recX.dst z⟩
  have basis (stages : List (FlatCoordinateSchedule.Op 16)) (e : Fin (1+FlatCoordinateCleanSchedule.tapeCount stages) ↪ Fin _)
      (site : e ((0 : Fin 1).castAdd _) = ports recordPort) (Y : Stacks _ prime)
      (rep : RepT (basisWorkspace (w := w+1) (W := W) stages 0) Y.L Y.R)
      (onBank : ∀ j, D.L (e (j.natAdd 1)) = Y.L j ∧ D.R (e (j.natAdd 1)) = Y.R j) :
      RepT (input stages 0) (embStk e D).L (embStk e D).R := by
    intro j z
    induction j using Fin.addCases with
    | left j =>
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp only [input,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,site,swap_source_word]
      apply Eq.trans _ (recordRead.src z).symm
      congr 2
      exact List.ofFn_congr size _
    | right j =>
      simpa only [input,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,(onBank j).1,(onBank j).2] using rep j z
  refine ⟨D,basis A a srcA Y repY reverseBank,basis B' b srcB Z repZ forwardBank,recordRead,?_⟩
  intro l hl
  exact ⟨(placed l).1.trans (freeX l hl).1,(placed l).2.trans (freeX l hl).2⟩

open M8.Machine.Segments SharedPlacementAlphabet in
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord) in
open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Allocate one scheduled MOVE around its selected owner. The local table only
has to execute the transpose at the strictly smaller child descriptor. -/
theorem allocatedPhaseMove_host [M8.Machine.Net] {k : ℕ} (src : Fin k)
    (p : ℕ × ℕ) (checked : Geometry.Moves.CheckedPair p) (paid : 0 < Geometry.moveRank p.1 p.2) :
    ∃ (A B' : List (FlatCoordinateSchedule.Op 16)) (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (fan : Fin (k+2) ↪ Fin T)
      (a : Fin (1+FlatCoordinateCleanSchedule.tapeCount A) ↪ Fin T)
      (b : Fin (1+FlatCoordinateCleanSchedule.tapeCount B') ↪ Fin T),
    let payload := ports ((Fin.castLEEmb swapHostFits) ((Fin.castLEEmb (by decide : 35 ≤ 59)) 24))
    let privateSlot := fun j => j ≠ payload ∧ ¬ ((∀ l, a l ≠ j) ∧ (∀ l, ports l ≠ j) ∧ (∀ l, b l ≠ j))
    (∀ j, privateSlot j → ∀ l, fan l ≠ j) ∧ fan (src.castAdd 2) = payload ∧ a ((0 : Fin 1).castAdd _) = payload ∧ b ((0 : Fin 1).castAdd _) = payload ∧
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : P → Pr P T Q prime U) (f : P),
    ∃ base swaps : ℕ, ∀ (node : Descriptor) (i : Fin nodeChildren5.length) (w B rows : ℕ),
    nodeChildren5[i.val] = Geometry.moveRank p.1 p.2 → node.width = 64*(w+1) →
    node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W → ∀ record dest q,
    let desc := scheduledChild prime node i
    let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
      SparseRoleCircuit.encode (fun _ => blank) dest 0 q
    let clean := fun D : Stacks T prime => ∀ l : Fin (rowSwapBlock.tapes+35), 35 ≤ l.val → D.L (ports l) = [] ∧ D.R (ports l) = []
    let live := fun (X : Fin k → Fin V → ZMod 2) (D : Stacks T prime) => RepT (PointwiseRoleGate.bank (a := prime)
      (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V))
      (embStk fan D).L (embStk fan D).R
    ∃ (position : Fin (volume prime desc) ≃ Fin V), (∀ h, (position h).val = (CopyChildLayout.packActive desc h).val) ∧
    let lo := min (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    let hi := max (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    let view := phaseIntervalChild lo hi (w+1) W
    let size := phaseIntervalChild_volume (phaseInterval_bounds checked paid).1.le (phaseInterval_bounds checked paid).2 (w+1) W
    let input := fun stages (x : Fin V → ZMod 2) =>
      (⟨fun _ => 0,fun _ => sourceWord (v := view) (fun j => x (j.cast size))⟩ : Tapes 1 prime).append (basisWorkspace stages x)
    let stock := PrivateStock privateSlot
      (fun D => ∃ old, RepT (input A old) (embStk a D).L (embStk a D).R ∧
        RepT (input B' old) (embStk b D).L (embStk b D).R ∧ stored old D ∧ clean D)
    (∀ (owners : Stacks (k+2) prime) (L R : List (Fin (prime+4))), (∀ z, readAt blank L R (z-q) = RadixToBinary.binaryEncoding.encode (dest z)) →
      ∃ seed, embStk fan seed = owners ∧ stock seed) ∧
    ∃ code : Pr P T Q prime U, ∀ budget,
    (desc.width < node.width → ∀ u D word, stored word D → clean D →
      ∃ z F n changed, Exec body (body f) (mk u D) n (mk z F) ∧ n ≤ budget ∧ z.user = u.user ∧
        stored changed F ∧ clean F ∧ (∀ j, (∀ l, ports l ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
        ∀ h : Fin (volume prime desc), changed (position h) =
          Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (word ∘ position) h) →
    ∀ data u S, live data S → stock S → ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧
      t ≤ budget+(base+swaps*swapVolumeRate w)*V ∧ z.user = u.user ∧ live (Function.update data src y) F ∧
      stock F ∧ ∀ s (j : Fin W), y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) p) s)) j) =
        data src (index (AffineFieldCoordinates.embed s) j) := by
  obtain ⟨C,rev,fwd,build⟩ := scheduledPhasePacked_host p checked paid
  let A := description _ rev.good
  let B' := description _ fwd.good
  let recordPort : Fin (rowSwapBlock.tapes+35) := (Fin.castLEEmb swapHostFits) ((Fin.castLEEmb (by decide : 35 ≤ 59)) 24)
  obtain ⟨ports,fan,a,b,shared,srcA,srcB,apart,privateB,ownersOff,controlsOff⟩ :=
    copyWorkspacePlacement recordPort src (FlatCoordinateCleanSchedule.tapeCount A) (FlatCoordinateCleanSchedule.tapeCount B')
  let statesOf {t q : ℕ} (_ : Program t q prime) := q
  let qa := statesOf (FlatCoordinateCleanSchedule.program A)
  let qb := statesOf (FlatCoordinateCleanSchedule.program B')
  have disjoint (j) (hj : j ≠ ports recordPort ∧ ¬ ((∀ l, a l ≠ j) ∧ (∀ l, ports l ≠ j) ∧ (∀ l, b l ≠ j))) :
      ∀ l, fan l ≠ j := by
    intro l
    induction l using Fin.addCases with
    | left l =>
      by_cases eq : l = src
      · subst l
        exact fun h => hj.1 (h.symm.trans shared)
      · exact fun h => hj.2 (h ▸ ownersOff l eq)
    | right l => exact fun h => hj.2 (h ▸ controlsOff l)
  refine ⟨A,B',_,rowSwapBlock.states+qa+qb,ports,fan,a,b,disjoint,shared,srcA,srcB,?_⟩
  intro P U Q fits body f
  obtain ⟨setup,swaps,run⟩ := build (k := k) ports body f (by omega)
  let rate := fun (stages : List (FlatCoordinateSchedule.Op 16)) => FlatCoordinateCleanSchedule.constant stages*(1+FlatCoordinateCleanSchedule.tapeCount stages+5)
  refine ⟨rate A+rate B'+setup+16,swaps,?_⟩
  intro node i w B rows rank width split label M K W V hW record dest q desc bank stored clean live
  obtain ⟨position,offset,step⟩ := run node i w B rows rank width split label hW
  have useMove := step a b (show qa ≤ Q by omega) (show qb ≤ Q by omega) srcA srcB apart privateB fan src shared
    ownersOff controlsOff record dest q
  refine ⟨position,offset,?_⟩
  intro lo hi view size input stock
  constructor
  · intro owners L R readDest
    obtain ⟨D,ha,hb,hr,hc⟩ := basisRecordSeed A B' ports a b srcA srcB apart privateB view size record dest q L R readDest
    exact ⟨embOvr fan owners.get D,embStk_ovr fan.injective owners D,D,⟨0,ha,hb,hr,hc⟩,
      fun j hj => embOvr_off _ _ (disjoint j hj)⟩
  let pack := fun js => statePlacedNormalized (U := U) ports (show rowSwapBlock.states ≤ Q by omega)
    swapStates_pos (Empty.elim : Empty → P) (packSchedule 16 js)
  let is := phasePackSchedule lo hi
  let middle := (pack is).seq ((Prog.call f).seq (pack is.reverse))
  let machine := fun (stages : List (FlatCoordinateSchedule.Op 16)) =>
    Placement.placed (FlatCoordinateCleanSchedule.program stages) (sharedPlacement (0 : Fin 1) (segmentSource stages))
  refine ⟨(embProg a (Empty.elim : Empty → P) (foreign (liftQ (machine A) (show qa ≤ Q by omega)))).seq
    (middle.seq (embProg b (Empty.elim : Empty → P) (foreign (liftQ (machine B') (show qb ≤ Q by omega))))),?_⟩
  intro budget child data u S liveS stockS
  obtain ⟨y,z,F,t,exec,time,user,rep,kept,_,action⟩ := useMove budget child data u S liveS stockS
  exact ⟨z,F,t,y,exec,time,user,rep,kept,action⟩

open IntegerMultBounds.Networks.Certificates.PR589 in
noncomputable def positiveMove (p : ℕ × ℕ) : Bool := Geometry.moveRank p.1 p.2 != 0

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Register named by the compiled MOVE at an index across both scatter phases. -/
def invocationRegister (i : ℕ) : Option ℕ :=
  let cut := (Frames.edges (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)).length
  if i < cut then ((sectionD ++ sectionA).flatMap Frames.touched)[i]?
  else ((sectionB ++ sectionC).flatMap Frames.touched)[i-cut]?

/-- Position in the original list of the indexed entry retained by a filter. -/
def retainedPosition {α : Type} (keep : α → Bool) : List α → ℕ → ℕ
  | [], _ => 0
  | x :: xs, i => if keep x then
      match i with
      | 0 => 0
      | j+1 => retainedPosition keep xs j + 1
    else retainedPosition keep xs i + 1

private theorem retainedPosition_split {α : Type} (keep : α → Bool) (pre : List α)
    (x : α) (post : List α) (kept : keep x = true) :
    retainedPosition keep (pre ++ x :: post) (pre.filter keep).length = pre.length := by
  induction pre with
  | nil => simp [retainedPosition,kept]
  | cons y pre ih =>
    cases h : keep y <;> simp [retainedPosition,h,ih]

open IntegerMultBounds.Networks.Certificates.PR589 in
noncomputable def paidRegister (i : ℕ) : Fin 661 :=
  Fin.ofNat 661 ((invocationRegister (retainedPosition positiveMove Geometry.Moves.phaseEdges i)).getD 0)

open IntegerMultBounds.Networks.Certificates.PR589 in
theorem paidRegister_at (pre : List (ℕ × ℕ)) (p : ℕ × ℕ) (post : List (ℕ × ℕ))
    (split : Geometry.Moves.phaseEdges = pre ++ p :: post) (paid : positiveMove p = true)
    (j : Fin 661) (aligned : invocationRegister pre.length = some j.val) :
    paidRegister (pre.filter positiveMove).length = j := by
  apply Fin.ext
  simp only [paidRegister,split,retainedPosition_split _ _ _ _ paid,aligned,
    Option.getD_some,Fin.val_ofNat,Nat.mod_eq_of_lt j.isLt]

open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Install a finite family of paid MOVE calls on a single owner bank. The
workspace and procedure name belong to the occurrence, even for equal pairs. -/
theorem scheduledMoves_host [M8.Machine.Net] (stage : Fin 9) (run : Fin 32 × Fin 5) :
    let edges := Geometry.Moves.phaseEdges.filter fun p => Geometry.moveRank p.1 p.2 != 0
    let I := Fin edges.length
    let edge := fun i : I => edges[i.val]'i.isLt
    let child := fun i : I => phaseChildPositions.choose (stage,run,i)
    let src := fun i : I => ownerTape stage run.1 run.2 (paidRegister i.val)
    ∃ (tapes : I → ℕ) (T states : ℕ) (ports : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (tapes i))
      (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (localBody : ∀ i, P → Pr P (tapes i) Q prime U) (f : I → P),
    let proc := fun (i : I) (g : P) => (i,g)
    let body := fun g : I × P => embProg (bank g.1) (proc g.1) (localBody g.1 g.2)
    ∃ base swaps : I → ℕ, ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W → ∀ record : I → List (Fin (prime+4)),
    let desc := fun i => scheduledChild prime node (child i)
    let regs := fun i => ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans (ports i)
    let stored := fun i => RecordReady (b := prime) (w := w) (d := 16) (W := W) (regs i) M.size W.size (record i)
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun i (D : Stacks (tapes i) prime) => ∀ l : Fin (rowSwapBlock.tapes+35), 35 ≤ l.val →
      D.L (ports i l) = [] ∧ D.R (ports i l) = []
    let live := fun (X : Fin 142081 → Fin V → ZMod 2) (D : Stacks T prime) => RepT (PointwiseRoleGate.bank (a := prime)
      (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V))
      (embStk fan D).L (embStk fan D).R
    ∃ (position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V) (stock : Stacks T prime → Prop),
    (∀ i h, (position i h).val = (CopyChildLayout.packActive (desc i) h).val) ∧
    (∀ owners, ∃ S, embStk fan S = owners ∧ stock S) ∧
    (∀ S F, stock S → (∀ j, (∀ l, fan l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) → stock F) ∧
    ∀ i, ∃ code, ∀ budget,
    ((desc i).width < node.width → ∀ u D word, stored i word D → clean i D →
      ∃ z F t changed, Exec (localBody i) (localBody i (f i)) (mk u D) t (mk z F) ∧ t ≤ budget ∧ z.user = u.user ∧
        stored i changed F ∧ clean i F ∧ (∀ j, (∀ l, ports i l ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
        ∀ h, changed (position i h) = Shared50RecursiveNodeRows.transpose (one_dvd (desc i).rows) (word ∘ position i) h) →
    ∀ data u S, live data S → stock S → ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧
      t ≤ budget+(base i+swaps i*swapVolumeRate w)*V ∧ z.user = u.user ∧ live (Function.update data (src i) y) F ∧
      stock F ∧ ∀ s (j : Fin W), y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) (edge i)) s)) j) =
        data (src i) (index (AffineFieldCoordinates.embed s) j) := by
  classical
  intro edges I edge child src
  have mem (i : I) := List.mem_filter.mp (show edge i ∈ edges from List.getElem_mem ..)
  have checked (i : I) := Geometry.Moves.phase_checked _ (mem i).1
  have paid (i : I) : 0 < Geometry.moveRank (edge i).1 (edge i).2 := Nat.pos_of_ne_zero (bne_iff_ne.mp (mem i).2)
  choose A B' tapes states ports fans a b layout using fun i => allocatedPhaseMove_host (src i) (edge i) (checked i) (paid i)
  obtain ⟨T,fan,bank,shared,family⟩ := moveFamily_host tapes fans
  refine ⟨tapes,T,Finset.univ.sup states,ports,fan,bank,?_⟩
  intro P U Q capacity localBody f proc body
  have fits (i) : states i ≤ Q := (Finset.le_sup (Finset.mem_univ i)).trans capacity
  choose base swaps runMove using fun i => (layout i).2.2.2.2 (fits i) (localBody i) (f i)
  refine ⟨base,swaps,?_⟩
  intro node w B rows width split label M K W V hW record desc regs stored clean live
  choose position offset calls using fun i => runMove i node (child i) w B rows (phaseChildPositions.choose_spec stage run i).1 width split label hW (record i) (fun _ => blank) 0
  let owners : Stacks (142081+2) prime := ⟨[],[],fun _ => [],fun _ => []⟩
  have seeds (i) := (calls i).1 owners [] [] (fun z => by simp [readAt_nil_left,wordTape_nil]; rfl)
  choose code step using fun i => (calls i).2
  obtain ⟨prepare,frame,place⟩ := family _ _ (fun i => (layout i).1) (fun i => by
    obtain ⟨S,_,ready⟩ := seeds i
    exact ⟨S,ready⟩)
  refine ⟨position,_,offset,prepare,frame,?_⟩
  intro i
  refine ⟨embProg (bank i) (proc i) (code i),?_⟩
  intro budget recurse data u S represented ready
  have project (D : Stacks T prime) : embStk (fans i) (embStk (bank i) D) = embStk fan D := by
    simp only [embStk,Function.comp_def,shared]
  obtain ⟨z,F,t,y,exec,time,user,rep,kept,action⟩ := step i budget recurse data (embDn (bank i) u) (embStk (bank i) S)
    (by dsimp only; rw [project]; exact represented) (ready i)
  obtain ⟨v,G,placed,same,view,stock⟩ := place localBody i (code i) u S z F t ready exec kept
  exact ⟨v,G,t,y,placed,time,same.trans user,by dsimp only [live]; rw [view]; exact rep,stock,action⟩

/-- Place the record, both basis passes and both chart machines around the same owner tapes. -/
private theorem copyWindowPlacement {t k m n e x : ℕ} (record : Fin t) (tmp : Fin k)
    (entry : Fin k ↪ Fin e) (exit : Fin k ↪ Fin x) :
    ∃ (T : ℕ) (ports : Fin t ↪ Fin T) (fan : Fin (k+2) ↪ Fin T)
      (a : Fin (1+m) ↪ Fin T) (b : Fin (1+n) ↪ Fin T) (left : Fin e ↪ Fin T) (right : Fin x ↪ Fin T),
    let slots := (Fin.castAddEmb 2).trans fan
    let privatePort := fun j => (∀ l, a l ≠ j) ∧ (∀ l, ports l ≠ j) ∧ (∀ l, b l ≠ j)
    slots tmp = ports record ∧ a ((0 : Fin 1).castAdd _) = ports record ∧ b ((0 : Fin 1).castAdd _) = ports record ∧
    (∀ j, ports j ≠ ports record → ∀ l, a l ≠ ports j) ∧
    (∀ j : Fin n, (∀ l, a l ≠ b (j.natAdd 1)) ∧ (∀ l, ports l ≠ b (j.natAdd 1))) ∧
    (∀ j, j ≠ tmp → privatePort (slots j)) ∧ (∀ i : Fin 2, privatePort (fan (i.natAdd k))) ∧
    (∀ i, left (entry i) = slots i) ∧ (∀ i, right (exit i) = slots i) ∧
    (∀ i : Fin 2, (∀ l, left l ≠ fan (i.natAdd k)) ∧ (∀ l, right l ≠ fan (i.natAdd k))) ∧
    (∀ j, (∀ i, entry i ≠ j) → (privatePort (left j) ∧ ∀ h, fan h ≠ left j) ∧ ∀ l, right l ≠ left j) ∧
    (∀ j, (∀ i, exit i ≠ j) → (privatePort (right j) ∧ ∀ h, fan h ≠ right j) ∧ ∀ l, left l ≠ right j) := by
  obtain ⟨ports,fan,a,b,tmpSlot,aSlot,bSlot,apart,separate,owners,controls⟩ :=
    copyWorkspacePlacement record tmp m n
  let slots := (Fin.castAddEmb 2).trans fan
  let parent := (Fin.castAddEmb (n := ((t+(k+2))+m)+n) e).trans (Fin.castAddEmb x)
  obtain ⟨left,right,shared,outside,rightOff,leftOff⟩ := copyChartPlacement slots entry exit
  refine ⟨_,ports.trans parent,fan.trans parent,a.trans parent,b.trans parent,left,right,
    congrArg parent tmpSlot,congrArg parent aSlot,congrArg parent bSlot,?_,?_,?_,?_,
    fun i => (shared i).1,fun i => (shared i).2,?_,?_,?_⟩
  · exact fun j h l => parent.injective.ne (apart j (fun eq => h (congrArg parent eq)) l)
  · exact fun j => ⟨fun l => parent.injective.ne ((separate j).1 l),fun l => parent.injective.ne ((separate j).2 l)⟩
  · exact fun j h => ⟨fun l => parent.injective.ne ((owners j h).1 l),
      fun l => parent.injective.ne ((owners j h).2.1 l),fun l => parent.injective.ne ((owners j h).2.2 l)⟩
  · exact fun i => ⟨fun l => parent.injective.ne ((controls i).1 l),
      fun l => parent.injective.ne ((controls i).2.1 l),fun l => parent.injective.ne ((controls i).2.2 l)⟩
  · intro i
    apply outside
    intro j eq
    have contra := congrArg Fin.val (fan.injective eq)
    simp [Fin.val_natAdd] at contra
    omega
  · intro j h
    obtain ⟨other,off⟩ := leftOff j h
    exact ⟨⟨⟨fun l => off (a l),fun l => off (ports l),fun l => off (b l)⟩,fun l => off (fan l)⟩,other⟩
  · intro j h
    obtain ⟨other,off⟩ := rightOff j h
    exact ⟨⟨⟨fun l => off (a l),fun l => off (ports l),fun l => off (b l)⟩,fun l => off (fan l)⟩,other⟩

open M8.Machine.Segments SharedPlacementAlphabet in
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord) in
open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Execute one routed COPY window on its assigned tapes and charge its distinct rank-seven child. -/
theorem scheduledCopyWindow_layout [M8.Machine.Net]
    (stage : Fin 9) (r : Fin 32) (d : Fin 5) (window : Fin Copy.lifecycles.length) :
    let life := Copy.lifecycles[window.val]
    ∃ (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (fan : Fin (142081+2) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : P → Pr P T Q prime U) (f : P),
    ∃ base swaps leaf fixed : ℕ, ∀ (node : Descriptor) (w parentB rows B K : ℕ),
    let i := copyChildPosition (stage,(r,d),window)
    node.width = 64*(w+1) →
    node.rows = 142080*rows → node.beforeH = parentB*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let W := B*prime^(64*((w+1)*64))*K
    W = parentB*prime^(64*((w+1)*64))*(M^112*(node.beforeRows*rows*node.between*node.afterD)) →
    0 < W →
    let desc := scheduledChild prime node i
    ∃ position : Fin (volume prime desc) ≃ Fin (M^16*W),
    (∀ k, (position k).val = (CopyChildLayout.packActive desc k).val) ∧
    let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
    let clean := fun D : Stacks T prime => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []
    let V := M^16*W
    let v := copyLabelLayout (w+1) B K
    let sizeV := copyLabel_volume (w+1) B K
    let labels := fun (x : Fin 142081 → Fin V → ZMod 2) k i => x k (Fin.cast sizeV i)
    ∀ record, ∃ prepared : Stacks T prime, ∀ budget,
    let fanReady := fun X (D : Stacks T prime) => RepT (PointwiseRoleGate.bank (a := prime)
      (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V))
      (embStk fan D).L (embStk fan D).R
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    (desc.width < node.width → ∀ (u : HS T Q prime U) D word, stored word D → clean D →
      ∃ z F n changed, Exec body (body f) (mk u D) n (mk z F) ∧ n ≤ budget ∧ z.user = u.user ∧
        stored changed F ∧ clean F ∧ (∀ j, (∀ i, ports i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
        ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (word ∘ position) k) →
    ∃ code : Pr P T Q prime U,
    ∀ (data : Fin 142081 → Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime),
    fanReady data S →
    (∀ j, (∀ h, fan h ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
    ∃ z F t out, Exec body code
      (mk u S) t (mk z F) ∧
      t ≤ (base+swaps*swapVolumeRate w)*V + leaf*M8.RevMachine.LeafCore.coreCost V ((w+1)*64) + fixed + budget ∧
      z.user = u.user ∧ fanReady out F ∧ CopyWindowEffect stage r d life (w+1) B K (labels data) (labels out) := by
  intro life
  have scheduled : life ∈ Copy.lifecycles := List.getElem_mem ..
  classical
  obtain ⟨enter,leave,P₀,Q₀,leadingL,leadingR,chart⟩ := routedCopyWindow_host stage r d life scheduled
  let p := (life.sourceFrame,0)
  let tmp := Fin.last 142080
  let src := ownerTape stage r d ⟨life.source,(Copy.source_bounds life scheduled).2⟩
  let regs := life.targets.attach.map fun j =>
    (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
  let targets := regs.map (ownerTape stage r d)
  have mem := copySource_mem life scheduled
  have checked := retainedCopy_checked.1 _ mem
  have rank : Geometry.moveRank p.1 p.2 = 7 := by
    rw [Geometry.Moves.rank p checked]
    have h := List.mem_map_of_mem (f := Geometry.Moves.value) mem
    rw [retainedCopy_checked.2] at h
    exact (List.mem_replicate.mp h).2
  have paid : 0 < Geometry.moveRank p.1 p.2 := by omega
  obtain ⟨q,s,load,finish,fanout⟩ := copyFanout_host stage r d life scheduled
  obtain ⟨C,rev,fwd,packed⟩ := scheduledPhasePacked_host p checked paid
  let A := description _ rev.good
  let B' := description _ fwd.good
  let recordPort : Fin (rowSwapBlock.tapes+35) := (Fin.castLEEmb swapHostFits) ((Fin.castLEEmb (by decide : 35 ≤ 59)) 24)
  let ls : Fin 142081 ↪ Fin enter.tapes := (Fin.castAddEmb 24).trans ⟨enter.slots,enter.slots_injective⟩
  let rs : Fin 142081 ↪ Fin leave.tapes := (Fin.castAddEmb 24).trans ⟨leave.slots,leave.slots_injective⟩
  obtain ⟨T,ports,fan,a,b,left,right,shared,srcA,srcB,apart,priv,ownersOff,controlsOff,sameL,sameR,counts,leftPriv,rightPriv⟩ :=
    copyWindowPlacement (m := FlatCoordinateCleanSchedule.tapeCount A) (n := FlatCoordinateCleanSchedule.tapeCount B') recordPort (Fin.last 142080) ls rs
  let statesOf {t q : ℕ} (_ : Program t q prime) := q
  let qa := statesOf (FlatCoordinateCleanSchedule.program A)
  let qb := statesOf (FlatCoordinateCleanSchedule.program B')
  refine ⟨T,rowSwapBlock.states+qa+qb+q+s+enter.states+leave.states,ports,fan,?_⟩
  intro P U Q fits body f
  have capacity : rowSwapBlock.states ≤ Q := by omega
  obtain ⟨setup,swaps,run⟩ := packed (k := 142081) ports body f capacity
  let basisRate := fun (stages : List (FlatCoordinateSchedule.Op 16)) =>
    FlatCoordinateCleanSchedule.constant stages*(1+FlatCoordinateCleanSchedule.tapeCount stages+5)
  let base := P₀*(enter.tapes+5)+Q₀*(leave.tapes+5)+basisRate A+basisRate B'+setup+16+76*(life.targets.length+2)*142088
  let leaf := (63+252*life.targets.length)*(enter.tapes+5+ (leave.tapes+5))
  let fixed := (life.targets.length+1)*(enter.tapes+5+(leave.tapes+5))+24
  refine ⟨base,swaps,leaf,fixed,?_⟩
  intro node w parentB rows B K i width split label M W layout hW desc
  have seven := copyChildPosition_rank stage r d window
  have atParent := run node i w parentB rows (seven.trans rank.symm) width split label
  dsimp only at atParent
  rw [← layout] at atParent
  obtain ⟨position,offset,step⟩ := atParent hW
  refine ⟨position,offset,?_⟩
  intro bank clean V
  let view := phaseIntervalChild (min (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2))
    (max (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)) (w+1) W
  let size : volume prime view = V := phaseIntervalChild_volume (phaseInterval_bounds checked paid).1.le
    (phaseInterval_bounds checked paid).2 (w+1) W
  have fitsA : qa ≤ Q := by omega
  have fitsB : qb ≤ Q := by omega
  have loadFits : q ≤ Q := by omega
  have finishFits : s ≤ Q := by omega
  have lf : enter.states ≤ Q := by omega
  have rf : leave.states ≤ Q := by omega
  let privatePort := fun (j : Fin T) => (∀ l, a l ≠ j) ∧ (∀ l, ports l ≠ j) ∧ (∀ l, b l ≠ j)
  intro v sizeV labels record
  let dest := fun _ : ℤ => (blank : Fin 4)
  let q' : ℤ := 0
  obtain ⟨core,initialA,initialB,initialRecord,initialClean⟩ :=
    basisRecordSeed A B' ports a b srcA srcB apart priv view size record dest q' [] []
      (fun z => by simp [readAt_nil_left,wordTape_nil]; rfl)
  let headers := M8.Stage2Machine.Straight.words (LabelSchedule.base v (w+1))
  obtain ⟨L,seedL⟩ := copyChartStacks v headers 142081 enter.tapes
  obtain ⟨R,seedR⟩ := copyChartStacks v headers 142081 leave.tapes
  let charts := embOvr right R.get (embOvr left L.get core)
  let prepared : Stacks T prime := ⟨core.inp,core.out,
    fun j => if privatePort j then charts.L j else core.L j,
    fun j => if privatePort j then charts.R j else core.R j⟩
  have coreAt (j) (used : ¬ privatePort j) :
      prepared.L j = core.L j ∧ prepared.R j = core.R j := by simp [prepared,used]
  have leftAt (j) (hj : ∀ i, ls i ≠ j) :
      prepared.L (left j) = L.L j ∧ prepared.R (left j) = L.R j := by
    obtain ⟨⟨privateL,_⟩,apartR⟩ := leftPriv j hj
    obtain ⟨l,r⟩ := embOvr_off R.get (embOvr left L.get core) (apartR)
    have h : privatePort (left j) := privateL
    simp only [prepared,if_pos h,charts]
    rw [l,r]
    simp only [embOvr,embExt_apply left.injective,Stacks.get,and_self]
  have rightAt (j) (hj : ∀ i, rs i ≠ j) :
      prepared.L (right j) = R.L j ∧ prepared.R (right j) = R.R j := by
    have privateR : privatePort (right j) := (rightPriv j hj).1.1
    simp only [prepared,if_pos privateR,charts,embOvr,embExt_apply right.injective,Stacks.get,and_self]
  refine ⟨prepared,?_⟩
  intro budget fanReady stored recurse
  let price := fun (c t : ℕ) => (c*volume prime v+(63+252*life.targets.length)*M8.RevMachine.LeafCore.coreCost (volume prime v) ((w+1)*64)+life.targets.length+1)*(t+5)+6
  let slots := (Fin.castAddEmb 2).trans fan
  let off := fun j => privatePort j ∧ ∀ l, fan l ≠ j
  let pack := fun js => statePlacedNormalized (U := U) ports capacity swapStates_pos (Empty.elim : Empty → P) (packSchedule 16 js)
  let is := phasePackSchedule (min (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2))
    (max (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2))
  let middle := (pack is).seq ((Prog.call f).seq (pack is.reverse))
  let machine := fun (stages : List (FlatCoordinateSchedule.Op 16)) =>
    Placement.placed (FlatCoordinateCleanSchedule.program stages) (sharedPlacement (0 : Fin 1) (segmentSource stages))
  let convert := (embProg a (Empty.elim : Empty → P) (foreign (liftQ (machine A) fitsA))).seq
        (middle.seq (embProg b (Empty.elim : Empty → P) (foreign (liftQ (machine B') fitsB))))
  let inner := (embProg fan (Empty.elim : Empty → P) (foreign (liftQ load loadFits))).seq
      (convert.seq (embProg fan (Empty.elim : Empty → P) (foreign (liftQ finish finishFits))))
  let code : Pr P T Q prime U := ((embProg left (Empty.elim : Empty → P) (foreign (liftQ enter.program lf))).seq
      (inner.seq (embProg right (Empty.elim : Empty → P) (foreign (liftQ leave.program rf)))))
  refine ⟨code,?_⟩
  intro data u S flatReady saved
  let before := labels data
  let flatten := fun (X : Fin 142081 → Fin (volume prime v) → ZMod 2) k i => X k (Fin.cast sizeV.symm i)
  let chartReady := fun X (D : Stacks T prime) => RepT (PointwiseRoleGate.bank (a := prime)
    (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded (flatten X)) (FlatCoordinateSchedule.bits (volume prime v)))
    (embStk fan D).L (embStk fan D).R
  have restore : flatten before = data := by funext k i; simp [flatten,before,labels]
  have ready := flatReady
  rw [← restore] at ready
  have bitSize := congrArg FlatCoordinateSchedule.bits sizeV
  dsimp only [fanReady] at ready
  rw [← bitSize] at ready
  have hB : 0 < B := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz,W] at hW
  have hK : 0 < K := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz,W] at hW
  have owners : RepT (copyOwners (v := v) before) (embStk slots S).L (embStk slots S).R := by
    have rep := ready
    rw [copyOwners_controls sizeV (flatten before),show (fun k i => flatten before k (Fin.cast sizeV i)) = before by
      funext k i; simp [flatten]] at rep
    intro k j
    have slot : slots k = fan (k.castAdd 2) := by apply congrArg fan; apply Fin.ext; rfl
    simpa only [Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,slot] using rep (k.castAdd 2) j
  have readyL := copyRoute_ready enter leadingL left v _ (copyOwners 0) (copyOwners before) (embOvr left L.get core) S (by simpa only [embStk_ovr left.injective] using seedL)
    (by intro k j; simpa only [embStk,Function.comp_apply,show ∀ i, left (enter.slots (Fin.castAdd 24 i)) = slots i from sameL] using owners k j)
    (by
      intro j hj
      obtain ⟨l,r⟩ := saved _ (leftPriv j hj).1.2
      obtain ⟨pl,pr⟩ := leftAt j hj
      simpa only [embOvr,embExt_apply left.injective,Stacks.get] using And.intro (l.trans pl) (r.trans pr))
  have readyR := copyRoute_ready leave leadingR right v _ (copyOwners 0) (copyOwners before) (embOvr right R.get core) S (by simpa only [embStk_ovr right.injective] using seedR)
    (by intro k j; simpa only [embStk,Function.comp_apply,show ∀ i, right (leave.slots (Fin.castAdd 24 i)) = slots i from sameR] using owners k j)
    (by
      intro j hj
      obtain ⟨l,r⟩ := saved _ (rightPriv j hj).1.2
      obtain ⟨pl,pr⟩ := rightAt j hj
      simpa only [embOvr,embExt_apply right.injective,Stacks.get] using And.intro (l.trans pl) (r.trans pr))
  obtain ⟨out,z,F,t,exec,time,user,rr,rl,rfan,effect,frame⟩ := chart left right fan lf rf body inner off
    (budget+(basisRate A+basisRate B'+setup+16+swaps*swapVolumeRate w)*V+76*(life.targets.length+2)*V*142088+12) (w+1) B K (Nat.succ_pos _) hB hK sameL
    (fun i => (counts i).1) sameR (fun i => (counts i).2) (fun j hj => (rightPriv j hj).2)
    (fun j hj => (leftPriv j hj).2) before u S readyL readyR ready (by
    intro entered v' D₀ tmpEq fanInput chartOff
    let data := flatten entered
    let x := data src
    let keep := privatePort
    have digits : FlatCoordinateSchedule.bits (volume prime v) = FlatCoordinateSchedule.bits V := congrArg _ sizeV
    have inFan : RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded data) (FlatCoordinateSchedule.bits V)) (embStk fan D₀).L (embStk fan D₀).R := by
      change chartReady entered D₀ at fanInput
      simpa only [chartReady,digits] using fanInput
    obtain ⟨z,F,t,exec,time,user,done,frame⟩ := fanout fan loadFits finishFits body convert
      (budget+(basisRate A+basisRate B'+setup+16+swaps*swapVolumeRate w)*V) keep data hW v' D₀ inFan (by
        intro v D loaded outside
        let X := Function.update data tmp x
        have kept (j) (separate : j ≠ bank 24) (used : ¬ keep j) : D.L j = core.L j ∧ D.R j = core.R j := by
          have chartKeep : ∀ l, left l ≠ j := by
            intro l eq
            by_cases covered : ∃ i, ls i = l
            · obtain ⟨i,rfl⟩ := covered
              rw [sameL] at eq
              by_cases ht : i = tmp
              · exact separate (eq.symm.trans ((congrArg slots ht).trans shared))
              · exact used (eq ▸ ownersOff i ht)
            · exact used (eq ▸ (leftPriv l (fun i h => covered ⟨i,h⟩)).1.1)
          have fanOff : ∀ l, fan l ≠ j := by
            intro l
            induction l using Fin.addCases with
            | left k =>
              change slots k ≠ j
              by_cases ht : k = tmp
              · exact fun eq => separate (eq.symm.trans ((congrArg slots ht).trans shared))
              · exact fun eq => used (eq ▸ ownersOff k ht)
            | right k => exact fun eq => used (eq ▸ controlsOff k)
          obtain ⟨ld,rd⟩ := outside j fanOff
          obtain ⟨lc,rc⟩ := chartOff j chartKeep
          obtain ⟨ls,rs⟩ := saved j fanOff
          exact ⟨ld.trans (lc.trans (ls.trans (coreAt j used).1)),rd.trans (rc.trans (rs.trans (coreAt j used).2))⟩
        obtain ⟨y,z,G,m,exec,time,user,owners,_,off,action⟩ :=
          step a b fitsA fitsB srcA srcB apart priv fan tmp shared ownersOff controlsOff record dest q' budget recurse
            X v D loaded ⟨core,⟨0,initialA,initialB,initialRecord,initialClean⟩,fun j h => kept j h.1 h.2⟩
        refine ⟨z,G,m,y,exec,time,user,?_,?_,fun j h _ => off j h.1 h.2.1 h.2.2⟩
        · simpa only [X,Function.update_idem] using owners
        · simpa only [copyAddress_index,X,Function.update_self] using action)
    let addr := copyAddress (Q := M) (W := W)
    let move := AffineFieldProgram.run (selectedWord (w+1) p)
    let common := fun i => x (addr.symm (move (addr i).1,(addr i).2))
    let result := Function.update (fun j i => if j ∈ targets then data j i + common i else data j i) tmp 0
    refine ⟨result,z,F,t,exec,time,user,?_,copyFanout_effect stage r d life scheduled (w+1) B K data,?_,?_,?_⟩
    · have castEq : flatten (fun k i => result k (Fin.cast sizeV i)) = result := by funext k i; simp [flatten]
      change chartReady (fun k i => result k (Fin.cast sizeV i)) F
      dsimp only [chartReady]
      rw [castEq,digits]
      exact done
    · intro j hj
      obtain ⟨privateTapes,fanOff⟩ := (leftPriv j hj).1
      exact frame _ privateTapes fanOff
    · intro j hj
      obtain ⟨privateTapes,fanOff⟩ := (rightPriv j hj).1
      exact frame _ privateTapes fanOff
    · intro j hj _ _
      exact frame _ hj.1 hj.2)
  have back : labels (flatten out) = out := by funext k i; simp [flatten,labels]
  change t ≤ price P₀ enter.tapes+(budget+(basisRate A+basisRate B'+setup+16+swaps*swapVolumeRate w)*V+
    76*(life.targets.length+2)*V*142088+12)+price Q₀ leave.tapes at time
  refine ⟨z,F,t,flatten out,exec,time.trans_eq ?_,user,?_,?_⟩
  · have vol : volume prime v = V := sizeV
    simp only [price,vol,base,leaf,fixed]
    ring
  · change chartReady out F at rfan
    dsimp only [fanReady]
    rw [← bitSize]
    exact rfan
  · rw [back]
    exact effect

open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
theorem scheduledCopyWindow_host [M8.Machine.Net]
    (stage : Fin 9) (r : Fin 32) (d : Fin 5) (window : Fin Copy.lifecycles.length) :
    let life := Copy.lifecycles[window.val]
    ∃ (T states : ℕ) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (fan : Fin (142081+2) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q → ∀ (body : P → Pr P T Q prime U) (f : P),
    ∃ base swaps leaf fixed : ℕ, ∀ (node : Descriptor) (w B rows : ℕ),
    let i := copyChildPosition (stage,(r,d),window)
    node.width = 64*(w+1) →
    node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    0 < W →
    let desc := scheduledChild prime node i
    ∃ position : Fin (volume prime desc) ≃ Fin (M^16*W),
    (∀ k, (position k).val = (CopyChildLayout.packActive desc k).val) ∧
    let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
    let clean := fun D : Stacks T prime => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []
    let V := M^16*W
    let v := copyLabelLayout (w+1) B K
    let sizeV := copyLabel_volume (w+1) B K
    let labels := fun (x : Fin 142081 → Fin V → ZMod 2) k i => x k (Fin.cast sizeV i)
    ∀ record, ∃ prepared : Stacks T prime, ∀ budget,
    let fanReady := fun X (D : Stacks T prime) => RepT (PointwiseRoleGate.bank (a := prime)
      (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V))
      (embStk fan D).L (embStk fan D).R
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    (desc.width < node.width → ∀ (u : HS T Q prime U) D word, stored word D → clean D →
      ∃ z F n changed, Exec body (body f) (mk u D) n (mk z F) ∧ n ≤ budget ∧ z.user = u.user ∧
        stored changed F ∧ clean F ∧ (∀ j, (∀ i, ports i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
        ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (word ∘ position) k) →
    ∃ code : Pr P T Q prime U,
    ∀ (data : Fin 142081 → Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime),
    fanReady data S →
    (∀ j, (∀ h, fan h ≠ j) → S.L j = prepared.L j ∧ S.R j = prepared.R j) →
    ∃ z F t out, Exec body code
      (mk u S) t (mk z F) ∧
      t ≤ (base+swaps*swapVolumeRate w)*V + leaf*M8.RevMachine.LeafCore.coreCost V ((w+1)*64) + fixed + budget ∧
      z.user = u.user ∧ fanReady out F ∧ CopyWindowEffect stage r d life (w+1) B K (labels data) (labels out) := by
  intro life
  obtain ⟨T,states,ports,fan,build⟩ := scheduledCopyWindow_layout stage r d window
  refine ⟨T,states,ports,fan,?_⟩
  intro P U Q fits body f
  obtain ⟨base,swaps,leaf,fixed,run⟩ := build fits body f
  refine ⟨base,swaps,leaf,fixed,?_⟩
  intro node w B rows i width split label M K W
  exact run node w B rows B K width split label rfl


def indexedBill {α : Type} (cost : ℕ → α → ℕ) (i : ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => cost i x + indexedBill cost (i+1) xs

private theorem indexedBill_append {α : Type} (cost : ℕ → α → ℕ) (xs ys : List α) (i : ℕ) :
    indexedBill cost i (xs ++ ys) = indexedBill cost i xs + indexedBill cost (i+xs.length) ys := by
  induction xs generalizing i with
  | nil => simp [indexedBill]
  | cons x xs ih => simp [indexedBill,ih,Nat.add_assoc,Nat.add_comm 1]

private theorem indexedBill_split {α : Type} (work child : ℕ → ℕ) (xs : List α) (i : ℕ) :
    indexedBill (fun j _ => work j + child j) i xs =
      ((List.range' i xs.length).map work).sum + ((List.range' i xs.length).map child).sum := by
  induction xs generalizing i with
  | nil => simp [indexedBill]
  | cons x xs ih => simp [indexedBill,ih,List.range'_succ]; omega

private theorem windowBill_split {n : ℕ} (work : Fin n → ℕ) (child : ℕ → ℕ) (i : ℕ) :
    (List.ofFn (fun j => work j + child (i+j.val))).sum =
      (List.ofFn work).sum + ((List.range' i n).map child).sum := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.range'_succ,List.map_cons,List.sum_cons,Fin.val_zero,Nat.add_zero,Fin.val_succ]
    simp only [show ∀ j : Fin n, i + (j.val+1) = i+1+j.val by intro j; omega]
    rw [ih (fun j => work j.succ) (i+1)]
    omega

/-- Registers in MOVE order, including rank-zero frame changes. -/
def phaseRegisters {w : ℕ} :
    List (FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^w)))) → List ℕ
  | [] => []
  | .gate _ :: rest => phaseRegisters rest
  | .edge r _ _ :: rest => r :: phaseRegisters rest

open IntegerMultBounds.Networks.Certificates.PR589 in
private theorem phaseRegisters_compile {w : ℕ}
    (frame : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^w))))
    (current : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^w))))
    (gs : List RawGate) :
    phaseRegisters (FramedCircuit.compile current (gs.map (Frames.framedGate frame))) =
      gs.flatMap Frames.touched := by
  have append (xs ys : List (FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^w))))) :
      phaseRegisters (xs ++ ys) = phaseRegisters xs ++ phaseRegisters ys := by
    induction xs with
    | nil => rfl
    | cons op xs ih => cases op <;> simp [phaseRegisters,ih]
  have wires (a b : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^w)))) (is : List ℕ) :
      phaseRegisters (FramedCircuit.edges a b is) = is := by
    induction is generalizing a with
    | nil => rfl
    | cons i is ih => simp only [FramedCircuit.edges,phaseRegisters,ih]
  induction gs generalizing current with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,FramedCircuit.compile,FramedCircuit.compileGate,append,wires,
      phaseRegisters,Frames.framedGate,Frames.touched_toCircuit,List.append_nil,ih,List.flatMap_cons]

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Sequence physical phase instructions on the common owner bank. Each gate
and positive-rank edge pays its own execution bound once. Rank-zero moves
consume the corresponding trace entry and leave the machine untouched. -/
theorem phaseInstructions_host {T Q w W : ℕ} {P U I : Type}
    (body : P → Pr P T Q prime U)
    (ready : I → (Fin W → ℕ → AddressStream (ZMod (prime^(w+1)))) → Stacks T prime → Prop)
    (gs : List (FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^(w+1))))))
    (ps : List (ℕ × ℕ)) (checked : ∀ p ∈ ps, Geometry.Moves.CheckedPair p)
    (gateTime : Circuit.Gate ℕ (ZMod 2) → ℕ) (edgeTime : ℕ → ℕ × ℕ → ℕ) (start : ℕ)
    (gate : ∀ g, .gate g ∈ gs → ∃ code, ∀ ctx x u S, ready ctx x S →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ n ≤ gateTime g ∧ z.user = u.user ∧
        ready ctx (fun j => FramedCircuit.moduleGate g (x j)) F)
    (edge : ∀ r old next, .edge r old next ∈ gs → ∀ pre p post, ps = pre ++ p :: post →
      (phaseRegisters gs)[pre.length]? = some r → Geometry.moveRank p.1 p.2 ≠ 0 →
      ∃ code, ∀ ctx x u S, ready ctx x S → ∃ z F n, Exec body code (mk u S) n (mk z F) ∧
        n ≤ edgeTime (start+(pre.filter positiveMove).length) p ∧ z.user = u.user ∧ ready ctx (fun j => Function.update (x j) r
          (fun s => x j r (AffineFieldProgram.run (selectedWord (w+1) p) s))) F) :
    let localCost := fun op : FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^(w+1)))) =>
      match op with | .gate g => gateTime g | .edge .. => 0
    ∃ code, ∀ ctx x u S, ready ctx x S → ∃ z F n, Exec body code (mk u S) n (mk z F) ∧
      n ≤ (gs.map localCost).sum+indexedBill edgeTime start (ps.filter positiveMove)+1 ∧ z.user = u.user ∧
      ready ctx (fun j => runPhase (selectedWord (w+1)) gs ps (x j)) F := by
  intro localCost
  induction gs generalizing ps start with
  | nil =>
    exact ⟨.act .done,fun _ _ u S ok => ⟨u,S,1,Exec.act _ _,by simp,rfl,ok⟩⟩
  | cons op rest ih =>
    have gates := fun g (h : FramedCircuit.Instruction.gate g ∈ rest) => gate g (List.mem_cons_of_mem _ h)
    have edges := fun r old next (h : FramedCircuit.Instruction.edge r old next ∈ rest) =>
      edge r old next (List.mem_cons_of_mem _ h)
    cases op with
    | gate g =>
      obtain ⟨head,step⟩ := gate g List.mem_cons_self
      obtain ⟨tail,finish⟩ := ih ps checked start gates
        (fun i a b h pre p post split aligned => edges i a b h pre p post split aligned)
      refine ⟨head.seq tail,?_⟩
      intro ctx x u S ok
      obtain ⟨v,D,t,run,time,user,mid⟩ := step ctx x u S ok
      obtain ⟨z,F,n,exec,bound,same,out⟩ := finish ctx _ v D mid
      refine ⟨z,F,_,Exec.seq run exec,?_,same.trans user,out⟩
      simp only [List.map_cons,List.sum_cons,localCost] at bound ⊢
      omega
    | edge r old next =>
      cases ps with
      | nil =>
        exact ⟨.act .done,fun _ _ u S ok => ⟨u,S,1,Exec.act _ _,by simp,rfl,ok⟩⟩
      | cons p ps =>
        let advance := if positiveMove p then 1 else 0
        obtain ⟨tail,finish⟩ := ih ps (fun q h => checked q (List.mem_cons_of_mem _ h)) (start+advance) gates
          (fun i a b h pre q post eq aligned => by
            have step := edges i a b h (p :: pre) q post (congrArg (p :: ·) eq) (by simpa [phaseRegisters] using aligned)
            by_cases pos : positiveMove p <;> simpa [advance,pos,Nat.add_assoc,Nat.add_comm 1] using step)
        by_cases zero : Geometry.moveRank p.1 p.2 = 0
        · refine ⟨tail,?_⟩
          intro ctx x u S ok
          obtain ⟨z,F,n,run,time,user,out⟩ := finish ctx x u S ok
          refine ⟨z,F,n,run,?_,user,?_⟩
          · simpa [localCost,advance,positiveMove,zero] using time
          · have unchanged (j : Fin W) : Function.update (x j) r
                (fun s => x j r (AffineFieldProgram.run (selectedWord (w+1) p) s)) = x j := by
              simp only [(modular_scatter (w+1)).choose_spec.2.2.1.zero p (checked p List.mem_cons_self) zero,
                Function.update_eq_self]
            simpa only [runPhase,unchanged] using out
        · obtain ⟨head,step⟩ := edge r old next List.mem_cons_self [] p ps rfl rfl zero
          refine ⟨head.seq tail,?_⟩
          intro ctx x u S ok
          obtain ⟨v,D,t,run,time,user,mid⟩ := step ctx x u S ok
          obtain ⟨z,F,n,exec,bound,same,out⟩ := finish ctx _ v D mid
          refine ⟨z,F,_,Exec.seq run exec,?_,same.trans user,out⟩
          have pos : positiveMove p = true := by simp [positiveMove,zero]
          simp [localCost,advance,pos,indexedBill] at bound time ⊢
          omega

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Assemble either literal PR589 phase from physical scalar and MOVE
executions. The returned owner bank implements the compiled frame snapshot. -/
theorem invocationPhase_host {T Q k w W : ℕ} {P U : Type} (owner : Fin 661 ↪ Fin k)
    (body : P → Pr P T Q prime U) (afterScatter : Bool)
    (ready : (Fin k → Fin ((prime^(w+1))^16*W) → ZMod 2) → Stacks T prime → Prop)
    (moveTime : ℕ → ℕ × ℕ → ℕ) (start : ℕ) :
    let V := (prime^(w+1))^16*W
    let gates := if afterScatter then sectionB ++ sectionC else sectionD ++ sectionA
    let current := if afterScatter then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let frame := selectedFrame (w+1)
    let edges := Frames.edges gates current
    let gateTime := fun g : Circuit.Gate ℕ (ZMod 2) => 76*g.terms.length*V*(k+7)+6
    (∀ g ∈ program, ∃ code, ∀ data u S, ready data S →
      ∃ z F n out, Exec body code (mk u S) n (mk z F) ∧ n ≤ gateTime g.toCircuit ∧ z.user = u.user ∧
        ready out F ∧ (∀ i, (∀ r, owner r ≠ i) → out i = data i) ∧ ∀ r : Fin 661, ∀ i, out (owner r) i =
          g.toCircuit.run (Copy.extendStored (fun r => data (owner r) i)) r.val) →
    (∀ (r : Fin 661) pre p post, edges = pre ++ p :: post →
      (phaseRegisters (FramedCircuit.compile (fun i => frame (current i)) (gates.map (Frames.framedGate frame))))[pre.length]? = some r.val →
      Geometry.Moves.CheckedPair p → Geometry.moveRank p.1 p.2 ≠ 0 →
      ∃ code, ∀ data u S, ready data S → ∃ z F n y, Exec body code (mk u S) n (mk z F) ∧
        n ≤ moveTime (start+(pre.filter positiveMove).length) p ∧ z.user = u.user ∧ ready (Function.update data (owner r) y) F ∧
        ∀ s j, y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) p) s)) j) =
          data (owner r) (index (AffineFieldCoordinates.embed s) j)) →
    ∃ code, ∀ data u S, ready data S → ∃ z F n out, Exec body code (mk u S) n (mk z F) ∧
      n ≤ (gates.map (fun g => gateTime g.toCircuit)).sum +
        indexedBill moveTime start (edges.filter positiveMove)+1 ∧
      z.user = u.user ∧ ready out F ∧ (∀ i, (∀ r, owner r ≠ i) → out i = data i) ∧ ∀ j, phaseRead owner out j =
        FramedCircuit.encode (fun i => frame (Frames.run gates current i))
          (FramedCircuit.moduleRun (gates.map RawGate.toCircuit)
            (FramedCircuit.decode (fun i => frame (current i)) (phaseRead owner data j))) := by
  intro V gates current frame edges gateTime gate move
  let instructions := FramedCircuit.compile (fun i => frame (current i)) (gates.map (Frames.framedGate frame))
  obtain ⟨checked,valid⟩ := invocationPhase_valid (w+1) afterScatter
  let represented := fun (original : Fin k → Fin V → ZMod 2) (x : Fin W → ℕ → AddressStream (ZMod (prime^(w+1)))) S => ∃ data, ready data S ∧ (∀ i, (∀ r, owner r ≠ i) → data i = original i) ∧ ∀ j, phaseRead owner data j = x j
  let scalar := fun op : FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^(w+1)))) =>
    match op with | .gate g => gateTime g | .edge .. => 0
  have gatesCost (gs : List RawGate) (cur : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^(w+1))))) :
      ((FramedCircuit.compile cur (gs.map (Frames.framedGate frame))).map scalar).sum =
        (gs.map fun g => gateTime g.toCircuit).sum := by
    have free (a b : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^(w+1))))) (ws : List ℕ) :
        ((FramedCircuit.edges a b ws).map scalar).sum = 0 := by
      induction ws generalizing a with
      | nil => rfl
      | cons i is ih => simp only [FramedCircuit.edges,List.map_cons,List.sum_cons,scalar,ih,Nat.zero_add]
    induction gs generalizing cur with
    | nil => rfl
    | cons g gs ih => simp only [List.map_cons,FramedCircuit.compile,FramedCircuit.compileGate,
        List.map_append,List.sum_append,ih,free,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Nat.zero_add,Nat.add_zero,scalar,Frames.framedGate]
  obtain ⟨code,run⟩ := phaseInstructions_host body represented instructions edges checked gateTime moveTime start (by
    intro g member
    obtain ⟨raw,scheduled,rfl⟩ := valid (.gate g) member
    obtain ⟨code,step⟩ := gate raw scheduled
    refine ⟨code,?_⟩
    intro original x u S ⟨data,ok,fixed,hx⟩
    obtain ⟨z,F,n,out,exec,time,user,done,off,act⟩ := step data u S ok
    exact ⟨z,F,n,exec,time,user,out,done,fun i h => (off i h).trans (fixed i h),fun j => (phaseRead_gate owner raw scheduled data out act j).trans
      (congrArg _ (hx j))⟩) (by
    intro i a b member pre p post split aligned paid
    have hp : p ∈ edges := split ▸ List.mem_append_right _ List.mem_cons_self
    let r : Fin 661 := ⟨i,valid (.edge i a b) member⟩
    obtain ⟨code,step⟩ := move r pre p post split aligned (checked p hp) paid
    refine ⟨code,?_⟩
    intro original x u S ⟨data,ok,fixed,hx⟩
    obtain ⟨z,F,n,y,exec,time,user,done,act⟩ := step data u S ok
    refine ⟨z,F,n,exec,time,user,_,done,fun k h => (Function.update_of_ne (h r).symm ..).trans (fixed k h),?_⟩
    intro j
    dsimp only
    rw [← hx j]
    apply phaseRead_edge owner r p data _ (fun k ne => Function.update_of_ne ne ..) _ j
    intro s l
    rw [Function.update_self]
    have h := act (AffineFieldProgram.run (selectedWord (w+1) p) s) l
    rwa [(modular_scatter (w+1)).choose_spec.2.1 p (checked p hp) s] at h)
  refine ⟨code,?_⟩
  intro data u S ok
  obtain ⟨z,F,n,exec,time,user,out,done,off,reads⟩ := run data (phaseRead owner data) u S ⟨data,ok,fun _ _ => rfl,fun _ => rfl⟩
  refine ⟨z,F,n,out,exec,?_,user,done,off,fun j => (reads j).trans (phaseLogicalRead (w+1) gates current checked _)⟩
  change n ≤ (instructions.map scalar).sum+_+1 at time
  rwa [gatesCost gates (fun i => frame (current i))] at time

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- The literal XOR list for a phase gate runs on the shared owner and control bank. -/
private theorem phaseGateProgram {k : ℕ} (owner : Fin 661 ↪ Fin k) (g : RawGate) (mem : g ∈ program) :
    ∃ (q : ℕ) (machine : Program (k+2) q prime), ∀ V, 0 < V → ∀ data : Fin k → Fin V → ZMod 2,
      let bank := fun X => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V)
      ∃ out, HoareTime machine (fun X => X = bank data) (fun Y => Y = bank out) (76*g.toCircuit.terms.length*V) ∧
        (∀ i, (∀ j, owner j ≠ i) → out i = data i) ∧ ∀ j : Fin 661, ∀ i,
        out (owner j) i = g.toCircuit.run (Copy.extendStored (fun r => data (owner r) i)) j.val := by
  classical
  let target := (⟨g.target,(register_bounds g mem).1⟩ : Fin 661)
  let dst := fun _ : Unit => owner target
  let src := fun j : {j // j ∈ g.sources} => owner ⟨j.val,(register_bounds g mem).2 _ j.property⟩
  let entries := g.sources.attach.map fun j => ((),j)
  have off : ∀ a b, dst a ≠ src b := by
    intro a b eq
    have same : b.val = g.target := (congrArg Fin.val (owner.injective eq)).symm
    exact target_not_mem_sources g mem (same ▸ b.property)
  refine ⟨_,SparseRoleCircuit.program dst src off entries,?_⟩
  intro V pos data bank
  let out := fun k i => Circuit.run (SparseCircuit.copies dst src entries) (fun j => data j i) k
  refine ⟨out,?_,?_,?_⟩
  · have run := SparseRoleCircuit.copies_hoare (a := prime) dst src off entries (fun _ _ => blank) (fun _ => 0)
        data (FlatCoordinateSchedule.bits V) (FlatCoordinateSchedule.bits_value V)
    apply run.consequence (fun _ h => h) (fun _ h => h)
    simpa [entries,RawGate.toCircuit] using SparseRoleCircuit.cost_linear entries.length V _
      (FlatCoordinateSchedule.bits_value V) (FlatCoordinateSchedule.bits_canonical V) pos
  · intro j unused
    funext i
    simp [out,SparseCircuit.copies_run _ _ _ off,entries,dst,unused]
  · intro j i
    rw [RawGate.run_eq]
    change Circuit.run _ _ _ = _
    rw [SparseCircuit.copies_run _ _ _ off]
    by_cases eq : j = target
    · subst j
      have reads (r : {j // j ∈ g.sources}) : data (src r) i =
          Copy.extendStored (fun a => data (owner a) i) r.val := by
        simp [Copy.extendStored,src,(register_bounds g mem).2 _ r.property]
      simp only [entries,List.map_map,Function.comp_def,dst,ite_true,reads]
      rw [List.attach_map_val (l := g.sources) (f := Copy.extendStored (fun a => data (owner a) i))]
      simp [target,Copy.extendStored,(register_bounds g mem).1]
    · have ne : j.val ≠ g.target := fun h => eq (Fin.ext h)
      simp [entries,dst,Ne.symm eq,Function.update_of_ne ne,Copy.extendStored,j.isLt]

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Place the scalar gates on the owner ports while preserving any stock
whose representation depends only on private tape words. -/
theorem scheduledGates_host {k : ℕ} (owner : Fin 661 ↪ Fin k) :
    ∃ states : ℕ, ∀ {T Q V : ℕ} {P U : Type}, states ≤ Q → 0 < V →
    ∀ (ports : Fin (k+2) ↪ Fin T) (body : P → Pr P T Q prime U) (stock : Stacks T prime → Prop),
    (∀ S F, stock S → (∀ l, (∀ h, ports h ≠ l) → F.L l = S.L l ∧ F.R l = S.R l) → stock F) →
    let ready := fun (data : Fin k → Fin V → ZMod 2) (S : Stacks T prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded data) (FlatCoordinateSchedule.bits V)) (embStk ports S).L (embStk ports S).R ∧ stock S
    ∀ g ∈ program, ∃ code, ∀ data u S, ready data S → ∃ z F t out,
      Exec body code (mk u S) t (mk z F) ∧ t ≤ 76*g.toCircuit.terms.length*V*(k+7)+6 ∧
      z.user = u.user ∧ ready out F ∧ (∀ i, (∀ j, owner j ≠ i) → out i = data i) ∧
      ∀ j : Fin 661, ∀ i, out (owner j) i = g.toCircuit.run (Copy.extendStored (fun j => data (owner j) i)) j.val := by
  let gate (g : {g // g ∈ program}) := phaseGateProgram owner g.val g.property
  let states := program.attach.map fun g => (gate g).choose
  refine ⟨states.sum,?_⟩
  intro T Q V P U capacity pos ports body stock frame ready
  intro g mem
  let h := gate ⟨g,mem⟩
  obtain ⟨machine,run⟩ := h.choose_spec
  have fits : h.choose ≤ Q := (List.le_sum_of_mem (show h.choose ∈ states from
    List.mem_map.mpr ⟨⟨g,mem⟩,List.mem_attach _ _,rfl⟩)).trans capacity
  refine ⟨embProg ports (Empty.elim : Empty → P) (foreign (liftQ machine fits)),?_⟩
  intro data u S ok
  obtain ⟨out,hoare,other,reads⟩ := run V pos data
  obtain ⟨z,F,t,exec,time,user,rep,off⟩ := placedHoare_exec machine ports fits body
    hoare u S ok.1
  refine ⟨z,F,t,out,exec,time,user,⟨rep,?_⟩,other,reads⟩
  exact frame _ _ ok.2 off

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Price either scalar phase against its positions in the full invocation schedule. -/
theorem scheduledScalarPhase_host {T Q w W : ℕ} {P U : Type} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (body : P → Pr P T Q prime U)
    (ready : (Fin 142081 → Fin ((prime^(w+1))^16*W) → ZMod 2) → Stacks T prime → Prop)
    (moveTime : ℕ → ℕ × ℕ → ℕ) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let gateTime := fun g : Circuit.Gate ℕ (ZMod 2) => 76*g.terms.length*((prime^(w+1))^16*W)*(142081+7)+6
    (∀ g ∈ program, ∃ code, ∀ data u S, ready data S →
      ∃ z F n out, Exec body code (mk u S) n (mk z F) ∧ n ≤ gateTime g.toCircuit ∧ z.user = u.user ∧
        ready out F ∧ (∀ i, (∀ r, owner r ≠ i) → out i = data i) ∧ ∀ r : Fin 661, ∀ i, out (owner r) i =
          g.toCircuit.run (Copy.extendStored (fun r => data (owner r) i)) r.val) →
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    (∀ i : Fin edges.length,
      let p := edges[i.val]'i.isLt
      let child := phaseChildPositions.choose (n,(r,d),i)
      let j := paidRegister i.val
      ∃ code, ∀ data u S, ready data S → ∃ z F t y,
        Exec body code (mk u S) t (mk z F) ∧ t ≤ moveTime child.val p ∧ z.user = u.user ∧
        ready (Function.update data (owner j) y) F ∧ ∀ s l,
          y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) p) s)) l) =
            data (owner j) (index (AffineFieldCoordinates.embed s) l)) →
    ∀ afterScatter : Bool,
    let gates := if afterScatter then sectionB ++ sectionC else sectionD ++ sectionA
    let current := if afterScatter then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let start := stageChildStart n + runChildStart (r,d) + (if afterScatter then
      ((Frames.edges (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length else 0)
    let frame := selectedFrame (w+1)
    let edges := Frames.edges gates current
    ∃ code, ∀ data u S, ready data S → ∃ z F n out, Exec body code (mk u S) n (mk z F) ∧
      n ≤ (gates.map (fun g => gateTime g.toCircuit)).sum +
        indexedBill moveTime start (edges.filter positiveMove)+1 ∧
      z.user = u.user ∧ ready out F ∧ (∀ i, (∀ r, owner r ≠ i) → out i = data i) ∧ ∀ j, phaseRead owner out j =
        FramedCircuit.encode (fun i => frame (Frames.run gates current i))
          (FramedCircuit.moduleRun (gates.map RawGate.toCircuit)
            (FramedCircuit.decode (fun i => frame (current i)) (phaseRead owner data j))) := by
  intro owner gateTime gates paidEdges moves
  have moveAt (j : Fin 661) (pre : List (ℕ × ℕ)) p post (split : Geometry.Moves.phaseEdges = pre ++ p :: post)
      (aligned : invocationRegister pre.length = some j.val)
      (checked : Geometry.Moves.CheckedPair p) (paid : Geometry.moveRank p.1 p.2 ≠ 0) :
      ∃ code, ∀ data u S, ready data S → ∃ z F t y,
        Exec body code (mk u S) t (mk z F) ∧ t ≤ moveTime (stageChildStart n + runChildStart (r,d) + (pre.filter positiveMove).length) p ∧ z.user = u.user ∧
        ready (Function.update data (owner j) y) F ∧ ∀ s l,
          y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) p) s)) l) =
            data (owner j) (index (AffineFieldCoordinates.embed s) l) := by
    have trace : paidEdges = pre.filter positiveMove ++ p :: post.filter positiveMove := by
      have keep : positiveMove p = true := by simpa [positiveMove] using paid
      simp only [paidEdges,split,List.filter_append,List.filter_cons_of_pos keep]
    let k : Fin paidEdges.length := ⟨(pre.filter positiveMove).length,by rw [trace]; simp⟩
    have atPos : paidEdges[k.val]'k.isLt = p := by
      simp only [k,trace,List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]
    have offset := (phaseChildPositions.choose_spec n (r,d) k).2
    have reg := paidRegister_at pre p post split (by simpa [positiveMove] using paid) j aligned
    obtain ⟨code,execute⟩ := moves k
    refine ⟨code,?_⟩
    intro data u S ready
    obtain ⟨z,F,t,y,exec,time,user,out,reads⟩ := execute data u S ready
    have ownerEq : paidRegister k.val = j := reg
    rw [ownerEq] at out reads
    rw [atPos] at reads time
    rw [offset] at time
    exact ⟨z,F,t,y,exec,by simpa only [Nat.add_assoc] using time,user,out,reads⟩
  intro afterScatter
  cases afterScatter
  · exact invocationPhase_host owner body false ready moveTime (stageChildStart n + runChildStart (r,d)) gates
      (fun j pre p post split aligned => moveAt j pre p (post ++ Frames.edges (sectionB ++ sectionC) (Frames.scatterFinish Frames.beforeScatter)) (by
        simp only [Bool.false_eq_true,ite_false] at split
        unfold Geometry.Moves.phaseEdges
        rw [split]
        simp only [List.append_assoc,List.cons_append]) (by
          have lt : pre.length < (Frames.edges (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)).length := by
            simp only [Bool.false_eq_true,ite_false] at split
            rw [split]
            simp
          simpa only [invocationRegister,if_pos lt,phaseRegisters_compile,Bool.false_eq_true,ite_false] using aligned))
  · exact invocationPhase_host owner body true ready moveTime ((stageChildStart n + runChildStart (r,d)) + ((Frames.edges (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)).filter positiveMove).length) gates
      (fun j pre p post split aligned => by
        have step := moveAt j (Frames.edges (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs) ++ pre) p post (by
        simp only [ite_true] at split
        unfold Geometry.Moves.phaseEdges
        rw [split,List.append_assoc]) (by
          have right (a b : ℕ) : ¬ a+b < a := by omega
          have offset (a b : ℕ) : a+b-a = b := by omega
          simpa only [invocationRegister,List.length_append,if_neg (right _ _),offset,
            ite_true,phaseRegisters_compile] using aligned)
        simpa only [List.filter_append,List.length_append,Nat.add_assoc] using step)

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- One class invocation executes the two literal phases around the nine COPY
lifecycles and returns the selected register action at every cover label. -/
theorem invocation_host
    (n : Fin 9) (r : Fin 32) (d : Fin 5) :
    ∃ gateStates : ℕ, ∀ (tapes : Option (Fin Copy.lifecycles.length) → ℕ)
      (ports : ∀ i, Fin (142081+2) ↪ Fin (tapes i)),
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ (shared : Stacks (142081+2) prime) (initial : ∀ i, Stacks (tapes i) prime),
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    (∀ i l, (∀ j, ports i j ≠ l) →
      prepared.L (bank i l) = (initial i).L l ∧ prepared.R (bank i l) = (initial i).R l) ∧
    let region := fun i k => ∃ l, (∀ j, ports i j ≠ l) ∧ bank i l = k
    let workspace := fun i => region (some i)
    ∀ {w B K : ℕ} {P U : Type} (Q : ℕ), gateStates ≤ Q →
    ∀ localBody : ∀ i, P → Pr P (tapes i) Q prime U,
    let proc := fun (i : Option (Fin Copy.lifecycles.length)) (f : P) => (i,f)
    let body := fun f : Option (Fin Copy.lifecycles.length) × P =>
      embProg (bank f.1) (proc f.1) (localBody f.1 f.2)
    let W := B*prime^(64*((w+1)*64))*K
    let V := (prime^(w+1))^16*W
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let view := fun (x : Fin 142081 → Fin V → ZMod 2) k t => x k (Fin.cast (copyLabel_volume (w+1) B K) t)
    let gateTime := fun g : Circuit.Gate ℕ (ZMod 2) => 76*g.terms.length*V*(142081+7)+6
    0 < V → ∀ (moveWork : ℕ → ℕ) (copyWork : Fin Copy.lifecycles.length → ℕ) (childTime : ℕ → ℕ),
    let start := stageChildStart n + runChildStart (r,d)
    let moveTime := fun i (_ : ℕ × ℕ) => moveWork i + childTime i
    let copyTime := fun j => copyWork j + childTime (copyChildPosition (n,(r,d),j)).val
    let represented := fun {t : ℕ} (e : Fin (142081+2) ↪ Fin t) (data : Fin 142081 → Fin V → ZMod 2) (S : Stacks t prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded data) (FlatCoordinateSchedule.bits V)) (embStk e S).L (embStk e S).R
    let copyReady := represented fan
    let saved := fun (region : Fin T → Prop) (S : Stacks T prime) =>
      ∀ k, region k → S.L k = prepared.L k ∧ S.R k = prepared.R k
    ∀ stock : Stacks (tapes none) prime → Prop, stock (initial none) →
    (∀ S F, stock S → (∀ l, (∀ h, ports none h ≠ l) → F.L l = S.L l ∧ F.R l = S.R l) → stock F) →
    let phaseReady := fun data (S : Stacks (tapes none) prime) => represented (ports none) data S ∧ stock S
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    (∀ i : Fin edges.length,
      let p := edges[i.val]'i.isLt
      let child := phaseChildPositions.choose (n,(r,d),i)
      let j := paidRegister i.val
      ∃ code, ∀ data u S, phaseReady data S → ∃ z F t y,
        Exec (localBody none) code (mk u S) t (mk z F) ∧ t ≤ moveTime child.val p ∧ z.user = u.user ∧
        phaseReady (Function.update data (owner j) y) F ∧ ∀ s l,
          y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) p) s)) l) =
            data (owner j) (index (AffineFieldCoordinates.embed s) l)) →
    (∀ j, ∃ code, ∀ data u S, represented (ports (some j)) data S →
      (∀ l, (∀ h, ports (some j) h ≠ l) →
        S.L l = (initial (some j)).L l ∧ S.R l = (initial (some j)).R l) →
      ∃ z F t out, Exec (localBody (some j)) code (mk u S) t (mk z F) ∧ t ≤ copyTime j ∧
        z.user = u.user ∧ represented (ports (some j)) out F ∧
        CopyWindowEffect n r d Copy.lifecycles[j.val] (w+1) B K (view data) (view out)) →
    ∃ code, ∀ data u S, copyReady data S → (∀ i, saved (region i) S) → ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
      t ≤ ((sectionD++sectionA++(sectionB++sectionC)).map (fun g => gateTime g.toCircuit)).sum +
        ((List.range' start (Geometry.Moves.phaseEdges.filter positiveMove).length).map moveWork).sum + (List.ofFn copyWork).sum +
        ((List.range' start Geometry.Moves.localPaid.length).map childTime).sum+3 ∧ z.user = u.user ∧ copyReady out F ∧ stock (embStk (bank none) F) ∧
        InvocationEffect n r d (w+1) B K data out := by
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
  obtain ⟨states,gateRuns⟩ := scheduledGates_host owner
  refine ⟨states,?_⟩
  intro tapes ports
  obtain ⟨T,fan,bank,selected,collect,off⟩ := copyWindowBanks tapes ports
  refine ⟨T,fan,bank,selected,?_⟩
  intro shared initial
  obtain ⟨prepared,base,localInit⟩ := collect shared initial
  refine ⟨prepared,base,localInit,?_⟩
  intro region workspace
  intro w B K P U Q capacity localBody proc body W V _ view gateTime pos moveWork copyWork childTime start moveTime copyTime represented copyReady saved stock stockInit frame phaseReady paidEdges moves copies
  have gates := gateRuns capacity pos (ports none) (localBody none) stock frame
  have outside (i j) (ne : i ≠ j) (k) (h : region i k) : ∀ l, bank j l ≠ k := by
    obtain ⟨l,hl,rfl⟩ := h
    exact (off i l hl).2 j ne.symm
  have phases := scheduledScalarPhase_host n r d (localBody none) phaseReady moveTime gates moves
  obtain ⟨left,enter⟩ := phases false
  obtain ⟨right,leave⟩ := phases true
  have project (i) (S : Stacks T prime) : embStk (ports i) (embStk (bank i) S) = embStk fan S := by
    simp only [embStk,Function.comp_def,selected]
  have phase (data S) : phaseReady data (embStk (bank none) S) ↔ copyReady data S ∧ stock (embStk (bank none) S) := by
    simp only [phaseReady,represented,copyReady,project]
  have scatter (ls : List (Fin Copy.lifecycles.length)) (unique : ls.Nodup) :
      ∃ code, ∀ data u S, copyReady data S → stock (embStk (bank none) S) →
        (∀ i ∈ ls, saved (workspace i) S) → ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
        t ≤ (ls.map copyTime).sum+1 ∧ z.user = u.user ∧ copyReady out F ∧ stock (embStk (bank none) F) ∧
          CopyScheduleEffect n r d (w+1) B K (ls.map fun j => Copy.lifecycles[j.val]'j.isLt) (view data) (view out) := by
    induction ls with
    | nil => exact ⟨.act .done,fun x u S ok guard _ => ⟨u,S,1,x,Exec.act _ _,by simp,rfl,ok,guard,rfl⟩⟩
    | cons l ls ih =>
      obtain ⟨head,step⟩ := copies l
      obtain ⟨tail,finish⟩ := ih (List.nodup_cons.mp unique).2
      refine ⟨(embProg (bank (some l)) (proc (some l)) head).seq tail,?_⟩
      intro x u S ok guard fresh
      obtain ⟨v₀,D₀,t,y,run,ha,user₀,rep,act⟩ := step x (embDn (bank (some l)) u) (embStk (bank (some l)) S)
        (by simpa only [represented,project,copyReady] using ok) (by
        intro m hm
        obtain ⟨a,b⟩ := fresh l List.mem_cons_self (bank (some l) m) ⟨m,hm,rfl⟩
        obtain ⟨c,d⟩ := localInit (some l) m hm
        exact ⟨a.trans c,b.trans d⟩)
      obtain ⟨v,D,a,_,user,placed,off⟩ := exec_emb (ι := proc (some l)) (body' := body)
        (bank (some l)).injective (fun _ => rfl) run u rfl S rfl
      have same : v.user = u.user := user.trans user₀
      have mid : copyReady y D := by
        rw [← placed] at rep
        simpa only [represented,project,copyReady] using rep
      obtain ⟨z,F,m,out,b,hb,user,done,safe,rest⟩ := finish y v D mid (by
        exact frame _ _ guard (fun k hk => off (bank none k) (outside none (some l) (by simp) _ ⟨k,hk,rfl⟩))) (by
        intro i member k used
        have ne : i ≠ l := fun eq => (List.nodup_cons.mp unique).1 (eq ▸ member)
        obtain ⟨ld,rd⟩ := off k (outside (some i) (some l) (by simpa using ne) k used)
        obtain ⟨ls,rs⟩ := fresh i (List.mem_cons_of_mem _ member) k used
        exact ⟨ld.trans ls,rd.trans rs⟩)
      refine ⟨z,F,_,out,Exec.seq a b,?_,user.trans same,done,safe,view y,act,rest⟩
      simp only [List.map_cons,List.sum_cons]
      omega
  obtain ⟨middle,window⟩ := scatter (List.finRange Copy.lifecycles.length) (List.nodup_finRange _)
  rw [← List.ofFn_eq_map,← List.ofFn_eq_map,List.ofFn_getElem] at window
  refine ⟨(embProg (bank none) (proc none) left).seq (middle.seq (embProg (bank none) (proc none) right)),?_⟩
  intro x u S ok fresh
  obtain ⟨v₀,D₀,a,y,first₀,ha,ua,mid,offA,readA⟩ := enter x (embDn (bank none) u) (embStk (bank none) S)
    ((phase _ _).2 ⟨ok,by
      apply frame _ _ stockInit
      intro k hk
      obtain ⟨a,b⟩ := fresh none (bank none k) ⟨k,hk,rfl⟩
      obtain ⟨c,d⟩ := localInit none k hk
      exact ⟨a.trans c,b.trans d⟩⟩)
  obtain ⟨v,D,first,_,uv,vd,offD⟩ := exec_emb (ι := proc none) (body' := body)
    (bank none).injective (fun _ => rfl) first₀ u rfl S rfl
  rw [← vd] at mid
  obtain ⟨live,guard⟩ := (phase _ _).1 mid
  obtain ⟨h,G,b,z,copy,hb,ub,placed,safe,effect⟩ := window y v D live guard (by
    intro i _ k hk
    obtain ⟨a,b⟩ := offD k (outside (some i) none (by simp) k hk)
    obtain ⟨c,d⟩ := fresh (some i) k hk
    exact ⟨a.trans c,b.trans d⟩)
  obtain ⟨q₀,F₀,c,out,last₀,hc,uc,done,offB,readB⟩ := leave z (embDn (bank none) h) (embStk (bank none) G)
    ((phase _ _).2 ⟨placed,safe⟩)
  obtain ⟨q,F,last,_,uq,qf,_⟩ := exec_emb (ι := proc none) (body' := body)
    (bank none).injective (fun _ => rfl) last₀ h rfl G rfl
  rw [← qf] at done
  obtain ⟨result,restored⟩ := (phase _ _).1 done
  refine ⟨q,F,_,out,Exec.seq first (Exec.seq copy last),?_,uq.trans (uc.trans (ub.trans (uv.trans ua))),result,restored,?_,?_⟩
  · change a ≤ ((sectionD++sectionA).map (fun g => gateTime g.toCircuit)).sum+_+1 at ha
    change c ≤ ((sectionB++sectionC).map (fun g => gateTime g.toCircuit)).sum+_+1 at hc
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    have count : edges.length = (Geometry.Moves.phaseValues.filter (· ≠ 0)).length := by
      rw [← Geometry.Moves.phase_ranks,List.filter_map,List.length_map]
      have h : positiveMove = fun p => decide (Geometry.moveRank p.1 p.2 ≠ 0) := by
        funext p
        simp [positiveMove,bne,BEq.beq]
      change (Geometry.Moves.phaseEdges.filter positiveMove).length = _
      rw [h]
      rfl
    have total : Geometry.Moves.localPaid.length = edges.length + Copy.lifecycles.length := by
      rw [Geometry.Moves.localPaid,List.length_append,Geometry.Moves.phase_ranks,Geometry.Moves.copyRanks_eq,
        List.length_replicate,Copy.copy_count,count]
    have copiesCost : (List.ofFn copyTime).sum = (List.ofFn copyWork).sum +
        ((List.range' (start+edges.length) Copy.lifecycles.length).map childTime).sum := by
      have eq (j : Fin Copy.lifecycles.length) : copyTime j = copyWork j + childTime (start+edges.length+j.val) := by
        simp only [copyTime,copyChildPosition_offset,start,count,Nat.add_assoc]
      rw [show copyTime = _ from funext eq]
      exact windowBill_split copyWork childTime (start+edges.length)
    have moveCost := indexedBill_split moveWork childTime edges start
    change indexedBill moveTime start edges = _ at moveCost
    rw [total,← List.range'_append_1,List.map_append,List.sum_append]
    rw [copiesCost] at hb
    simp only [edges,start,Geometry.Moves.phaseEdges,List.filter_append,indexedBill_append,List.map_append,
      List.sum_append,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at moveCost ha hb hc ⊢
    omega
  · intro g cell
    change phaseRead owner out (labelSpectator g cell) = _
    rw [readB,labelScatter_read y z effect g cell]
    exact congrArg (fun bank => labelPhase (w+1) (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)
      (labelScatter n bank g)) (funext (fun h => readA (labelSpectator h cell)))
  · intro i live outside
    have kept := copySchedule_other effect i live outside
    refine (offB i outside).trans (Eq.trans ?_ (offA i outside))
    funext t
    exact congrFun kept (Fin.cast (copyLabel_volume (w+1) B K).symm t)

open Cover.Fallback RecursiveInterchangeLayout in
/-- The recursive call transposes the packed child record and restores its scratch and private tapes. -/
def ScheduledChildExec [M8.Machine.Net] {P U : Type} {T Q : ℕ} (node desc : Descriptor) (w W : ℕ)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (record : List (Fin (prime+4)))
    (position : Fin (volume prime desc) ≃ Fin ((prime^(w+1))^16*W))
    (body : P → Pr P T Q prime U) (f : P) (budget : ℕ) : Prop :=
  let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
  let M := prime^(w+1)
  let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
    SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
  let clean := fun (D : Stacks T prime) => ∀ l : Fin (rowSwapBlock.tapes+35), 35 ≤ l.val →
    D.L (ports l) = [] ∧ D.R (ports l) = []
  desc.width < node.width → ∀ u D word, stored word D → clean D →
    ∃ z F t changed, Exec body (body f) (mk u D) t (mk z F) ∧ t ≤ budget ∧ z.user = u.user ∧
      stored changed F ∧ clean F ∧ (∀ j, (∀ l, ports l ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
      ∀ h, changed (position h) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (word ∘ position) h

open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Run a class invocation with its allocated MOVE machines. Both MOVE and COPY
use the caller’s recursive execution at their scheduled child positions. -/
def AllocatedInvocation [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) : Prop :=
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    let child := fun i : I => phaseChildPositions.choose (n,(r,d),i)
    ∃ (moveTapes : I → ℕ) (regsPort : ∀ i, Fin (rowSwapBlock.tapes+35) ↪ Fin (moveTapes i))
      (phaseT states : ℕ) (phaseFan : Fin (142081+2) ↪ Fin phaseT) (moveBank : ∀ i, Fin (moveTapes i) ↪ Fin phaseT),
    ∃ (copyTapes : J → ℕ) (copyPorts : ∀ j, Fin (142081+2) ↪ Fin (copyTapes j))
      (copyRegs : ∀ j, Fin (rowSwapBlock.tapes+35) ↪ Fin (copyTapes j)),
    let tapes := fun i : Option J => i.elim phaseT copyTapes
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ h, bank none (phaseFan h) = fan h) ∧
    (∀ j h, bank (some j) (copyPorts j h) = fan h) ∧
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (localMove : ∀ i, P → Pr P (moveTapes i) Q prime U) (f : I → P)
      (localCopy : ∀ j, I × P → Pr (I × P) (copyTapes j) Q prime U) (copyProc : J → I × P),
    let moveBody := fun g : I × P => embProg (moveBank g.1) (fun h => (g.1,h)) (localMove g.1 g.2)
    let localBody : ∀ i, I × P → Pr (I × P) (tapes i) Q prime U :=
      Option.rec (motive := fun i => I × P → Pr (I × P) (tapes i) Q prime U) moveBody localCopy
    let body := fun g : Option J × (I × P) => embProg (bank g.1) (fun h => (g.1,h)) (localBody g.1 g.2)
    ∃ (base swaps : I → ℕ) (copyBase copySwaps copyLeaf copyFixed : J → ℕ), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    let V := M^16*W
    0 < W → ∀ (record : I → List (Fin (prime+4))) (copyRecord : J → List (Fin (prime+4))),
    let desc := fun i => scheduledChild prime node (child i)
    ∃ position : ∀ i, Fin (volume prime (desc i)) ≃ Fin V,
    (∀ i h, (position i h).val = (CopyChildLayout.packActive (desc i) h).val) ∧
    let copyChild := fun j : J => copyChildPosition (n,(r,d),j)
    let copyDesc := fun j => scheduledChild prime node (copyChild j)
    ∃ copyPosition : ∀ j, Fin (volume prime (copyDesc j)) ≃ Fin V,
    (∀ j h, (copyPosition j h).val = (CopyChildLayout.packActive (copyDesc j) h).val) ∧
    ∀ childTime : ℕ → ℕ,
    (∀ i, ScheduledChildExec node (desc i) w W (regsPort i) (record i) (position i)
      (localMove i) (f i) (childTime (child i).val)) →
    (∀ i, ScheduledChildExec node (copyDesc i) w W (copyRegs i) (copyRecord i) (copyPosition i)
      (localCopy i) (copyProc i) (childTime (copyChild i).val)) →
    ∀ shared : Stacks (142081+2) prime,
    let represented := fun {t : ℕ} (e : Fin (142081+2) ↪ Fin t) (data : Fin 142081 → Fin V → ZMod 2) (S : Stacks t prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded data) (FlatCoordinateSchedule.bits V)) (embStk e S).L (embStk e S).R
    let copyWork := fun j => (copyBase j+copySwaps j*swapVolumeRate w)*V +
      copyLeaf j * M8.RevMachine.LeafCore.coreCost V ((w+1)*64) + copyFixed j
    let start := stageChildStart n + runChildStart (r,d)
    let work := fun (j : ℕ) => if h : j-start < edges.length then
      (base ⟨j-start,h⟩ + swaps ⟨j-start,h⟩ * swapVolumeRate w)*V else 0
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    ∃ code, ∀ data u S, represented fan data S →
      (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
      ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
      t ≤ ((sectionD++sectionA++(sectionB++sectionC)).map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum +
        ((List.range' start edges.length).map work).sum + (List.ofFn copyWork).sum +
        ((List.range' start Geometry.Moves.localPaid.length).map childTime).sum+3 ∧ z.user = u.user ∧
        represented fan out F ∧ InvocationEffect n r d (w+1) B K data out

open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
theorem allocatedInvocation_host [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) :
    AllocatedInvocation n r d := by
  classical
  unfold AllocatedInvocation
  intro edges I J child
  obtain ⟨mt,phaseT,mq,regs,pfan,mbank,machine⟩ := scheduledMoves_host n (r,d)
  obtain ⟨gq,layout⟩ := invocation_host n r d
  choose ct cq cr cp copyMachine using fun j : J => scheduledCopyWindow_host n r d j
  let states := max (max mq gq) (Finset.univ.sup cq)
  refine ⟨mt,regs,phaseT,states,pfan,mbank,ct,cp,cr,?_⟩
  intro tapes
  let ports : ∀ i, Fin (142081+2) ↪ Fin (tapes i) := Option.rec (motive := fun i => Fin (142081+2) ↪ Fin (tapes i)) pfan cp
  obtain ⟨T,fan,bank,selected,place⟩ := layout tapes ports
  refine ⟨T,fan,bank,selected none,fun j => selected (some j),?_⟩
  intro P U Q fits localMove f localCopy copyProc moveBody localBody body
  have common : max mq gq ≤ Q := (le_max_left ..).trans fits
  obtain ⟨base,swaps,run⟩ := machine ((le_max_left ..).trans common) localMove f
  have fitsCopy (j : J) : cq j ≤ Q :=
    (Finset.le_sup (Finset.mem_univ j)).trans ((le_max_right ..).trans fits)
  choose cb cs cl cf copyRun using fun j => copyMachine j (fitsCopy j) (localCopy j) (copyProc j)
  refine ⟨base,swaps,cb,cs,cl,cf,?_⟩
  intro node w B rows width split label M K W V pos record copyRecord desc
  obtain ⟨position,stock,coords,seed,frame,moves⟩ := run node w B rows width split label pos record
  refine ⟨position,coords,?_⟩
  intro copyChild copyDesc
  choose copyPosition copyCoords window using fun j => copyRun j node w B rows width split label pos
  refine ⟨copyPosition,copyCoords,?_⟩
  intro childTime recurse copyRecurse shared represented copyWork start work
  choose initial windowRun using fun j => window j (copyRecord j)
  obtain ⟨phaseInit,_,ready⟩ := seed shared
  let init : ∀ i, Stacks (tapes i) prime := Option.rec (motive := fun i => Stacks (tapes i) prime) phaseInit initial
  obtain ⟨prepared,sharedView,_,assemble⟩ := place shared init
  refine ⟨prepared,sharedView,?_⟩
  have size : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
  obtain ⟨code,execute⟩ := assemble (w := w) (B := B) (K := K) Q ((le_max_right ..).trans common)
    localBody size work copyWork childTime stock ready frame (by
      intro i
      obtain ⟨code,step⟩ := moves i
      refine ⟨code,?_⟩
      intro data u S ok
      obtain ⟨z,F,t,y,exec,time,user,out,guard,reads⟩ := step (childTime (child i).val) (recurse i) data u S ok.1 ok.2
      have atChild : (child i).val - start = i.val := by
        rw [(phaseChildPositions.choose_spec n (r,d) i).2]
        dsimp only [start]
        omega
      refine ⟨z,F,t,y,exec,?_,user,⟨out,guard⟩,reads⟩
      change t ≤ work (child i).val + childTime (child i).val
      have valid : i.val < edges.length := i.isLt
      simp only [work,atChild,dif_pos valid]
      exact time.trans_eq (Nat.add_comm _ _)) (fun j => windowRun j (childTime (copyChild j).val) (copyRecurse j))
  refine ⟨code,?_⟩
  intro data u S live fresh
  obtain ⟨z,F,t,out,exec,time,user,result,_,effect⟩ := execute data u S live (by
    intro i k used
    obtain ⟨l,privatePort,rfl⟩ := used
    apply fresh
    intro h eq
    exact privatePort h ((bank i).injective ((selected i h).trans eq)))
  exact ⟨z,F,t,out,exec,time,user,result,effect⟩

/-- Sequence local machines with shared owner tapes in schedule order. A later
machine sees its own initialized private tapes and the preceding owner's result. -/
theorem scheduledBanks_exec {I : Type} [Fintype I] {k : ℕ}
    (tapes : I → ℕ) (ports : ∀ i, Fin k ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin k ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ {X P U : Type} {Q : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U) (code : ∀ i, Pr P (tapes i) Q prime U)
      (represented : X → Stacks k prime → Prop) (effect : I → X → X → Prop)
      (cost : I → ℕ) (initial : ∀ i, Stacks (tapes i) prime) (shared : Stacks k prime),
    (∀ i x u S, represented x (embStk (ports i) S) →
      (∀ l, (∀ j, ports i j ≠ l) → S.L l = (initial i).L l ∧ S.R l = (initial i).R l) →
      ∃ v D t y, Exec (body i) (code i) (mk u S) t (mk v D) ∧ t ≤ cost i ∧ v.user = u.user ∧
        represented y (embStk (ports i) D) ∧ effect i x y) →
    let table := fun g : I × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    let placed := fun i => embProg (bank i) (Prod.mk i) (code i)
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    ∀ (order : List I), order.Nodup → ∀ x u S, represented x (embStk fan S) →
      (∀ l, (∀ j, fan j ≠ l) → S.L l = prepared.L l ∧ S.R l = prepared.R l) →
      ∃ v D t y, Exec table (Prog.seqList (order.map placed)) (mk u S) t (mk v D) ∧
        t ≤ (order.map cost).sum+1 ∧ v.user = u.user ∧ represented y (embStk fan D) ∧
        order.foldr (fun i next a => ∃ b, effect i a b ∧ next b) (fun a => a = y) x := by
  obtain ⟨T,fan,bank,selected,prepare,off⟩ := copyWindowBanks tapes ports
  refine ⟨T,fan,bank,selected,?_⟩
  intro X P U Q body code represented effect cost initial shared run table placed
  obtain ⟨prepared,owners,stock⟩ := prepare shared initial
  refine ⟨prepared,owners,?_⟩
  let fresh := fun i (S : Stacks T prime) => ∀ l, (∀ j, ports i j ≠ l) →
    S.L (bank i l) = (initial i).L l ∧ S.R (bank i l) = (initial i).R l
  have project (i) (S : Stacks T prime) : embStk (ports i) (embStk (bank i) S) = embStk fan S := by
    simp only [embStk,Function.comp_def,selected]
  intro order unique x u S ready saved
  have frames : ∀ i ∈ order, fresh i S := by
    intro i _ l privateSlot
    obtain ⟨a,b⟩ := saved _ (off i l privateSlot).1
    obtain ⟨c,d⟩ := stock i l privateSlot
    exact ⟨a.trans c,b.trans d⟩
  clear saved
  induction order generalizing x S u with
  | nil => exact ⟨u,S,1,x,Exec.act .done _,by simp,rfl,ready,rfl⟩
  | cons i rest ih =>
    obtain ⟨v,D,t,y,exec,time,user,mid,act⟩ := run i x (embDn (bank i) u) (embStk (bank i) S)
      ((project i S) ▸ ready) (frames i List.mem_cons_self)
    obtain ⟨z,F,first,_,same,view,untouched⟩ := exec_emb (ι := Prod.mk i) (body' := table)
      (bank i).injective (fun _ => rfl) exec u rfl S rfl
    rw [← view,project] at mid
    obtain ⟨v',D',t',y',last,bill,final,out,acts⟩ := ih (List.nodup_cons.mp unique).2 y z F mid (by
      intro j member l privateSlot
      have ne : i ≠ j := fun eq => (List.nodup_cons.mp unique).1 (eq ▸ member)
      obtain ⟨a,b⟩ := untouched _ ((off j l privateSlot).2 i ne)
      obtain ⟨c,d⟩ := frames j (List.mem_cons_of_mem _ member) l privateSlot
      exact ⟨a.trans c,b.trans d⟩)
    refine ⟨v',D',_,y',Exec.seq first last,?_,final.trans (same.trans user),out,y,act,acts⟩
    simp only [List.map_cons,List.sum_cons]
    omega

theorem scheduledChildBill {I : Type} [BEq I] [LawfulBEq I] (entries : I → List ℕ)
    (childTime : ℕ → ℕ) (order : List I) (distinct : order.Nodup) (start : ℕ) :
    (order.map fun i => ((List.range' (start+((order.take (order.idxOf i)).flatMap entries).length)
      (entries i).length).map childTime).sum).sum =
      ((List.range' start (order.flatMap entries).length).map childTime).sum := by
  induction order generalizing start with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
    simp only [List.map_cons,List.idxOf_cons_self,List.take_zero,List.flatMap_nil,List.length_nil,
      Nat.add_zero,List.sum_cons,List.flatMap_cons,List.length_append,← List.range'_append_1,
      List.map_append,List.sum_append]
    congr 1
    rw [← ih tail (start+(entries i).length)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j member
    have ne : i ≠ j := fun eq => fresh (eq ▸ member)
    simp only [List.idxOf_cons_ne _ ne,List.take_succ_cons,List.flatMap_cons,List.length_append,Nat.add_assoc]

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- The stage runs share the owner bank. Their recursive costs cover the
single consecutive interval of children beginning at this stage's offset. -/
theorem stageInvocations_host (n : Fin 9) (tapes : Fin 32 × Fin 5 → ℕ)
    (ports : ∀ i, Fin (142081+2) ↪ Fin (tapes i)) :
    ∃ (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ {P U : Type} {Q w B K : ℕ} (body : ∀ i, P → Pr P (tapes i) Q prime U)
      (code : ∀ i, Pr P (tapes i) Q prime U) (localCost : Fin 32 × Fin 5 → ℕ) (childTime : ℕ → ℕ)
      (initial : ∀ i, Stacks (tapes i) prime) (shared : Stacks (142081+2) prime),
    let V := (prime^w)^16*(B*prime^(64*(w*64))*K)
    let ready := fun (x : Fin 142081 → Fin V → ZMod 2) (S : Stacks (142081+2) prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded x) (FlatCoordinateSchedule.bits V)) S.L S.R
    (∀ i x u S, ready x (embStk (ports i) S) →
      (∀ l, (∀ j, ports i j ≠ l) → S.L l = (initial i).L l ∧ S.R l = (initial i).R l) →
      ∃ v D t y, Exec (body i) (code i) (mk u S) t (mk v D) ∧
        t ≤ localCost i + ((List.range' (stageChildStart n+runChildStart i) Geometry.Moves.localPaid.length).map childTime).sum ∧
        v.user = u.user ∧ ready y (embStk (ports i) D) ∧ InvocationEffect n i.1 i.2 w B K x y) →
    let table := fun g : (Fin 32 × Fin 5) × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    let placed := fun i => embProg (bank i) (Prod.mk i) (code i)
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    ∀ x u S, ready x (embStk fan S) →
      (∀ l, (∀ j, fan j ≠ l) → S.L l = prepared.L l ∧ S.R l = prepared.R l) →
      ∃ v D t y, Exec table (Prog.seqList (stageRuns.map placed)) (mk u S) t (mk v D) ∧
        t ≤ (stageRuns.map localCost).sum +
          ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1 ∧
        v.user = u.user ∧ ready y (embStk fan D) ∧
        stageRuns.foldr (fun i next a => ∃ b, InvocationEffect n i.1 i.2 w B K a b ∧ next b) (fun a => a = y) x := by
  obtain ⟨T,fan,bank,selected,build⟩ := scheduledBanks_exec tapes ports
  refine ⟨T,fan,bank,selected,?_⟩
  intro P U Q w B K body code localCost childTime initial shared V ready run table placed
  let bill := fun i => ((List.range' (stageChildStart n+runChildStart i) Geometry.Moves.localPaid.length).map childTime).sum
  obtain ⟨prepared,owners,execute⟩ := build body code ready (fun i => InvocationEffect n i.1 i.2 w B K)
    (fun i => localCost i + bill i) initial shared run
  refine ⟨prepared,owners,?_⟩
  intro x u S live fresh
  obtain ⟨v,D,t,y,exec,time,user,out,acts⟩ := execute stageRuns stageRuns_nodup x u S live fresh
  refine ⟨v,D,t,y,exec,?_,user,out,acts⟩
  have split (ls : List (Fin 32 × Fin 5)) :
      (ls.map fun i => localCost i + bill i).sum = (ls.map localCost).sum + (ls.map bill).sum := by
    induction ls with
    | nil => rfl
    | cons i rest ih => simp only [List.map_cons,List.sum_cons,ih]; omega
  rw [split,show (stageRuns.map bill).sum = _ from scheduledChildBill (fun _ => Geometry.Moves.localPaid)
    childTime stageRuns stageRuns_nodup (stageChildStart n)] at time
  exact time

open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Execute the physical class invocations in stage order, with a single bill for their recursive children. -/
def AllocatedStage [M8.Machine.Net] (n : Fin 9) : Prop :=
    let edges := Geometry.Moves.phaseEdges.filter positiveMove
    let R := Fin 32 × Fin 5
    let I := Fin edges.length
    let J := Fin Copy.lifecycles.length
    let child := fun (k : R) (i : I) => phaseChildPositions.choose (n,k,i)
    ∃ (moveTapes : R → I → ℕ) (regsPort : ∀ k i, Fin (rowSwapBlock.tapes+35) ↪ Fin (moveTapes k i))
      (phaseT : R → ℕ) (states : ℕ) (moveBank : ∀ k i, Fin (moveTapes k i) ↪ Fin (phaseT k))
      (copyTapes : R → J → ℕ) (copyRegs : ∀ k j, Fin (rowSwapBlock.tapes+35) ↪ Fin (copyTapes k j)),
    let tapes := fun k (i : Option J) => i.elim (phaseT k) (copyTapes k)
    ∃ (runT : R → ℕ) (bank : ∀ k i, Fin (tapes k i) ↪ Fin (runT k))
      (T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (runBank : ∀ k, Fin (runT k) ↪ Fin T),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (localMove : ∀ k i, P → Pr P (moveTapes k i) Q prime U) (f : R → I → P)
      (localCopy : ∀ k j, I × P → Pr (I × P) (copyTapes k j) Q prime U) (copyProc : R → J → I × P),
    let moveBody := fun k (g : I × P) => embProg (moveBank k g.1) (fun h => (g.1,h)) (localMove k g.1 g.2)
    let localBody := fun k => Option.rec (motive := fun i => I × P → Pr (I × P) (tapes k i) Q prime U)
      (moveBody k) (localCopy k)
    let runBody := fun k (g : Option J × (I × P)) => embProg (bank k g.1) (fun h => (g.1,h)) (localBody k g.1 g.2)
    let body := fun g : R × (Option J × (I × P)) => embProg (runBank g.1) (Prod.mk g.1) (runBody g.1 g.2)
    ∃ (base swaps : R → I → ℕ) (copyBase copySwaps copyLeaf copyFixed : R → J → ℕ), ∀ (node : Descriptor) (w B rows : ℕ),
    node.width = 64*(w+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((w+1)*64)) →
    let M := prime^(w+1)
    let K := M^112*(node.beforeRows*rows*node.between*node.afterD)
    let W := B*prime^(64*((w+1)*64))*K
    let V := M^16*W
    ∀ pos : 0 < W, ∀ (record : R → I → List (Fin (prime+4))) (copyRecord : R → J → List (Fin (prime+4))),
    let desc := fun k i => scheduledChild prime node (child k i)
    ∃ position : ∀ k i, Fin (volume prime (desc k i)) ≃ Fin V,
    (∀ k i h, (position k i h).val = (CopyChildLayout.packActive (desc k i) h).val) ∧
    let copyChild := fun (k : R) (j : J) => copyChildPosition (n,k,j)
    let copyDesc := fun k j => scheduledChild prime node (copyChild k j)
    ∃ copyPosition : ∀ k j, Fin (volume prime (copyDesc k j)) ≃ Fin V,
    (∀ k j h, (copyPosition k j h).val = (CopyChildLayout.packActive (copyDesc k j) h).val) ∧
    ∀ childTime : ℕ → ℕ,
    (∀ k i, ScheduledChildExec node (desc k i) w W (regsPort k i) (record k i) (position k i)
      (localMove k i) (f k i) (childTime (child k i).val)) →
    (∀ k i, ScheduledChildExec node (copyDesc k i) w W (copyRegs k i) (copyRecord k i) (copyPosition k i)
      (localCopy k i) (copyProc k i) (childTime (copyChild k i).val)) →
    ∀ shared : Stacks (142081+2) prime,
    let represented := fun {t : ℕ} (e : Fin (142081+2) ↪ Fin t) (data : Fin 142081 → Fin V → ZMod 2) (S : Stacks t prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded data) (FlatCoordinateSchedule.bits V)) (embStk e S).L (embStk e S).R
    let copyWork := fun k j => (copyBase k j+copySwaps k j*swapVolumeRate w)*V +
      copyLeaf k j * M8.RevMachine.LeafCore.coreCost V ((w+1)*64) + copyFixed k j
    let start := fun k => stageChildStart n + runChildStart k
    let work := fun k (j : ℕ) => if h : j-start k < edges.length then
      (base k ⟨j-start k,h⟩ + swaps k ⟨j-start k,h⟩ * swapVolumeRate w)*V else 0
    let localCost := fun k => ((sectionD++sectionA++(sectionB++sectionC)).map (fun g => 76*g.toCircuit.terms.length*V*(142081+7)+6)).sum +
      ((List.range' (start k) edges.length).map (work k)).sum + (List.ofFn (copyWork k)).sum + 3
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧
    ∃ code, ∀ data u S, represented fan data S →
      (∀ k, (∀ h, fan h ≠ k) → S.L k = prepared.L k ∧ S.R k = prepared.R k) →
      ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
      t ≤ (stageRuns.map localCost).sum +
        ((List.range' (stageChildStart n) (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum+1 ∧
        z.user = u.user ∧ represented fan out F ∧
        stageRuns.foldr (fun k next x => ∃ y, InvocationEffect n k.1 k.2 (w+1) B K x y ∧ next y) (fun x => x = out) data ∧
        ∀ i, i ≠ Fin.last 142080 → out i = (referenceStage n (Nat.succ_pos w)
          (Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right pos)) (Nat.pos_of_mul_pos_left pos)).transform data i

open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
theorem allocatedStage_host [M8.Machine.Net] (n : Fin 9) : AllocatedStage n := by
  classical
  unfold AllocatedStage
  intro edges R I J child
  choose mt regs phaseT qs phaseFan mb ct cp cr runT rf bank phaseShared copyShared run using
    fun k : R => allocatedInvocation_host n k.1 k.2
  obtain ⟨T,fan,runBank,_,stage⟩ := stageInvocations_host n runT rf
  refine ⟨mt,regs,phaseT,Finset.univ.sup qs,mb,ct,cr,?_⟩
  intro tapes
  refine ⟨runT,bank,T,fan,runBank,?_⟩
  intro P U Q fits localMove f localCopy copyProc moveBody localBody runBody body
  have capacity (k : R) : qs k ≤ Q := (Finset.le_sup (Finset.mem_univ k)).trans fits
  choose base swaps cb cs cl cf invoke using fun k =>
    run k (capacity k) (localMove k) (f k) (localCopy k) (copyProc k)
  refine ⟨base,swaps,cb,cs,cl,cf,?_⟩
  intro node w B rows width split label M K W V pos record copyRecord desc
  choose position coords copyPosition copyCoords ready using fun k =>
    invoke k node w B rows width split label pos (record k) (copyRecord k)
  refine ⟨position,coords,?_⟩
  intro copyChild copyDesc
  refine ⟨copyPosition,copyCoords,?_⟩
  intro childTime recurse copyRecurse shared represented copyWork start work localCost
  choose initial owner code execute using fun k => ready k childTime (recurse k) (copyRecurse k) shared
  obtain ⟨prepared,owners,runStage⟩ := stage (w := w+1) (B := B) (K := K) runBody code localCost childTime initial shared (by
    intro k x u S live fresh
    obtain ⟨v,D,t,y,exec,time,user,out,act⟩ := execute k x u S live fresh
    exact ⟨v,D,t,y,exec,time.trans_eq (Nat.add_right_comm _ _ 3),user,out,act⟩)
  refine ⟨prepared,owners,Prog.seqList (stageRuns.map fun k => embProg (runBank k) (Prod.mk k) (code k)),?_⟩
  intro data u S live fresh
  obtain ⟨z,F,t,out,exec,time,user,representedOut,trace⟩ := runStage data u S live fresh
  exact ⟨z,F,t,out,exec,time,user,representedOut,trace,stageTrace_transform n _ _ _ trace⟩

open IntegerMultBounds.Networks.Certificates.PR589.Nine in
/-- Each replica, port and class may choose its own address order across
the eight banks. A constant family specializes to the common role read. -/
noncomputable def readLanes {V : ℕ} (address : BankLane → (Axis ⊕ Axis → ℚ) → Fin V)
    (data : Fin 142081 → Fin V → ZMod 2) : State :=
  fun ρ => readRoles (address (ρ.replica,ρ.port,ρ.cls)) data ρ

private theorem remainder_readLanes {V : ℕ} (i : ℕ) {data out : Fin 142081 → Fin V → ZMod 2}
    (address : BankLane → (Axis ⊕ Axis → ℚ) → Fin V)
    (read : ∀ lane, readRoles (address lane) out = (Piece.remainder i).run (readRoles (address lane) data)) :
    readLanes address out = (Piece.remainder i).run (readLanes address data) := by
  funext ρ
  have step := congrFun (read (ρ.replica,ρ.port,ρ.cls)) ρ
  by_cases active : ρ.bank.val / 2 = BitHosting.pairOf i <;>
    simpa only [Piece.run,active,↓reduceIte,readLanes] using step

open IntegerMultBounds.Networks.Certificates.PR589.Nine in
/-- To read a physical stage it suffices to identify the framed word on each
of the 661 owners. All other roles follow from the invocation frame. -/
theorem stageReads_of_ownerReads {w B K : ℕ} (n : Fin 9)
    (address : BankLane → (Axis ⊕ Axis → ℚ) → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)))
    (owned : ∀ (k : Fin 32 × Fin 5) x y, InvocationEffect n k.1 k.2 w B K x y →
      ∀ (j : Fin 661) z, let ρ := owner n k.1 k.2 j.val
        y (ownerTape n k.1 k.2 j) (address (ρ.replica,ρ.port,ρ.cls) z) =
        along (bar (chart n j.val)ᵀ) (runWord n (registers n k.1 k.2 (readLanes address x)) j.val) z)
    (data out) (acts : stageRuns.foldr (fun k next x => ∃ y, InvocationEffect n k.1 k.2 w B K x y ∧ next y)
      (fun x => x = out) data) :
    readLanes address out = (Piece.stage n).run (readLanes address data) := by
  have step (k : Fin 32 × Fin 5) (x y) (run : InvocationEffect n k.1 k.2 w B K x y) :
      readLanes address y = stageRun n k (readLanes address x) := by
    funext ρ z
    by_cases h : ∃ j : Fin 661, owner n k.1 k.2 j.val = ρ
    · obtain ⟨j,rfl⟩ := h
      change _ = invoke n k.1 k.2 _ _ _
      rw [invoke_owner _ _ _ _ _ j.isLt]
      exact owned k x y run j z
    · have outside (j : ℕ) (hj : j < 661) : owner n k.1 k.2 j ≠ ρ := fun eq => h ⟨⟨j,hj⟩,eq⟩
      change _ = invoke n k.1 k.2 _ _ _
      rw [invoke_other _ _ _ _ _ outside]
      let lane : BankLane := (ρ.replica,ρ.port,ρ.cls)
      apply congrFun (run.2 (bankTape ρ.bank lane) (Fin.castSucc_ne_last _) ?_) (address lane z)
      intro j eq
      have same := (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eq))
      exact outside j.val j.isLt same
  have read (ls : List (Fin 32 × Fin 5)) (x y) (h : ls.foldr
      (fun k next a => ∃ b, InvocationEffect n k.1 k.2 w B K a b ∧ next b) (fun a => a = y) x) :
      readLanes address y = ls.foldl (fun a k => stageRun n k a) (readLanes address x) := by
    induction ls generalizing x with
    | nil => exact congrArg (readLanes address) h.symm
    | cons k rest ih =>
      obtain ⟨mid,run,tail⟩ := h
      simpa only [List.foldl_cons,← step k x mid run] using ih mid tail
  exact read stageRuns data out acts

/-- One directed XOR between two distinct banks, applied to every lane. -/
private abbrev BankAdd := {p : Fin 8 × Fin 8 // p.1 ≠ p.2}

private def BankAdd.apply {α : Type} [Add α] (p : BankAdd) (x : Fin 8 → α) : Fin 8 → α :=
  Function.update x p.val.1 (x p.val.1 + x p.val.2)

private theorem bankAddProgram (p : BankAdd) :
    ∃ (q : ℕ) (machine : Program (142081+2) q prime), ∀ {V : ℕ}, 0 < V →
    ∀ data : Fin 142081 → Fin V → ZMod 2,
    let bank := fun X => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V)
    ∃ out, HoareTime machine (fun X => X = bank data) (fun Y => Y = bank out) (76*17760*V) ∧
      (∀ x b, out (bankTape b x) = p.apply (fun j => data (bankTape j x)) b) ∧
      out (Fin.last 142080) = data (Fin.last 142080) := by
  classical
  let dst := bankTape p.val.1
  let src := bankTape p.val.2
  let lanes := Fintype.equivFin BankLane
  let entries := List.ofFn fun i => (lanes.symm i,lanes.symm i)
  have off (x y : BankLane) : dst x ≠ src y := fun h => p.property (bankTape_eq.mp h).1
  refine ⟨_,SparseRoleCircuit.program dst src off entries,?_⟩
  intro V pos data bank
  let out := fun j i => Circuit.run (SparseCircuit.copies dst src entries) (fun l => data l i) j
  refine ⟨out,?_,?_,?_⟩
  · have run := SparseRoleCircuit.copies_hoare (a := prime) dst src off entries (fun _ _ => blank) (fun _ => 0)
        data (FlatCoordinateSchedule.bits V) (FlatCoordinateSchedule.bits_value V)
    apply run.consequence (fun _ h => h) (fun _ h => h)
    have len : entries.length = 17760 := List.length_ofFn.trans (by simp only [BankLane,Fintype.card_prod,Fintype.card_fin])
    simpa only [len] using SparseRoleCircuit.cost_linear entries.length V _ (FlatCoordinateSchedule.bits_value V)
      (FlatCoordinateSchedule.bits_canonical V) pos
  · intro x b
    funext i
    simp only [out,SparseCircuit.copies_run _ _ _ off,BankAdd.apply]
    by_cases h : b = p.val.1
    · subst b
      simp only [entries,List.map_ofFn,List.sum_ofFn,Function.comp_apply,dst,src,bankTape_eq,
        true_and,Equiv.symm_apply_eq,Function.update_self,Pi.add_apply]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Equiv.symm_apply_apply]
    · have unused (j : BankLane) : dst j ≠ bankTape b x := fun eq => h (bankTape_eq.mp eq).1.symm
      simp only [entries,List.map_ofFn,List.sum_ofFn,Function.comp_apply,unused,ite_false,Finset.sum_const_zero,add_zero,Function.update_of_ne h]
  · funext i
    have untouched (x : BankLane) : dst x ≠ Fin.last 142080 := Fin.castSucc_ne_last _
    simp only [out,SparseCircuit.copies_run _ _ _ off,entries,List.map_ofFn,List.sum_ofFn,Function.comp_apply,untouched,ite_false,Finset.sum_const_zero,add_zero]

/-- Run directed bank additions on the owner's physical tapes, retaining the
counting controls and every tape outside the placement. -/
private theorem bankAdds_host (ops : List BankAdd) :
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (ports : Fin (142081+2) ↪ Fin T)
      (body : P → Pr P T Q prime U), states ≤ Q → ∃ code, ∀ {V : ℕ}, 0 < V →
    let ready := fun (x : Fin 142081 → Fin V → ZMod 2) (S : Stacks T prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded x) (FlatCoordinateSchedule.bits V)) (embStk ports S).L (embStk ports S).R
    ∀ data u S, ready data S → ∃ v D t out, Exec body code (mk u S) t (mk v D) ∧
      t ≤ ops.length*(76*17760*V*(142081+7)+6)+1 ∧ v.user = u.user ∧ ready out D ∧
      (∀ x b, out (bankTape b x) = ops.foldl (fun y op => op.apply y) (fun j => data (bankTape j x)) b) ∧
      out (Fin.last 142080) = data (Fin.last 142080) ∧
      ∀ j, (∀ l, ports l ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  induction ops with
  | nil =>
    exact ⟨0,fun _ _ _ => ⟨.act .done,fun _ data u S live =>
      ⟨u,S,1,data,Exec.act _ _,by simp,rfl,live,fun _ _ => rfl,rfl,fun _ _ => ⟨rfl,rfl⟩⟩⟩⟩
  | cons op ops ih =>
    obtain ⟨q,machine,run⟩ := bankAddProgram op
    obtain ⟨s,rest⟩ := ih
    refine ⟨max q s,?_⟩
    intro T Q P U ports body fits
    have cap := (le_max_left q s).trans fits
    obtain ⟨tail,execTail⟩ := rest ports body ((le_max_right q s).trans fits)
    refine ⟨(embProg ports (Empty.elim : Empty → P) (foreign (liftQ machine cap))).seq tail,?_⟩
    intro V pos ready data u S live
    obtain ⟨y,step,reads,tmp⟩ := run pos data
    obtain ⟨z,F,t,first,time,user,mid,keep⟩ := placedHoare_exec machine ports cap body step u S live
    obtain ⟨v,D,m,out,last,bill,same,done,acts,spare,off⟩ := execTail pos y z F mid
    refine ⟨v,D,_,out,Exec.seq first last,?_,same.trans user,done,?_,spare.trans tmp,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · intro x b
      simpa only [List.foldl_cons,show (fun j => y (bankTape j x)) = _ from funext (reads x)] using acts x b
    · intro j hj
      exact ⟨(off j hj).1.trans (keep j hj).1,(off j hj).2.trans (keep j hj).2⟩

private def swapAdds (d s : Fin 8) (h : d ≠ s) : List BankAdd :=
  [⟨(d,s),h⟩,⟨(s,d),Ne.symm h⟩,⟨(d,s),h⟩]

private theorem swapAdds_apply {V : ℕ} (d s : Fin 8) (h : d ≠ s) (x : Fin 8 → Fin V → ZMod 2) :
    (swapAdds d s h).foldl (fun y op => op.apply y) x = fun b => x (Equiv.swap d s b) := by
  have cancel₁ : ∀ a b : ZMod 2, (a+b)+(b+(a+b)) = b := by decide
  have cancel₂ : ∀ a b : ZMod 2, b+(a+b) = a := by decide
  funext b i
  by_cases hd : b = d
  · subst b
    simp only [swapAdds,List.foldl_cons,List.foldl_nil,BankAdd.apply,Function.update_self,
      Function.update_of_ne h,Function.update_of_ne (Ne.symm h),Pi.add_apply,Equiv.swap_apply_left,cancel₁]
  by_cases hs : b = s
  · subst b
    simp only [swapAdds,List.foldl_cons,List.foldl_nil,BankAdd.apply,Function.update_self,
      Function.update_of_ne h,Function.update_of_ne hd,Pi.add_apply,Equiv.swap_apply_right,cancel₂]
  · simp only [swapAdds,List.foldl_cons,List.foldl_nil,BankAdd.apply,Function.update_of_ne hd,
      Function.update_of_ne hs,Equiv.swap_apply_of_ne_of_ne hd hs]

private def exchangeAdds := swapAdds 0 1 (by decide) ++ swapAdds 2 3 (by decide) ++
  swapAdds 4 5 (by decide) ++ swapAdds 6 7 (by decide)

open IntegerMultBounds.Networks.Certificates.PR589.Nine in
private theorem bankPiece_adds (piece : Piece) (scheduled : piece ∈ nodeProgram)
    (isBank : (∃ d s, piece = .bridge d s) ∨ piece = .exchangeSides) :
    ∃ ops : List BankAdd, ops.length = (if piece = .exchangeSides then 12 else 2) ∧
    ∀ {V : ℕ} (data out : Fin 142081 → Fin V → ZMod 2),
      (∀ x b, out (bankTape b x) = ops.foldl (fun y op => op.apply y) (fun j => data (bankTape j x)) b) →
      ∀ address, readRoles address out = piece.run (readRoles address data) := by
  rcases isBank with ⟨d,s,rfl⟩ | rfl
  · have valid : ∀ e ∈ bridgeEdges, e.1 < 4 ∧ e.2 < 4 ∧ e.1 ≠ e.2 := by decide
    have member : (d,s) ∈ bridgeEdges := List.mem_filterMap.mpr ⟨_,scheduled,rfl⟩
    obtain ⟨hd,hs,ne⟩ := valid (d,s) member
    change d < 4 at hd
    change s < 4 at hs
    change d ≠ s at ne
    let de : Fin 8 := ⟨2*d,by omega⟩
    let se : Fin 8 := ⟨2*s,by omega⟩
    let do' : Fin 8 := ⟨2*d+1,by omega⟩
    let so : Fin 8 := ⟨2*s+1,by omega⟩
    have bankNe {a b : Fin 8} (h : a.val ≠ b.val) : a ≠ b := fun eq => h (congrArg Fin.val eq)
    let even : BankAdd := ⟨(de,se),bankNe (by dsimp [de,se]; omega)⟩
    let odd : BankAdd := ⟨(so,do'),bankNe (by dsimp [so,do']; omega)⟩
    refine ⟨[even,odd],rfl,?_⟩
    intro V data out acts address
    funext ρ z
    let lane : BankLane := (ρ.replica,ρ.port,ρ.cls)
    change out (bankTape ρ.bank lane) (address z) = _
    rw [acts]
    have parity : so ≠ de := bankNe (by dsimp [so,de]; omega)
    have parity' : do' ≠ de := bankNe (by dsimp [do',de]; omega)
    have srcEven : (⟨(2*s)%8,Nat.mod_lt _ (by decide)⟩ : Fin 8) = se := Fin.ext (Nat.mod_eq_of_lt se.isLt)
    have srcOdd : (⟨(2*d+1)%8,Nat.mod_lt _ (by decide)⟩ : Fin 8) = do' := Fin.ext (Nat.mod_eq_of_lt do'.isLt)
    by_cases a : ρ.bank.val = 2*d
    · have eq : ρ.bank = de := Fin.ext a
      simp only [List.foldl_cons,List.foldl_nil,even,odd,BankAdd.apply,eq,Function.update_of_ne (Ne.symm parity),
        Function.update_self,Piece.run,show de.val = 2*d from rfl,ite_true,readRoles,withBank,lane,srcEven,Pi.add_apply]
    · by_cases b : ρ.bank.val = 2*s+1
      · have eq : ρ.bank = so := Fin.ext b
        simp only [Piece.run,ite_eq_right a,ite_eq_left b]
        simp only [readRoles,withBank,lane,srcOdd,eq,List.foldl_cons,
          List.foldl_nil,even,odd,BankAdd.apply,Function.update_self,Function.update_of_ne parity,Function.update_of_ne parity',Pi.add_apply]
      · have n₁ : ρ.bank ≠ so := fun h => b (congrArg Fin.val h)
        have n₂ : ρ.bank ≠ de := fun h => a (congrArg Fin.val h)
        simp only [Piece.run,ite_eq_right a,ite_eq_right b,readRoles,lane,List.foldl_cons,List.foldl_nil,even,odd,BankAdd.apply,Function.update_of_ne n₁,Function.update_of_ne n₂]
  · refine ⟨exchangeAdds,rfl,?_⟩
    intro V data out acts address
    have sides : ∀ b : Fin 8, Equiv.swap 0 1 (Equiv.swap 2 3 (Equiv.swap 4 5 (Equiv.swap 6 7 b))) =
        (⟨(if b.val % 2 = 0 then b.val+1 else b.val-1)%8,Nat.mod_lt _ (by decide)⟩ : Fin 8) := by decide
    funext ρ z
    change out (bankTape ρ.bank (ρ.replica,ρ.port,ρ.cls)) (address z) = _
    rw [acts]
    simp only [exchangeAdds,List.foldl_append,swapAdds_apply,sides,Piece.run,otherSide,withBank,readRoles]

private theorem bankPiece_readLanes {V : ℕ} {piece : Piece}
    (bank : (∃ d s, piece = .bridge d s) ∨ piece = .exchangeSides)
    {data out : Fin 142081 → Fin V → ZMod 2}
    (read : ∀ address, readRoles address out = piece.run (readRoles address data)) :
    ∀ address, readLanes address out = piece.run (readLanes address data) := by
  intro address
  funext ρ
  have atLane := congrFun (read (address (ρ.replica,ρ.port,ρ.cls))) ρ
  rcases bank with ⟨d,s,rfl⟩ | rfl
  · simpa only [Piece.run,readLanes,withBank] using atLane
  · exact atLane

open IntegerMultBounds.Networks.Certificates.PR589.Nine in
/-- Physical bridge and side-exchange instructions on the same owner/control
bank as the stage invocations, at every logical address simultaneously. -/
theorem nodeBankPiece_host (piece : Piece) (scheduled : piece ∈ nodeProgram)
    (bankPiece : (∃ d s, piece = .bridge d s) ∨ piece = .exchangeSides) :
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (ports : Fin (142081+2) ↪ Fin T)
      (body : P → Pr P T Q prime U), states ≤ Q → ∃ code, ∀ {V : ℕ}, 0 < V →
    let ready := fun (x : Fin 142081 → Fin V → ZMod 2) (S : Stacks T prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded x) (FlatCoordinateSchedule.bits V)) (embStk ports S).L (embStk ports S).R
    ∀ data u S, ready data S → ∃ v D t out, Exec body code (mk u S) t (mk v D) ∧
      t ≤ (if piece = .exchangeSides then 12 else 2)*(76*17760*V*(142081+7)+6)+1 ∧
      v.user = u.user ∧ ready out D ∧ (∀ address, readLanes address out = piece.run (readLanes address data)) ∧
      out (Fin.last 142080) = data (Fin.last 142080) ∧
      ∀ j, (∀ l, ports l ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  obtain ⟨ops,len,acts⟩ := bankPiece_adds piece scheduled bankPiece
  obtain ⟨states,build⟩ := bankAdds_host ops
  refine ⟨states,?_⟩
  intro T Q P U ports body cap
  obtain ⟨code,run⟩ := build ports body cap
  refine ⟨code,?_⟩
  intro V pos ready data u S live
  obtain ⟨v,D,t,out,exec,time,user,done,reads,tmp,off⟩ := run pos data u S live
  exact ⟨v,D,t,out,exec,len ▸ time,user,done,bankPiece_readLanes bankPiece (acts data out reads),tmp,off⟩

def Piece.bankOp : Piece → Bool
  | .bridge .. | .exchangeSides => true
  | _ => false

open IntegerMultBounds.Networks.Certificates.PR589.Nine in
/-- Sequence the 29 physical piece occurrences. The nine bridges, side exchange
and terminal idle are supplied here. Stage and idle calls retain their own child intervals. -/
theorem nodePieces_host
    (tapes : Fin nodeProgram.length → ℕ) (ports : ∀ i, Fin (142081+2) ↪ Fin (tapes i)) :
    let I := Fin nodeProgram.length
    let piece := fun i : I => nodeProgram[i.val]'i.isLt
    ∃ (states T : ℕ) (fan : Fin (142081+2) ↪ Fin T) (bank : ∀ i, Fin (tapes i) ↪ Fin T),
    (∀ i j, bank i (ports i j) = fan j) ∧
    ∀ {P U A : Type} {Q V : ℕ}, states ≤ Q → 0 < V →
    ∀ (body : ∀ i, P → Pr P (tapes i) Q prime U) (initial : ∀ i, Stacks (tapes i) prime)
      (localCost : I → ℕ) (childTime : ℕ → ℕ) (shared : Stacks (142081+2) prime)
      (address : A → BankLane → (Axis ⊕ Axis → ℚ) → Fin V),
    let ready := fun (x : Fin 142081 → Fin V → ZMod 2) (S : Stacks (142081+2) prime) =>
      RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
        (SparseRoleCircuit.encoded x) (FlatCoordinateSchedule.bits V)) S.L S.R
    let start := fun i : I => ((nodeProgram.take i.val).flatMap Piece.children).length
    let fixed := fun (i : I) => if (piece i).bankOp then
      (if piece i = .exchangeSides then 12 else 2)*(76*17760*V*(142081+7)+6)+1
      else if piece i = .remainder 9 then 1 else localCost i
    (∀ i, (piece i).bankOp = false → piece i ≠ .remainder 9 → ∃ code, ∀ x u S, ready x (embStk (ports i) S) →
      (∀ l, (∀ j, ports i j ≠ l) → S.L l = (initial i).L l ∧ S.R l = (initial i).R l) →
      ∃ v D t y, Exec (body i) code (mk u S) t (mk v D) ∧
        t ≤ localCost i + ((List.range' (start i) (piece i).children.length).map childTime).sum ∧
        v.user = u.user ∧ ready y (embStk (ports i) D) ∧
        ∀ a, readLanes (address a) y = (piece i).run (readLanes (address a) x)) →
    let table := fun g : I × P => embProg (bank g.1) (Prod.mk g.1) (body g.1 g.2)
    ∃ prepared : Stacks T prime, embStk fan prepared = shared ∧ ∃ code,
    ∀ x u S, ready x (embStk fan S) → (∀ l, (∀ j, fan j ≠ l) → S.L l = prepared.L l ∧ S.R l = prepared.R l) →
      ∃ v D t y, Exec table code (mk u S) t (mk v D) ∧
        t ≤ (List.ofFn fixed).sum + ((List.range nodeChildren5.length).map childTime).sum+1 ∧
        v.user = u.user ∧ ready y (embStk fan D) ∧ ∀ a, readLanes (address a) y = runNode (readLanes (address a) x) := by
  classical
  intro I piece
  letI : BEq I := inferInstanceAs (BEq (Fin nodeProgram.length))
  let B := {i : I // (piece i).bankOp = true}
  have allowed (i : B) : (∃ d s, piece i.val = .bridge d s) ∨ piece i.val = .exchangeSides := by
    have h := i.property
    cases eq : piece i.val <;> simp_all [Piece.bankOp]
  choose qs make using fun i : B => nodeBankPiece_host (piece i.val) (List.getElem_mem ..) (allowed i)
  obtain ⟨T,fan,bank,selected,assemble⟩ := scheduledBanks_exec tapes ports
  refine ⟨Finset.univ.sup qs,T,fan,bank,selected,?_⟩
  intro P U A Q V fits pos body initial localCost childTime shared address ready start fixed active table
  let bill := fun i => ((List.range' (start i) (piece i).children.length).map childTime).sum
  let effect := fun i x y => ∀ a, readLanes (address a) y = (piece i).run (readLanes (address a) x)
  have step (i : I) : ∃ code, ∀ x u S, ready x (embStk (ports i) S) →
      (∀ l, (∀ j, ports i j ≠ l) → S.L l = (initial i).L l ∧ S.R l = (initial i).R l) →
      ∃ v D t y, Exec (body i) code (mk u S) t (mk v D) ∧ t ≤ fixed i + bill i ∧
        v.user = u.user ∧ ready y (embStk (ports i) D) ∧ effect i x y := by
    by_cases h : (piece i).bankOp = true
    · let j : B := ⟨i,h⟩
      obtain ⟨code,run⟩ := make j (ports i) (body i) ((Finset.le_sup (Finset.mem_univ j)).trans fits)
      refine ⟨code,?_⟩
      intro x u S live _
      obtain ⟨v,D,t,y,exec,time,user,done,reads,_,_⟩ := run pos x u S live
      refine ⟨v,D,t,y,exec,?_,user,done,fun a => reads (address a)⟩
      exact (show t ≤ fixed i by simpa only [fixed,h,ite_true] using time).trans (Nat.le_add_right ..)
    have hb : (piece i).bankOp = false := Bool.eq_false_iff.mpr h
    by_cases terminal : piece i = .remainder 9
    · refine ⟨.act .done,?_⟩
      intro x u S live _
      refine ⟨u,S,1,x,Exec.act _ _,?_,rfl,live,?_⟩
      · simp [fixed,terminal,Piece.bankOp]
      · intro a
        rw [terminal,terminalIdle_run]
    · simpa only [fixed,hb,Bool.false_eq_true,ite_false,if_neg terminal] using active i hb terminal
  choose code run using step
  let order := List.finRange nodeProgram.length
  have listed : order.map piece = nodeProgram := by rw [← List.ofFn_eq_map]; exact List.ofFn_getElem
  obtain ⟨prepared,owners,exec⟩ := assemble body code ready effect (fun i => fixed i + bill i) initial shared run
  refine ⟨prepared,owners,Prog.seqList (order.map fun i => embProg (bank i) (Prod.mk i) (code i)),?_⟩
  intro x u S live fresh
  obtain ⟨v,D,t,y,steps,paid,user,done,acts⟩ := exec order (List.nodup_finRange _) x u S live fresh
  refine ⟨v,D,t,y,steps,?_,user,done,?_⟩
  · have before (i : I) : ((order.take (order.idxOf i)).flatMap (fun j => (piece j).children)).length = start i := by
      rw [← List.flatMap_map, List.map_take,listed]
      have idx : order.idxOf i = i.val := List.idxOf_finRange i
      rw [idx]
    have children : order.flatMap (fun i => (piece i).children) = nodeChildren5 := by rw [← List.flatMap_map,listed,nodeChildren5]
    have fees := scheduledChildBill (fun i => (piece i).children) childTime order (List.nodup_finRange _) 0
    simp only [Nat.zero_add,before,children,List.range_eq_range'] at fees
    have split (ls : List I) : (ls.map fun i => fixed i + bill i).sum = (ls.map fixed).sum + (ls.map bill).sum := by
      induction ls with
      | nil => rfl
      | cons i rest ih => simp only [List.map_cons,List.sum_cons,ih]; omega
    rw [split,show (order.map bill).sum = _ from fees,← List.ofFn_eq_map] at paid
    simpa only [List.range_eq_range'] using paid
  · have read (ls : List I) (a : A) (x y) (h : ls.foldr (fun i next x => ∃ y, effect i x y ∧ next y) (fun x => x = y) x) :
        readLanes (address a) y = runPieces (ls.map piece) (readLanes (address a) x) := by
      induction ls generalizing x with
      | nil => exact congrArg (readLanes (address a)) h.symm
      | cons i ls ih =>
        obtain ⟨z,act,rest⟩ := h
        simpa only [List.map_cons,runPieces,List.foldl_cons,← act a] using ih z rest
    intro a
    simpa only [listed,runNode] using read order a x y acts

/-- Finish a nonroot scanner bank after the child queue transfer. The seven
header sources and two work registers can stay outside the caller/scan bank. -/
theorem childQueue_headers_exec {T Q w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin (21+59) ↪ Fin T) (source : Fin 7 → Fin T) (tmp aux : Fin T)
    (W a b h width : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (tail queue : List (Fin (prime+4)))
    (u v : HS T Q prime U) (S : Stacks T prime) (p : Pr P T Q prime U) (t : ℕ) :
    let scanner := (Fin.natAddEmb 21 (m := 59)).trans bank
    let dst := ordinaryHeaderPorts.trans scanner
    let words := ordinaryEntryWords W a b h false parent width queue
    let D : Stacks T prime := {S with R := (Function.update (Function.update (Function.update
      S.R (bank 7) tail) (scanner 58) queue) (scanner 47) (List.replicate width Node.tick))}
    Exec body p (mk u S) t (mk v D) → v.user = u.user →
    (∀ j, S.R (scanner j) = []) → (∀ i, S.R (source i) = words (ordinaryHeaderPorts i).val) →
    (∀ k ∈ tmp :: aux :: (List.finRange 7).map source, ∀ j, k ≠ bank j) →
    (∀ i, [source i,dst i,tmp,aux].Nodup) → S.R tmp = [] → S.R aux = [] →
    ∃ z F, z.user = u.user ∧ F.L = S.L ∧ (∀ j : Fin 59, F.R (scanner j) = words j.val) ∧
      Exec body (p.seq (Cover.Fallback.Record.copyLeafHeaders source dst tmp aux (List.finRange 7)))
        (mk u S) (t+(((List.finRange 7).map (fun i => 6*(words (ordinaryHeaderPorts i).val).length+6)).sum+1)) (mk z F) := by
  intro scanner dst words D prior same fresh sources outside ports temp auxFree
  have keep (k : Fin T) (hk : k ∈ tmp :: aux :: (List.finRange 7).map source) : D.R k = S.R k := by
    simp [D,scanner,Function.update_of_ne,outside k hk]
  have mem (i : Fin 7) : source i ∈ tmp :: aux :: (List.finRange 7).map source :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_finRange i)))
  obtain ⟨z,F,user,run,left,loaded,_⟩ := ordinaryHeaders_exec body source scanner (by decide) tmp aux
    W a b h false parent width queue v D (fun i => (keep _ (mem i)).trans (sources i))
    (fun i j => outside _ (mem i) _) ports ((keep _ (by simp)).trans temp)
    ((keep _ (by simp)).trans auxFree) (childQueue_scanner bank S tail queue width fresh)
  exact ⟨z,F,user.trans same,left,loaded,Exec.seq prior run⟩

/-- Normalize the caller's chart headers and decode the three row dimensions
and both spectator factors for the scanner. -/
theorem ordinaryDirectoryHeaders_exec {K T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 26 ↪ Fin T) (roles : Tapes K prime) (v : RecursiveInterchangeLayout.Descriptor) (w : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) (headers : LabelCallerHeaders.Represents r S roles v w) :
    let dims : List (Fin 7) := [0,1,2,4,5]
    (∀ i ∈ dims, S.R (LabelDecode.target r i) = []) → (∀ k ∈ [r 9,r 10,r 11], S.R k = []) →
    ∃ z F t, Exec body ((LabelCallerHeaders.load r).seq (LabelDecode.program r dims)) (mk u S) t (mk z F) ∧
      z.user = u.user ∧ t ≤ LabelCallerHeaders.cost r S + 17*(v.beforeRows+v.rows+v.beforeH+v.between+v.afterD)+86 ∧
      (∀ i ∈ dims, F.R (LabelDecode.target r i) = List.replicate (LabelDecode.field v w i) (bitSymbol true)) ∧
      (∀ i, F.R (LabelDecode.source r i) = (FlatCoordinateSchedule.bits (LabelDecode.field v w i)).map bitSymbol ∧
        F.L (LabelDecode.source r i) = [separator]) ∧
      ∀ j, j ∉ LabelCallerHeaders.ports r → j ∉ dims.map (LabelDecode.target r) → F.R j = S.R j ∧ F.L j = S.L j := by
  intro dims fresh scratch
  obtain ⟨a,B,m,user,paid,binary,off,load⟩ := LabelCallerHeaders.load_exec body r roles v w u S headers
  have separate (j : Fin 26) (small : j.val < 19) : r j ∉ LabelCallerHeaders.ports r := by
    intro mem
    obtain ⟨i,_,eq⟩ := List.mem_map.mp mem
    have val := congrArg Fin.val (r.injective eq)
    change 19+i.val = j.val at val
    omega
  obtain ⟨z,R,n,keep,time,unary,others,decode⟩ := LabelDecode.runs body r (LabelDecode.field v w)
    dims (by decide) a B (fun i _ => (binary i).1)
    (fun i hi => (off _ (separate _ (by change i.val < 19; omega))).1.trans (fresh i hi))
    (by
      intro j hj
      have unchanged : B.R j = S.R j := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl <;> exact (off _ (separate _ (by decide))).1
      exact unchanged.trans (scratch j hj))
  refine ⟨z,_,m+n,Exec.seq load decode,keep.trans user,?_,unary,?_,?_⟩
  · change n ≤ 17*(v.beforeRows+1)+(17*(v.rows+1)+(17*(v.beforeH+1)+(17*(v.between+1)+(17*(v.afterD+1)+0))))+1 at time
    omega
  · intro i
    refine ⟨(others _ ?_).trans (binary i).1,(binary i).2⟩
    intro mem
    obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
    have val := congrArg Fin.val (r.injective eq)
    change j.val = 19+i.val at val
    omega
  · intro j untouched unused
    exact ⟨(others j unused).trans (off j untouched).1,(off j untouched).2⟩

/-- From the normalized precision header, load the scanner's predecessor clock
on a fresh tape. Both the binary source and the scratch tapes are preserved. -/
theorem ordinaryClock_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    {src dst a b c : Fin T} (ports : [src,dst,a,b,c].Nodup) (w : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime)
    (word : S.R src = (FlatCoordinateSchedule.bits (w+1)).map bitSymbol)
    (empty : ∀ j ∈ [dst,a,b,c], S.R j = []) :
    ∃ z n, z.user = u.user ∧ n ≤ 17*w+35 ∧
      Exec body ((toUnary src dst a b c).seq (.act (.pop (.rt dst) (fun v _ => v) .done)))
        (mk u S) n (mk z {S with R := Function.update S.R dst (List.replicate w (bitSymbol true))}) := by
  obtain ⟨z,t,user,paid,decode⟩ := LabelDecode.field_exec body ports (w+1) u S word empty
  let D : Stacks T prime := {S with R := Function.update S.R dst (List.replicate (w+1) (bitSymbol true))}
  have pop := Exec.act (body := body) (.pop (.rt dst) (fun v _ => v) .done) (mk z D)
  have endPop : (Action.pop (.rt dst) (fun v _ => v) .done : Act T Q prime U).run (mk z D) =
      mk z {S with R := Function.update S.R dst (List.replicate w (bitSymbol true))} := by
    simp [Action.run,update_rt,D,Function.update_idem]
  rw [endPop] at pop
  exact ⟨z,t+1,user,by omega,Exec.seq decode pop⟩

open Fallback in
/-- Copy and widen the root cutoff without changing its source or the tape
supplying the common binary precision. -/
theorem copyCutoff_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (src header cut cnt tmp scratch : Fin T) (cutoff L : ℕ) (fits : cutoff.size ≤ L)
    (u : HS T Q prime U) (S : Stacks T prime)
    (regs : [src,header,cut,cnt,tmp,scratch].Nodup) (word : S.R src = binSyms cutoff.size cutoff)
    (precision : (S.R header).length = L) (blankCut : S.R cut = []) (a : S.R cnt = [])
    (b : S.R tmp = []) (c : S.R scratch = []) :
    ∃ z, z.user = u.user ∧ Exec body ((bcopy src cut cnt tmp).seq (bwiden cut header cnt tmp scratch))
      (mk u S) (6*cutoff.size+12*L+24) (mk z {S with R := Function.update S.R cut (binSyms L cutoff)}) := by
  regs_ne regs
  obtain ⟨v,user,copy⟩ := bcopy_exec (body := body) (a := src) (c := cut) (t₁ := cnt) (t₂ := tmp)
    (by simp_all [ne_comm]) u S a b
  rw [word,length_binSyms,blankCut,List.append_nil] at copy
  let D : Stacks T prime := {S with R := Function.update S.R cut (binSyms cutoff.size cutoff)}
  obtain ⟨z,final,widen⟩ := bwiden_exec (body := body) (a := cut) (wR := header) (cnt := cnt)
    (t₁ := tmp) (t₂ := scratch) (by simp_all [ne_comm]) fits (Nat.lt_size_self cutoff) v D
    (by simp [D]) (by change (Function.update S.R cut _ header).length = L; rw [Function.update_of_ne (by assumption)]; exact precision)
    (by simp [D,Function.update_of_ne, *, Ne.symm])
    (by simp [D,Function.update_of_ne, *, Ne.symm])
    (by simp [D,Function.update_of_ne, *, Ne.symm])
  exact ⟨z,final.trans user,(Exec.seq copy widen).cast (by omega) (by simp [D])⟩

open Fallback in
/-- Copy the caller's cutoff to the dispatcher's last tape and pad it to the
root precision. The source headers survive and the column scratch is restored. -/
theorem ordinaryRootCutoff_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (placement : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (src header : Fin T)
    (root : RecursiveInterchangeLayout.Descriptor) (cutoff : ℕ) (within : cutoff ≤ root.width)
    (u : HS T Q prime U) (S : Stacks T prime) :
    let cut := placement (Fin.last _)
    let col := columnBank.trans placement
    let L := root.width.size
    [src,header,cut,col 0,col 1,col 3].Nodup →
    S.R src = binSyms cutoff.size cutoff → (S.R header).length = L →
    S.R cut = [] → S.R (col 0) = [] → S.R (col 1) = [] → S.R (col 3) = [] →
    ∃ z, z.user = u.user ∧
      Exec body ((bcopy src cut (col 0) (col 1)).seq (bwiden cut header (col 0) (col 1) (col 3)))
        (mk u S) (6*cutoff.size+12*L+24)
        (mk z {S with R := Function.update S.R cut (binSyms L cutoff)}) ∧
      cutoff < 2^L ∧ ∀ path : List (Fin nodeChildren5.length),
        (path.foldl (scheduledChild prime) root).width.size ≤ L := by
  intro cut col L regs word precision blankCut a b c
  obtain ⟨z,user,run⟩ := copyCutoff_exec body src header cut (col 0) (col 1) (col 3) cutoff L
    (Nat.size_le_size within) u S regs word precision blankCut a b c
  refine ⟨z,user,run,within.trans_lt (Nat.lt_size_self _),fun path => ?_⟩
  have bound := directoryDigits_bound prime root path
  apply Nat.size_le_size
  omega

/-- The shared root precision is short enough even at the last active parent:
writing the child's width and testing the cutoff together cost one volume term. -/
theorem ordinaryChildComparison_volume_le (root : RecursiveInterchangeLayout.Descriptor)
    (depth b cutoff rank w W : ℕ) (levels : 0 < depth) (base : 0 < b)
    (width : root.width = 64^depth*b) (stop : 42^depth*b ≤ cutoff)
    (active : cutoff ≤ 64*(w+1)) (fits : rank ≤ 64) (live : 0 < W) :
    let L := root.width.size
    let M := prime^(w+1)
    4*w+23*((w+1)*rank)+22*L+51 ≤ 2940*(M^128*W) := by
  intro L M
  have room := alignedRootWidth_le root depth b cutoff levels base width stop
  have pos : 0 < root.width := width ▸ Nat.mul_pos (by positivity) base
  have bits : L ≤ cutoff := Nat.size_le.mpr (by omega)
  have rankWidth := Nat.mul_le_mul_left (w+1) fits
  have atom : w+1 ≤ M := (Nat.lt_two_pow_self (n := w+1)).le.trans
    (Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le _)
  have vol : w+1 ≤ M^128*W := atom.trans ((Nat.le_self_pow (by decide : 128 ≠ 0) M).trans
    (Nat.le_mul_of_pos_right _ live))
  omega

/-- Turn the parent's predecessor clock into the child's binary width. The
cutoff register sets the padding. Only the comparison operand survives. -/
theorem ordinaryChildWidth_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (rank w L : ℕ) (fits : ((w+1)*rank).size ≤ L)
    (u : HS T Q prime U) (S : Stacks T prime) (clock : (S.R (r 0)).length = w)
    (precision : (S.R (r 1)).length = L) (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (r j) = []) :
    let width := (w+1)*rank
    let push := Prog.act (.push (.rt (r 0)) (fun _ => Node.tick) .done)
    let pop := Prog.act (.pop (.rt (r 0)) (fun v _ => v) .done)
    ∃ z n, z.user = u.user ∧ n ≤ 4*w+23*width+12*L+40 ∧
      Exec body (((push.seq (Node.umul rank (r 0) (r 2) (r 4))).seq pop).seq
        ((unaryBinaryWidth (r 2) (r 1) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)).seq (bclear (r 2))))
        (mk u S) n (mk z {S with R := Function.update S.R (r 3) (binSyms L width)}) := by
  intro width push pop
  let A : Stacks T prime := {S with R := Function.update S.R (r 0) (Node.tick :: S.R (r 0))}
  have start : Exec body push (mk u S) 1 (mk u A) := by
    apply (Exec.act (body := body) (.push (.rt (r 0)) (fun _ => Node.tick) .done) (mk u S)).cast rfl
    simp [A,Action.run,update_rt]
  obtain ⟨v,user,multiply⟩ := Node.umul_exec (body := body) rank (a := r 0) (b := r 2) (t := r 4)
    (by simp) (by simp) (by simp) u A (by simpa [A] using empty 4 (by decide))
  have count : (A.R (r 0)).length = w+1 := by simp [A,clock]
  rw [count,show A.R (r 2) = [] by simpa [A] using empty 2 (by decide),List.append_nil,Nat.mul_comm rank] at multiply
  let B : Stacks T prime := {S with R := Function.update S.R (r 2) (List.replicate width Node.tick)}
  have restore : Exec body pop (mk v {A with R := Function.update A.R (r 2) (List.replicate width Node.tick)}) 1 (mk v B) := by
    apply (Exec.act (body := body) (.pop (.rt (r 0)) (fun v _ => v) .done : Act T Q prime U)
      (mk v {A with R := Function.update A.R (r 2) (List.replicate width Node.tick)})).cast rfl
    simp [Action.run,A,B,update_rt,Function.update_comm (show r 2 ≠ r 0 by simp)]
  have free (j : Fin 10) (hj : 3 ≤ j.val) : B.R (r j) = [] := by
    have ne : j ≠ 2 := fun eq => by subst j; contradiction
    simpa [B,Function.update_of_ne (r.injective.ne ne)] using empty j (by omega)
  obtain ⟨y,t,same,cost,binary⟩ := unaryBinaryWidth_exec (body := body) (src := r 2) (width := r 1) (dst := r 3)
    (a := r 4) (h := r 5) (par := r 6) (bits := r 7) (cnt := r 8) (saved := r 9) (by simp)
    width L fits v B (by simp [B]) (by simpa [B] using precision) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact free _ (by decide))
  let D : Stacks T prime := {B with R := Function.update B.R (r 3) (binSyms L width)}
  obtain ⟨z,final,_,erase⟩ := bclear_exec (body := body) (r 2) y D
  have len : (D.R (r 2)).length = width := by simp [D,B]
  rw [len] at erase
  refine ⟨z,_,final.trans (same.trans user),?_,(Exec.seq (Exec.seq (Exec.seq start multiply) restore)
    (Exec.seq binary erase)).cast rfl ?_⟩
  · omega
  · have reset : Function.update S.R (r 2) [] = S.R := by
      rw [← empty 2 (by decide),Function.update_eq_self]
    simp [D,B,Function.update_comm (show r 3 ≠ r 2 by simp),reset]

/-- Compare from the live predecessor clock and restore the full stack bank
before either child branch starts. The comparison bit survives cleanup. -/
noncomputable def ordinaryCutoffTest {T Q : ℕ} {P U : Type} (r : Fin 10 ↪ Fin T) (rank : ℕ) : Pr P T Q prime U :=
  let push := Prog.act (.push (.rt (r 0)) (fun _ => Node.tick) .done)
  let pop := Prog.act (.pop (.rt (r 0)) (fun v _ => v) .done)
  let width := ((push.seq (Node.umul rank (r 0) (r 2) (r 4))).seq pop).seq
    ((unaryBinaryWidth (r 2) (r 1) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)).seq (bclear (r 2)))
  width.seq ((blt (r 1) (r 3) (r 4) (r 5) (r 6) (r 7)).seq (bclear (r 3)))

theorem ordinaryCutoffTest_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (rank w L cutoff : ℕ) (cutFits : cutoff < 2^L) (fits : ((w+1)*rank).size ≤ L)
    (u : HS T Q prime U) (S : Stacks T prime) (clock : (S.R (r 0)).length = w)
    (word : S.R (r 1) = binSyms L cutoff) (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (r j) = []) :
    ∃ z n, z.user = u.user ∧ z.scan (r 7) = bitSymbol (decide (cutoff < (w+1)*rank)) ∧
      n ≤ 4*w+23*((w+1)*rank)+22*L+50 ∧ Exec body (ordinaryCutoffTest r rank) (mk u S) n (mk z S) := by
  let width := (w+1)*rank
  obtain ⟨v,t,user,cost,prepare⟩ := ordinaryChildWidth_exec body r rank w L fits u S clock
    (word ▸ length_binSyms ..) empty
  let D : Stacks T prime := {S with R := Function.update S.R (r 3) (binSyms L width)}
  obtain ⟨y,same,flag,_,compare⟩ := blt_exec body (a := r 1) (b := r 3) (tx := r 4) (ty := r 5)
    (tz := r 6) (cy := r 7) (by simp) (by simp) (by simp) cutFits (Nat.size_le.mp fits) v D
    (by simpa [D] using word) (by simp [D,width]) (by simpa [D] using empty 4 (by decide))
    (by simpa [D] using empty 5 (by decide)) (by simpa [D] using empty 6 (by decide))
  obtain ⟨z,final,slots,erase⟩ := bclear_exec (body := body) (r 3) y D
  have len : (D.R (r 3)).length = L := by simp [D]
  rw [len] at erase
  have reset : Function.update S.R (r 3) [] = S.R := by rw [← empty 3 (by decide),Function.update_eq_self]
  refine ⟨z,_,final.trans (same.trans user),(congrFun slots _).trans flag,?_,(Exec.seq prepare
    (Exec.seq compare erase)).cast rfl ?_⟩
  · omega
  · simp [D,reset]


def cutoffColumnSlots : Fin 10 ↪ Fin 35 := ⟨![33,34,0,1,3,4,5,6,7,8],by decide⟩

/-- Reuse the column clock and eight empty column registers. The persistent
cutoff lives outside the routing placement, so the packed call can read it. -/
def ordinaryCutoffPorts {T : ℕ} (bank : Fin 35 ↪ Fin T) (cut : Fin T)
    (off : ∀ i, bank i ≠ cut) : Fin 10 ↪ Fin T :=
  ⟨fun j => if j = 1 then cut else bank (cutoffColumnSlots j),by
    intro i j eq
    dsimp only at eq
    split_ifs at eq with hi hj hj
    · exact hi.trans hj.symm
    · exact (off _ eq.symm).elim
    · exact (off _ eq).elim
    · exact cutoffColumnSlots.injective (bank.injective eq)⟩

open Fallback RecursiveInterchangeLayout in
/-- The role-stream payload passed to an ordinary call is exactly one
scheduled occurrence's volume. This identifies its charge in parent units. -/
theorem ordinaryScheduledMeasures (node : Descriptor) (i : Fin nodeChildren5.length) (w : ℕ)
    (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) :
    let parent := role node 142080
    let r := nodeChildren5[i.val]
    let g := 64-r
    let packed := ordinaryChildDescriptor r g w (CopyChildLayout.spectators parent)
    let child := scheduledChild prime node i
    rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child ∧
      packed.width = child.width ∧ volume prime packed * 142080 = volume prime node := by
  intro parent r g packed child
  have rankLayout : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child := by
    simp only [child,scheduledChild,aligned,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
    rfl
  have size := Fintype.card_congr (ordinaryScheduledLayout parent r g w)
  simp only [Fintype.card_fin,rankLayout] at size
  refine ⟨rankLayout,?_,?_⟩
  · rw [← rankLayout]
    exact Nat.mul_comm ..
  · rw [show volume prime packed = volume prime child from size]
    exact (scheduledChild_measures prime node ⟨w+1,aligned⟩ rows i).2

open Fallback RecursiveInterchangeLayout in
private theorem ordinaryOccurrenceTranspose (parent : Descriptor) (r g w : ℕ) (child : Descriptor)
    (eqn : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child) :
    let packed := ordinaryChildDescriptor r g w (CopyChildLayout.spectators parent)
    let layout := (ordinaryScheduledLayout parent r g w).trans (finCongr (congrArg (volume prime) eqn))
    ∀ (word : Fin (volume prime child) → ZMod 2) k,
      Shared50RecursiveNodeRows.transpose (one_dvd packed.rows) (word ∘ layout) k =
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word (layout k) := by
  subst child
  exact ordinaryScheduledTranspose parent r g w

open Fallback RecursiveInterchangeLayout in
/-- Read the predecessor clock and compare the child width with the cutoff. Equality executes the stopped exchange. -/
theorem ordinaryChildDispatch_exec [M8.Machine.Net] {P U : Type} {T : ℕ}
    (placement : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (body : P → Pr P T columnCapacity prime U) :
    let ports := columnPorts.trans placement
    let cut := placement (Fin.last _)
    let outside : ∀ i, ports i ≠ cut := fun i => placement.injective.ne (Fin.castSucc_ne_last i)
    ∃ C : ℕ, ∀ (node : Descriptor) (i : Fin nodeChildren5.length) w (aligned : node.width = 64*(w+1)),
      let r := nodeChildren5[i.val]
      let g := 64-r
      let parent := role node 142080
      let W := CopyChildLayout.spectators parent
      0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let is := ordinaryChildPackSchedule r g
      let routeTime := (is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1
      let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
      let cmp := ordinaryCutoffPorts bank cut (fun i => outside _)
      let pass := fun js => statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule d js)
      let clean := fun (S : Stacks T prime) => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → S.L (ports k) = [] ∧ S.R (ports k) = []
      ∀ (v : HS T columnCapacity prime U) (S : Stacks T prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (original : Fin (M^d*W) → ZMod 2)
        (input : (Fin d → ZMod M) → IntegerMultBounds.Swap.Shear.State (Fin (r+g)) (ZMod M))
        (f : P) (budget cutoff L : ℕ),
      let saved := fun D : Stacks T prime => ∀ j, (∀ i, ports i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j
      let desc := ordinaryChildDescriptor r g w W
      let child := scheduledChild prime node i
      let same : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child := by
        simp only [child,scheduledChild,aligned,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
        rfl
      let layout := (ordinaryScheduledLayout parent r g w).trans (finCongr (congrArg (volume prime) same))
      let onTape := fun (word : Fin (volume prime child) → ZMod 2) (D : Stacks T prime) =>
        ∀ z, readAt blank (D.L (bank 24)) (D.R (bank 24)) z =
          M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (v := desc) (word ∘ layout) z
      let columns := ColumnRecordReady bank M.size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      cutoff < 2^L → desc.width.size ≤ L →
      S.R cut = binSyms L cutoff →
      (cutoff < desc.width → child.width < node.width → ∀ word u D, onTape word D → clean D → saved D → D.R cut = binSyms L cutoff → ∃ y G t, y.user = u.user ∧ t ≤ budget ∧
        Exec body (body f) (mk u D) t (mk y G) ∧
        onTape (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word) G ∧
        (∀ j : Fin 35, j ≠ 24 → G.L (bank j) = D.L (bank j) ∧ G.R (bank j) = D.R (bank j)) ∧ clean G ∧ saved G) →
      columns original (fun x => Fin.append (input x).1 (input x).2) S → clean S → ∃ z F n, z.user = v.user ∧
        n ≤ 4*w+23*desc.width+22*L+51+(if cutoff < desc.width then budget+2+2*(1+routeTime) else C*(desc.width*(M^d*W))) ∧
        Exec body (.seq (ordinaryCutoffTest cmp r)
          (.cond (fun u => symBit (u.scan (cmp 7))) (.seq (pass is) (.seq (.call f) (pass is.reverse)))
            (pass (stoppedParentSchedule r g)))) (mk v S) n (mk z F) ∧
        columns original (fun x => let t := Cover.Weighted.child r (fun _ => 1) (fun _ => 1) (input x)
                                   Fin.append t.1 t.2) F ∧ clean F ∧ saved F ∧ F.R cut = binSyms L cutoff ∧
        ∀ c, Fast.Main.mnProgPush (pass is) ≤ c → Fast.Main.mnProgPush (pass is.reverse) ≤ c →
          Fast.Main.mnProgPush (pass (stoppedParentSchedule r g)) ≤ c →
          (∀ f, Fast.Main.mnProgPush (body f) ≤ c) → StackGrowthExcept (bank 24) S F
            (c*(if cutoff < desc.width then 2*(1+routeTime) else C*(desc.width*(M^d*W)))) := by
  intro ports cut outside
  obtain ⟨C,stopped⟩ := stoppedOrdinaryChild_exec ports body
  refine ⟨C,?_⟩
  intro node i w aligned r g parent W hW d M is routeTime bank cmp pass clean v S record dest q original input f budget cutoff L
    saved desc child eqn layout onTape columns cutFits widthFits cutWord recurse start free
  have rankPos : 0 < r := (nodeChildren5_bounds i).1
  have rankBound : r ≤ 42 := nodeChildren5_le i
  have split : r+g = 64 := by dsimp only [g]; omega
  have gap : 0 < g := by omega
  have div : node.width/64 = w+1 := by simp [aligned]
  obtain ⟨u,m,user,flag,testCost,compare⟩ := ordinaryCutoffTest_exec body cmp r w L cutoff cutFits widthFits
    v S (by exact start.choose_spec.1.clock) (by exact cutWord) (by
      intro j hj
      have ne : j ≠ 1 := fun eq => by subst j; contradiction
      have scratch : ∀ k : Fin 10, 2 ≤ k.val → cutoffColumnSlots k ∈ shearWork := by decide
      simpa [cmp,ordinaryCutoffPorts,ne] using (start.choose_spec.1.scratch _ (scratch j hj)).2)
  change u.scan (cmp 7) = bitSymbol (decide (cutoff < desc.width)) at flag
  change m ≤ 4*w+23*desc.width+22*L+50 at testCost
  by_cases active : cutoff < desc.width
  · obtain ⟨z,F,n,hu,cost,run,done,clear,kept,growth⟩ := ordinaryChildRoute_exec ports body r g gap w W hW
      u S record dest q original input f budget (by
        intro smaller word y D reads clear saved
        let x := word ∘ layout.symm
        have entry : x ∘ layout = word := by funext k; simp [x]
        have less : child.width < node.width := by
          change r*(node.width/64) < node.width
          rw [div,aligned,← split,Nat.mul_comm r]
          exact smaller
        obtain ⟨v,G,t,user,time,run,returned,keep,empty,frame⟩ := recurse active less x y D
          (by simpa only [onTape,entry] using reads) clear saved ((saved cut outside).2.trans cutWord)
        refine ⟨v,G,t,user,time,run,?_,keep,empty,frame⟩
        have output : Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) word =
            Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x ∘ layout := by
          funext k
          rw [← entry]
          exact ordinaryOccurrenceTranspose parent r g w child eqn x k
        intro k
        rw [output]
        exact returned k) start free
    refine ⟨z,F,_,hu.trans user,?_,Exec.seq compare (Exec.cond_true (by simp [mk_var,flag,active]) run),done,clear,kept,(kept cut outside).2.trans cutWord,?_⟩
    · rw [ite_eq_left active]
      change n ≤ budget+2+2*(1+routeTime) at cost
      omega
    · simpa only [ite_eq_left active] using fun c enter exit _ hb => growth c enter exit hb
  · obtain ⟨z,F,n,hu,cost,run,done,clear,kept⟩ := stopped r g split rankPos w W hW u S record dest q original input start free
    refine ⟨z,F,_,hu.trans user,?_,Exec.seq compare (Exec.cond_false (by simp [mk_var,flag,active]) run),done,clear,kept,(kept cut outside).2.trans cutWord,?_⟩
    · rw [ite_eq_right active]
      change n ≤ C*(desc.width*(M^d*W)) at cost
      omega
    · intro c _ _ hp hb j ne
      rw [ite_eq_right active]
      obtain ⟨l,r⟩ := StackGrowthExcept.of_exec (bank 24) run hp hb j ne
      have paid := Nat.mul_le_mul_left c cost
      exact ⟨l.trans (Nat.add_le_add_left paid _),r.trans (Nat.add_le_add_left paid _)⟩

/-- Multiply the decoded spectator factors and encode their product in the
minimal binary width expected on scanner tape 53. -/
theorem ordinarySpectatorWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (u : HS T Q prime U) (S : Stacks T prime) (between afterD : ℕ)
    (left : (S.R (r 0)).length = between) (right : (S.R (r 1)).length = afterD)
    (positive : 0 < afterD) (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (r j) = []) :
    let W := between*afterD
    ∃ z t, z.user = u.user ∧ t ≤ 34*W+14 ∧
      Exec body ((Mult.ShortConv.unaryProduct (r 0) (r 1) (r 2) (r 4) (r 5)).seq
        (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)))
        (mk u S) t (mk z {S with R := Function.update (Function.update S.R (r 2)
          (List.replicate W Node.tick)) (r 3) (binSyms W.size W)}) := by
  intro W
  obtain ⟨a,m,user,paid,product⟩ := Mult.ShortConv.unaryProduct_exec (body := body)
    (a := r 0) (b := r 1) (dst := r 2) (t₁ := r 4) (t₂ := r 5) (by simp) u S
    (empty 4 (by decide)) (empty 5 (by decide))
  rw [left,right,empty 2 (by decide),List.append_nil] at product
  let D : Stacks T prime := {S with R := Function.update S.R (r 2) (List.replicate W Node.tick)}
  have free (j : Fin 10) (hj : 3 ≤ j.val) : D.R (r j) = [] := by
    have ne : j ≠ 2 := fun eq => by subst j; exact (by decide : ¬3 ≤ (2 : Fin 10).val) hj
    change Function.update _ _ _ (r j) = _
    rw [Function.update_of_ne (r.injective.ne ne),empty j (by omega)]
  obtain ⟨z,n,keep,bill,binary⟩ := unaryBinary_exec (body := body) (src := r 2) (dst := r 3) (a := r 4)
    (h := r 5) (par := r 6) (bits := r 7) (cnt := r 8) (saved := r 9) (by simp) W a D
    (by simp [D]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact free _ (by decide))
  refine ⟨z,m+n,keep.trans user,?_,Exec.seq product binary⟩
  rw [left,right,show between*(4*afterD+9)+4 = 4*(between*afterD)+9*between+4 by ring] at paid
  have le : between ≤ W := Nat.le_mul_of_pos_right _ positive
  dsimp only [W] at *
  omega

noncomputable def directorySpectatorWord {T Q : ℕ} {P U : Type} (ports : Fin 12 ↪ Fin T) : Pr P T Q prime U :=
  let r := (Fin.castAddEmb (n := 10) 2).trans ports
  (((toUnary (ports 10) (r 0) (r 4) (r 5) (r 6)).seq
        (toUnary (ports 11) (r 1) (r 4) (r 5) (r 6))).seq
        ((Mult.ShortConv.unaryProduct (r 0) (r 1) (r 2) (r 4) (r 5)).seq
        (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9))))

noncomputable def directorySpectatorState {T : ℕ} (r : Fin 12 ↪ Fin T) (b d : ℕ) (S : Stacks T prime) : Stacks T prime :=
  let W := b*d
  let factors := Function.update (Function.update S.R (r 0) (List.replicate b Node.tick)) (r 1) (List.replicate d Node.tick)
  {S with R := Function.update (Function.update factors (r 2) (List.replicate W Node.tick)) (r 3) (binSyms W.size W)}

/-- Compute the scanner's binary spectator product directly from the two
binary descriptor fields on a recursive call. -/
theorem directorySpectatorWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (ports : Fin 12 ↪ Fin T) (u : HS T Q prime U) (S : Stacks T prime) (b d : ℕ)
    (hb : 0 < b) (hd : 0 < d)
    (between : S.R (ports 10) = (FlatCoordinateSchedule.bits b).map bitSymbol)
    (afterD : S.R (ports 11) = (FlatCoordinateSchedule.bits d).map bitSymbol)
    (empty : ∀ i : Fin 10, S.R (ports (i.castAdd 2)) = []) :
    let W := b*d
    ∃ z t, z.user = u.user ∧ t ≤ 68*W+48 ∧
      Exec body (directorySpectatorWord ports)
        (mk u S) t (mk z (directorySpectatorState ports b d S)) := by
  intro W
  let r := (Fin.castAddEmb (n := 10) 2).trans ports
  let decoded := Function.update (Function.update S.R (r 0) (List.replicate b Node.tick)) (r 1) (List.replicate d Node.tick)
  obtain ⟨v,m,vu,readB,first⟩ := LabelDecode.field_exec body
    ((by decide : ([10,0,4,5,6] : List (Fin 12)).Nodup).map ports.injective) b u S between (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> first | exact empty 0 | exact empty 4 | exact empty 5 | exact empty 6)
  let B := {S with R := Function.update S.R (r 0) (List.replicate b Node.tick)}
  have free (i : Fin 10) (hi : i ≠ 0) : B.R (r i) = [] :=
    (Function.update_of_ne (r.injective.ne hi) ..).trans (empty i)
  obtain ⟨y,n,yv,readD,second⟩ := LabelDecode.field_exec body
    ((by decide : ([11,1,4,5,6] : List (Fin 12)).Nodup).map ports.injective) d v B
    ((Function.update_of_ne (ports.injective.ne (by decide : (11 : Fin 12) ≠ 0)) ..).trans afterD) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> first
        | exact free 1 (by decide) | exact free 4 (by decide) | exact free 5 (by decide) | exact free 6 (by decide))
  let D := {S with R := decoded}
  obtain ⟨z,k,zy,paid,run⟩ := ordinarySpectatorWord_exec body r y D b d
    (by simp [D,decoded]) (by simp [D,decoded]) hd (by
      intro i hi
      have h₁ : i ≠ 1 := fun eq => by subst i; contradiction
      have h₀ : i ≠ 0 := fun eq => by subst i; contradiction
      exact (Function.update_of_ne (r.injective.ne h₁) ..).trans (free i h₀))
  have lb : b ≤ W := Nat.le_mul_of_pos_right _ hd
  have ld : d ≤ W := Nat.le_mul_of_pos_left _ hb
  exact ⟨z,_,zy.trans (yv.trans vu),by change k ≤ 34*W+14 at paid; omega,Exec.seq (Exec.seq first second) run⟩

noncomputable def unaryModulusWord {T Q : ℕ} {P U : Type} (r : Fin 10 ↪ Fin T) : Pr P T Q prime U :=
  (Node.expProg 0 prime (r 0) (r 1) (r 2) (r 4) (r 5) (r 6)).seq
    (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9))

private theorem unaryModulusWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (u : HS T Q prime U) (D : Stacks T prime) (e : ℕ)
    (one : (D.R (r 0)).length = 1) (exponent : (D.R (r 1)).length = e)
    (free : ∀ j : Fin 10, 2 ≤ j.val → D.R (r j) = []) :
    let M := prime^e
    ∃ z t, z.user = u.user ∧ t ≤ 43*M+10 ∧ Exec body (unaryModulusWord r) (mk u D) t
      (mk z {D with R := Function.update (Function.update D.R (r 2) (List.replicate M Node.tick)) (r 3) (binSyms M.size M)}) := by
  intro M
  obtain ⟨b,m,user,paid,power⟩ := LabelCounts.power_exec body (one := r 0) (exponent := r 1)
    (dst := r 2) (t₁ := r 4) (t₂ := r 5) (t₃ := r 6) (by simp) u D one (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact free _ (by decide))
  rw [exponent] at paid power
  let B : Stacks T prime := {D with R := Function.update D.R (r 2) (List.replicate M Node.tick)}
  have blank (j : Fin 10) (lo : 3 ≤ j.val) (hi : j.val ≤ 9) : B.R (r j) = [] := by
    have ne : j ≠ 2 := fun eq => by subst j; exact (by decide : ¬3 ≤ (2 : Fin 10).val) lo
    change Function.update _ _ _ (r j) = _
    rw [Function.update_of_ne (r.injective.ne ne),free j (by omega)]
  obtain ⟨z,l,last,bill,binary⟩ := unaryBinary_exec (body := body) (src := r 2) (dst := r 3) (a := r 4)
    (h := r 5) (par := r 6) (bits := r 7) (cnt := r 8) (saved := r 9) (by simp) M b B
    (by simp [B]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact blank _ (by decide) (by decide))
  refine ⟨z,m+l,last.trans user,?_,Exec.seq power binary⟩
  change m ≤ 22*M at paid
  omega

noncomputable def childModulusWord {T Q : ℕ} {P U : Type} (r : Fin 10 ↪ Fin T) : Pr P T Q prime U :=
  (((Prog.act (.push (.rt (r 0)) (fun _ => Node.tick) (.push (.rt (r 1)) (fun _ => Node.tick) .done))).seq
        (unaryModulusWord r)).seq (Prog.act (.pop (.rt (r 1)) (fun v _ => v) (.pop (.rt (r 0)) (fun v _ => v) .done))))

/-- The recursive child has its predecessor in unary. Push a tick onto the
clock to obtain the exponent, and restore both borrowed tapes before returning. -/
theorem childModulusWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (u : HS T Q prime U) (S : Stacks T prime) (w : ℕ)
    (clock : (S.R (r 1)).length = w) (free : ∀ j : Fin 10, j ≠ 1 → S.R (r j) = []) :
    let M := prime^(w+1)
    ∃ z t, z.user = u.user ∧ t ≤ 43*M+12 ∧ Exec body
      (childModulusWord r) (mk u S) t
      (mk z {S with R := Function.update (Function.update S.R (r 2) (List.replicate M Node.tick)) (r 3) (binSyms M.size M)}) := by
  intro M
  let D := {S with R := Function.update (Function.update S.R (r 0) [Node.tick]) (r 1) (Node.tick :: S.R (r 1))}
  have start := Exec.act (body := body) (.push (.rt (r 0)) (fun _ => Node.tick)
    (.push (.rt (r 1)) (fun _ => Node.tick) .done)) (mk u S)
  have seed : Exec body _ (mk u S) 1 (mk u D) := start.cast rfl (by simp [Action.run,update_rt,D,free 0 (by decide)])
  obtain ⟨z,t,user,paid,run⟩ := unaryModulusWord_exec body r u D (w+1) (by simp [D])
    (by simp [D,clock]) (by
      intro j high
      have h₀ : j ≠ 0 := fun eq => by subst j; contradiction
      have h₁ : j ≠ 1 := fun eq => by subst j; contradiction
      simpa [D,Function.update_of_ne (r.injective.ne h₀),Function.update_of_ne (r.injective.ne h₁)] using free j h₁)
  let B := {D with R := Function.update (Function.update D.R (r 2) (List.replicate M Node.tick)) (r 3) (binSyms M.size M)}
  let clear : Act T Q prime U := .pop (.rt (r 1)) (fun v _ => v) (.pop (.rt (r 0)) (fun v _ => v) .done)
  refine ⟨z,1+t+1,user,by omega,Exec.seq (Exec.seq seed run) ((Exec.act (body := body) clear (mk z B)).cast rfl ?_)⟩
  simp [clear,Action.run,update_rt,B,D]
  congr 2
  funext j
  by_cases a : j = r 0
  · subst j; simp [free 0 (by decide)]
  by_cases b : j = r 1
  · subst j; simp
  by_cases c : j = r 2
  · subst j; simp
  by_cases d : j = r 3
  · subst j; simp
  simp [Function.update_of_ne,a,b,c,d]

/-- Generate the scanner modulus from the normalized binary precision header.
The program writes its own unit seed before exponentiation. -/
theorem ordinaryModulusWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 11 ↪ Fin T) (u : HS T Q prime U) (initial : Stacks T prime) (w : ℕ)
    (precision : initial.R (r 10) = (FlatCoordinateSchedule.bits (w+1)).map bitSymbol)
    (fresh : ∀ j : Fin 11, j.val ≤ 9 → initial.R (r j) = []) :
    let M := prime^(w+1)
    ∃ z n, z.user = u.user ∧ n ≤ 60*M+28 ∧
      let S : Stacks T prime := {initial with R := Function.update initial.R (r 0) [Node.tick]}
      Exec body ((Prog.act (.push (.rt (r 0)) (fun _ => Node.tick) .done)).seq ((toUnary (r 10) (r 1) (r 4) (r 5) (r 6)).seq
        ((Node.expProg 0 prime (r 0) (r 1) (r 2) (r 4) (r 5) (r 6)).seq
        (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)))))
        (mk u initial) n (mk z {S with R := Function.update (Function.update (Function.update S.R
          (r 1) (List.replicate (w+1) Node.tick)) (r 2) (List.replicate M Node.tick)) (r 3) (binSyms M.size M)}) := by
  intro M
  let S : Stacks T prime := {initial with R := Function.update initial.R (r 0) [Node.tick]}
  have seed := Exec.act (body := body) (.push (.rt (r 0)) (fun _ => Node.tick) .done) (mk u initial)
  have start : (Action.push (.rt (r 0)) (fun _ => Node.tick) .done : Act T Q prime U).run (mk u initial) =
      mk u S := by simp [Action.run,update_rt,S,fresh 0 (by decide)]
  rw [start] at seed
  have one : (S.R (r 0)).length = 1 := by simp [S]
  have empty (j : Fin 11) (lo : 1 ≤ j.val) (hi : j.val ≤ 9) : S.R (r j) = [] := by
    have ne : j ≠ 0 := fun eq => by subst j; exact (by decide : ¬1 ≤ (0 : Fin 11).val) lo
    exact (Function.update_of_ne (r.injective.ne ne) ..).trans (fresh j hi)
  obtain ⟨a,t,keep,price,decode⟩ := LabelDecode.field_exec body (src := r 10) (dst := r 1)
    (a := r 4) (b := r 5) (c := r 6) (by simp) (w+1) u S (by simpa [S] using precision) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact empty _ (by decide) (by decide))
  let D : Stacks T prime := {S with R := Function.update S.R (r 1) (List.replicate (w+1) Node.tick)}
  have free (j : Fin 11) (lo : 2 ≤ j.val) (hi : j.val ≤ 9) : D.R (r j) = [] := by
    have ne : j ≠ 1 := fun eq => by subst j; exact (by decide : ¬2 ≤ (1 : Fin 11).val) lo
    change Function.update _ _ _ (r j) = _
    rw [Function.update_of_ne (r.injective.ne ne),empty j (by omega) hi]
  obtain ⟨z,m,user,paid,run⟩ := unaryModulusWord_exec body ((Fin.castAddEmb 1).trans r) a D (w+1)
    (by change (D.R (r 0)).length = 1; simpa [D] using one)
    (by change (D.R (r 1)).length = _; simp [D]) (fun j hj => free (j.castAdd 1) hj (by change j.val ≤ 9; omega))
  refine ⟨z,1+(t+m),user.trans keep,?_,Exec.seq seed (Exec.seq decode run)⟩
  have size : w+1 ≤ M := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le
  omega

/-- Place each local owner program on the same permanent owners and a
disjoint private bank, even when its local owner slots are scattered. -/
noncomputable def idlePassBank {owners n : ℕ} (width : Fin n → ℕ) (k : Fin n)
    (slots : Fin owners ↪ Fin (width k)) :=
  (returnChartBank slots (Function.Embedding.refl _)).trans (Fallback.Record.exchangeBank owners width k)

theorem idlePassBank_owner {owners n : ℕ} (width : Fin n → ℕ) (k : Fin n)
    (slots : Fin owners ↪ Fin (width k)) (i : Fin owners) :
    idlePassBank width k slots (slots i) = i.castAdd _ := by
  unfold idlePassBank
  rw [Function.Embedding.trans_apply,returnChartBank_selected,Fallback.Record.exchangeBank_shared]
  rfl

/-- Assemble the initial stacks, storing the common owners once. Unused
positions in the occurrence banks start blank. -/
noncomputable def idlePassStacks {owners n : ℕ} (width : Fin n → ℕ)
    (slots : ∀ k, Fin owners ↪ Fin (width k)) (shared : Stacks owners prime)
    (entry : ∀ k, Stacks (width k) prime) :
    Stacks (owners + Fintype.card (Σ j, Fin (width j))) prime := by
  let decode := (Fintype.equivFin (Σ j, Fin (width j))).symm
  classical
  let bank (common : Fin owners → List (Fin (prime+4))) (words : ∀ j, Fin (width j) → List (Fin (prime+4))) :
      Fin (owners + Fintype.card (Σ j, Fin (width j))) → List (Fin (prime+4)) :=
    Fin.addCases common fun i =>
      let a := decode i
      if ∃ t, slots a.1 t = a.2 then [] else words a.1 a.2
  exact ⟨shared.inp,shared.out,bank shared.L (fun j => (entry j).L),bank shared.R (fun j => (entry j).R)⟩

theorem idlePassStacks_view {owners n : ℕ} (width : Fin n → ℕ)
    (slots : ∀ k, Fin owners ↪ Fin (width k)) (shared : Stacks owners prime)
    (entry : ∀ k, Stacks (width k) prime) (k : Fin n)
    (common : embStk (slots k) (entry k) = shared) :
    embStk (idlePassBank width k (slots k)) (idlePassStacks width slots shared entry) = entry k := by
  subst shared
  apply Stacks.ext
  · rfl
  · rfl
  all_goals
    funext j
    by_cases used : ∃ i, slots k i = j
    · obtain ⟨i,rfl⟩ := used
      simp [embStk,Function.comp_apply,idlePassBank_owner,idlePassStacks]
    · have place : idlePassBank width k (slots k) j =
          Fin.natAdd owners (Fallback.Record.exchangeScratch width k j) := by
        unfold idlePassBank
        rw [Function.Embedding.trans_apply,returnChartBank_private _ _ j (fun i h => used ⟨i,h⟩),
          Fallback.Record.exchangeBank_private]
      have decode : (Fintype.equivFin (Σ a, Fin (width a))).symm (Fallback.Record.exchangeScratch width k j) =
          ⟨k,j⟩ := (Fintype.equivFin (Σ a, Fin (width a))).symm_apply_apply ⟨k,j⟩
      simp only [embStk,Function.comp_apply,place,idlePassStacks,Fin.addCases_right]
      rw [decode]
      simp [used]

/-- All local control states fit the maximum over the finite occurrence list. -/
theorem idlePass_fits {n : ℕ} (states : Fin n → ℕ) (k : Fin n) :
    states k ≤ Finset.univ.sup states := Finset.le_sup (Finset.mem_univ k)

/-- Recursive calls carry their occurrence index in the common procedure table. -/
noncomputable def idlePassBody {owners n : ℕ} {P U : Type} (width states : Fin n → ℕ)
    (positive : ∀ k, 0 < states k) (slots : ∀ k, Fin owners ↪ Fin (width k))
    (body : ∀ k, P → Pr P (width k) (states k) prime U) (f : Fin n × P) :
    Pr (Fin n × P) (owners + Fintype.card (Σ j, Fin (width j))) (Finset.univ.sup states) prime U :=
  statePlacedPr (idlePassBank width f.1 (slots f.1)) (idlePass_fits states f.1) (positive f.1)
    (Prod.mk f.1) (body f.1 f.2)

/-- One normalization step installs the local control state. The resulting run
preserves both stacks of every other occurrence's private tapes. -/
theorem idlePassBank_exec {owners n : ℕ} {P U : Type} (width states : Fin n → ℕ) (k : Fin n)
    (positive : ∀ j, 0 < states j) (slots : ∀ j, Fin owners ↪ Fin (width j))
    (body : ∀ j, P → Pr P (width j) (states j) prime U)
    (p : Pr P (width k) (states k) prime U) (v : HS _ (Finset.univ.sup states) prime U) (S : Stacks _ prime)
    (z : HS (width k) (states k) prime U) (D : Stacks (width k) prime) (t : ℕ) :
    let bank := idlePassBank width k (slots k)
    Exec (body k) p (mk (stateLiftDown (positive k) (embDn bank v)) (embStk bank S)) t (mk z D) →
    ∃ u F, Exec (idlePassBody width states positive slots body)
      (statePlacedNormalized bank (idlePass_fits states k) (positive k) (Prod.mk k) p)
      (mk v S) (1+t) (mk u F) ∧ u.user = z.user ∧ embStk bank F = D ∧
      ∀ j, j ≠ k → ∀ a : Fin (width j),
        let h := Fin.natAdd owners (Fallback.Record.exchangeScratch width j a)
        F.L h = S.L h ∧ F.R h = S.R h := by
  intro bank run
  obtain ⟨u,_,user,exec⟩ := statePlaced_exec_normalized bank bank.injective (idlePass_fits states k)
    (positive k) (Prod.mk k) (body' := idlePassBody width states positive slots body) (fun _ => rfl) v S run
  refine ⟨u,_,exec,user,embStk_ovr bank.injective _ _,fun j ne a => embOvr_off _ _ (fun b => ?_)⟩
  exact Fallback.Record.exchangeBank_avoids owners width (Ne.symm ne) _ a

/-- Sequence the physical passes on the idle's distinct owners. Each pass may
return a different representation of the tape bank and has its own time bound. -/
theorem idleCopies_exec {T Q : ℕ} {P U α : Type} (i : Fin 9)
    (body : P → Pr P T Q prime U) (program : (Fin 32 × Fin 5) × Fin 222 → Pr P T Q prime U)
    (budget : (Fin 32 × Fin 5) × Fin 222 → ℝ)
    (prepared : (Fin 32 × Fin 5) × Fin 222 → List ((Fin 32 × Fin 5) × Fin 222) → Stacks T prime → Prop)
    (ready : List ((Fin 32 × Fin 5) × Fin 222) → (Fin 142081 → α) → Stacks T prime → Prop)
    (effect : (Fin 32 × Fin 5) × Fin 222 → α → α → Prop)
    (pass : ∀ k past rest x S (u : HS T Q prime U), past ++ k::rest = idleCopies → ready past x S → prepared k past S →
      ∃ y D z n, Exec body (program k) (mk u S) n (mk z D) ∧ (n : ℝ) ≤ budget k ∧
        z.user = u.user ∧ ready (past++[k]) y D ∧ (∀ a, a ≠ k → prepared a past S → prepared a (past++[k]) D) ∧
        effect k (x (idleTape i k)) (y (idleTape i k)) ∧
        ∀ j, j ≠ idleTape i k → y j = x j)
    (x : Fin 142081 → α) (S : Stacks T prime) (u : HS T Q prime U) (input : ready [] x S) (frames : ∀ k, prepared k [] S) :
    ∃ y D z n, Exec body (Prog.seqList (idleCopies.map program)) (mk u S) n (mk z D) ∧
      (n : ℝ) ≤ (idleCopies.map budget).sum + 1 ∧ z.user = u.user ∧ ready idleCopies y D ∧
      (∀ k, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
      ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j := by
  have run (past ks : List ((Fin 32 × Fin 5) × Fin 222)) (distinct : ks.Nodup) (order : past++ks = idleCopies)
      (x : Fin 142081 → α) (S : Stacks T prime) (u : HS T Q prime U) (input : ready past x S) (frames : ∀ k ∈ ks, prepared k past S) :
      ∃ y D z n, Exec body (Prog.seqList (ks.map program)) (mk u S) n (mk z D) ∧
        (n : ℝ) ≤ (ks.map budget).sum + 1 ∧ z.user = u.user ∧ ready idleCopies y D ∧
        (∀ k ∈ ks, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
        ∀ j, (∀ k ∈ ks, j ≠ idleTape i k) → y j = x j := by
    induction ks generalizing past x S u with
    | nil =>
      rw [List.append_nil] at order
      exact ⟨x,S,u,1,Exec.act .done _,by simp,rfl,order ▸ input,by simp,fun _ _ => rfl⟩
    | cons k ks ih =>
      obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
      obtain ⟨v,B,t,m,firstRun,paid,keep,next,preserve,acted,off⟩ := pass k past ks x S u order input (frames k List.mem_cons_self)
      obtain ⟨y,D,z,n,rest,bill,user,final,acts,kept⟩ := ih (past++[k]) tail (by simpa using order) v B t next
        (fun a ha => preserve a (fun h => fresh (h ▸ ha)) (frames a (List.mem_cons_of_mem _ ha)))
      refine ⟨y,D,z,m+n,Exec.seq firstRun rest,?_,user.trans keep,final,?_,?_⟩
      · simp only [List.map_cons,List.sum_cons,Nat.cast_add]
        linarith
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | member
        · rw [kept (idleTape i j) (fun a ha => (idleTape_injective i).ne (fun h => fresh (h.symm ▸ ha)))]
          exact acted
        · rw [← off _ ((idleTape_injective i).ne (fun h => fresh (h ▸ member)))]
          exact acts j member
      · intro j outside
        exact (kept j (fun a ha => outside a (List.mem_cons_of_mem _ ha))).trans
          (off j (outside k List.mem_cons_self))
  obtain ⟨y,D,z,n,exec,paid,user,final,acts,kept⟩ := run [] idleCopies
    (stageRuns_nodup.product (List.nodup_finRange _)) rfl x S u input (fun k _ => frames k)
  refine ⟨y,D,z,n,exec,paid,user,final,fun k => acts k ?_,fun j h => kept j (fun a _ => h a)⟩
  exact List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩

/-- Physical cell of a rational address in the fixed block, label and spectator slice. -/
noncomputable def ordinaryRoleAddress {w R W parents : ℕ} (parent : Fin 64 → ZMod (prime^(w+1)))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1))
    (count : parents*(prime^(w+1))^(64*64) = R) (spectator : Fin W) :
    (Axis ⊕ Axis → ℚ) → Fin (R*((prime^(w+1))^128*W)) :=
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let axes := Equiv.sumCongr stageAxis.symm stageAxis.symm
    let frame := fromBlocks (diagonal parent*g) 0 0 (M8.ReversedExchange.rev 64*g)
    let row : Fin R := (finProdFinEquiv (block,LabelAddress.address g)).cast count
    let pack := fun x => finProdFinEquiv (row,index ((frame.mulVec (x ∘ axes)) ∘ finSumFinEquiv.symm) spectator)
    pack ∘ addressMod M

/-- All selected owners realize the compiled idle at the same packed address
for each live label, inherited block and spectator. -/
theorem ordinaryIdle_read {w R W parents : ℕ} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1)) (live : IsUnit g)
    (count : parents*(prime^(w+1))^(64*64) = R) (spectator : Fin W)
    (before after : Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2)
    (reads : ∀ k, OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val)
      (before (idleTape i k)) (after (idleTape i k)))
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → after j = before j) :
    let address := ordinaryRoleAddress parent block g count spectator
    readRoles address after = (Piece.remainder i.val).run (readRoles address before) := by
  dsimp only [ordinaryRoleAddress]
  apply idleCopies_modular_read (w+1) i _ before after _ off
  intro k e P x
  rw [idleExchange_axes _ (port_checked _ (idleRole i k).port.isLt) e.1 e.2]
  exact (reads k).exchange units block g live count (x ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) spectator

/-- An idle also preserves a lane-specific choice of live label, spectator
and inherited block. Each remainder acts within a single role. -/
theorem ordinaryIdle_readLanes {w R W parents : ℕ} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (block : BankLane → Fin parents) (g : BankLane → LabelPadding.Label 64 (w+1))
    (live : ∀ lane, IsUnit (g lane)) (count : parents*(prime^(w+1))^(64*64) = R)
    (spectator : BankLane → Fin W)
    (before after : Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2)
    (reads : ∀ k, OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val)
      (before (idleTape i k)) (after (idleTape i k)))
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → after j = before j) :
    let address := fun lane => ordinaryRoleAddress parent (block lane) (g lane) count (spectator lane)
    readLanes address after = (Piece.remainder i.val).run (readLanes address before) := by
  intro address
  apply remainder_readLanes
  intro lane
  exact ordinaryIdle_read i parent units (block lane) (g lane) (live lane)
    count (spectator lane) before after reads off

/-- Run the installed passes on their common bank and read the compiled idle
from the very same final store and summed step bound. -/
theorem ordinaryIdle_exec {w R W parents T Q : ℕ} {P U : Type} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (count : parents*(prime^(w+1))^(64*64) = R)
    (body : P → Pr P T Q prime U) (program : (Fin 32 × Fin 5) × Fin 222 → Pr P T Q prime U)
    (budget : (Fin 32 × Fin 5) × Fin 222 → ℝ)
    (prepared : (Fin 32 × Fin 5) × Fin 222 → List ((Fin 32 × Fin 5) × Fin 222) → Stacks T prime → Prop)
    (ready : List ((Fin 32 × Fin 5) × Fin 222) → (Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2) → Stacks T prime → Prop)
    (pass : ∀ k past rest x S (u : HS T Q prime U), past ++ k::rest = idleCopies → ready past x S → prepared k past S →
      ∃ y D z n, Exec body (program k) (mk u S) n (mk z D) ∧ (n : ℝ) ≤ budget k ∧
        z.user = u.user ∧ ready (past++[k]) y D ∧ (∀ a, a ≠ k → prepared a past S → prepared a (past++[k]) D) ∧
        OriginalPortReads R W parents (idleInterval i k.2) parent
          (port (idleRole i k).port.val) (x (idleTape i k)) (y (idleTape i k)) ∧
        ∀ j, j ≠ idleTape i k → y j = x j)
    (x S u) (input : ready [] x S) (frames : ∀ k, prepared k [] S) :
    ∃ y D z n, Exec body (Prog.seqList (idleCopies.map program)) (mk u S) n (mk z D) ∧
      (n : ℝ) ≤ (idleCopies.map budget).sum + 1 ∧ z.user = u.user ∧ ready idleCopies y D ∧
      (∀ j, (∀ k, j ≠ idleTape i k) → y j = x j) ∧
      ∀ block g, IsUnit g → ∀ spectator, let address := ordinaryRoleAddress parent block g count spectator
        readRoles address y = (Piece.remainder i.val).run (readRoles address x) := by
  obtain ⟨y,D,z,n,exec,paid,user,final,acts,kept⟩ := idleCopies_exec i body program budget prepared ready
    (fun k => OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val))
    pass x S u input frames
  exact ⟨y,D,z,n,exec,paid,user,final,kept,fun block g live spectator =>
    ordinaryIdle_read i parent units block g live count spectator x y acts kept⟩

/-- The physical occurrence in the directory schedule for a given port and copy. -/
def idleCopyIndex (k : (Fin 32 × Fin 5) × Fin 222) : Fin idleCopies.length :=
  ⟨idleCopies.idxOf k,List.idxOf_lt_length_iff.mpr (List.mem_flatMap.mpr
    ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩)⟩

theorem idleCopyIndex_get (k : (Fin 32 × Fin 5) × Fin 222) :
    idleCopies[(idleCopyIndex k).val] = k := List.getElem_idxOf ..

theorem idleCopyIndex_at (j : Fin idleCopies.length) : idleCopyIndex idleCopies[j.val] = j := by
  apply Fin.ext
  exact (show idleCopies.Nodup from stageRuns_nodup.product (List.nodup_finRange _)).idxOf_getElem j j.isLt

/-- Local interval runs suffice to execute the idle on a common owner bank. -/
def PlacedIdleExecution {w R W parents jobs : ℕ} {P U : Type} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (count : parents*(prime^(w+1))^(64*64) = R)
    (copy : Fin jobs → (Fin 32 × Fin 5) × Fin 222) (index : ((Fin 32 × Fin 5) × Fin 222) → Fin jobs)
    (width states : Fin jobs → ℕ) (positive : ∀ j, 0 < states j)
    (slots : ∀ j, Fin 142081 ↪ Fin (width j))
    (body : ∀ j, P → Pr P (width j) (states j) prime U)
    (program : ∀ j, Pr P (width j) (states j) prime U)
    (reserve : ℝ) (budget growth : Fin jobs → ℝ) (entry : ∀ j, Stacks (width j) prime)
    (shared : Stacks 142081 prime) : Prop :=
    let N := R*((prime^(w+1))^128*W)
    let privateReady := fun j (S : Stacks (width j) prime) =>
      ∀ a, (∀ l, slots j l ≠ a) → S.L a = (entry j).L a ∧ S.R a = (entry j).R a
    let stock := fun (j : Fin jobs) (S : Stacks (width j) prime) l =>
      ((S.L (slots j l)).length+(S.R (slots j l)).length : ℕ)
    (∀ j, 0 ≤ growth j) →
    (∀ j (x : Fin 142081 → Fin N → ZMod 2) (S : Stacks (width j) prime) (a : HS _ _ prime U),
      RepT (phaseOwners x) (embStk (slots j) S).L (embStk (slots j) S).R → privateReady j S →
      ∃ y D z n, Exec (body j) (program j) (mk a S) n (mk z D) ∧ (n : ℝ) ≤ budget j+6*(stock j S (idleTape i (copy j)) : ℝ) ∧
        z.user = a.user ∧ RepT (phaseOwners y) (embStk (slots j) D).L (embStk (slots j) D).R ∧
        let k := copy j
        (stock j D (idleTape i k) : ℝ) ≤ reserve+growth j ∧
        (∀ l, l ≠ idleTape i k → (stock j D l : ℝ) ≤ (stock j S l : ℝ)+growth j) ∧
        OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val)
          (x (idleTape i k)) (y (idleTape i k)) ∧ ∀ l, l ≠ idleTape i k → y l = x l) →
    ∀ (x : Fin 142081 → Fin N → ZMod 2), RepT (phaseOwners x) shared.L shared.R →
    let start := idlePassStacks width slots shared entry
    let localPass := fun k => let j := index k
      statePlacedNormalized (idlePassBank width j (slots j)) (idlePass_fits states j) (positive j) (Prod.mk j) (program j)
    let charge := fun k => let l := idleTape i k
      let earlier := (idleCopies.take (idleCopies.idxOf k)).map (fun a => growth (index a))
      1+budget (index k)+6*((((shared.L l).length+(shared.R l).length : ℕ) : ℝ)+earlier.sum)
    ∀ u, ∃ y D z n, Exec (idlePassBody width states positive slots body)
      (Prog.seqList (idleCopies.map localPass)) (mk u start) n (mk z D) ∧
      (n : ℝ) ≤ (idleCopies.map charge).sum+1 ∧ z.user = u.user ∧
      (RepT (phaseOwners y) (fun l => D.L (l.castAdd _)) (fun l => D.R (l.castAdd _)) ∧
      (∀ l, (((D.L (l.castAdd _)).length+(D.R (l.castAdd _)).length : ℕ) : ℝ) ≤
        max (((shared.L l).length+(shared.R l).length : ℕ) : ℝ) reserve+
          (idleCopies.map (fun a => growth (index a))).sum)) ∧
      (∀ l, (∀ k, l ≠ idleTape i k) → y l = x l) ∧
      ∀ block g, IsUnit g → ∀ spectator, let address := ordinaryRoleAddress parent block g count spectator
        readRoles address y = (Piece.remainder i.val).run (readRoles address x)

private theorem placedIdleExecution_of_passes {w R W parents jobs : ℕ} {P U : Type} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (count : parents*(prime^(w+1))^(64*64) = R)
    (copy : Fin jobs → (Fin 32 × Fin 5) × Fin 222) (index : ((Fin 32 × Fin 5) × Fin 222) → Fin jobs)
    (selected : ∀ k, copy (index k) = k)
    (width states : Fin jobs → ℕ) (positive : ∀ j, 0 < states j)
    (slots : ∀ j, Fin 142081 ↪ Fin (width j))
    (body : ∀ j, P → Pr P (width j) (states j) prime U)
    (program : ∀ j, Pr P (width j) (states j) prime U)
    (reserve : ℝ) (budget growth : Fin jobs → ℝ) (entry : ∀ j, Stacks (width j) prime)
    (shared : Stacks 142081 prime) (common : ∀ j, embStk (slots j) (entry j) = shared) :
    PlacedIdleExecution (W := W) i parent count copy index width states positive slots body program reserve budget growth entry shared := by
  unfold PlacedIdleExecution
  intro N privateReady stock nonneg pass x represented start localPass charge u
  let bank := fun j => idlePassBank width j (slots j)
  let representedBy := fun (x : Fin 142081 → Fin N → ZMod 2) (S : Stacks _ prime) =>
    RepT (phaseOwners x) (fun l => S.L (l.castAdd (Fintype.card (Σ j, Fin (width j)))))
      (fun l => S.R (l.castAdd _))
  let observed := fun (S : Stacks (142081+Fintype.card (Σ j, Fin (width j))) prime) (l : Fin 142081) =>
    (S.L (l.castAdd _)).length+(S.R (l.castAdd _)).length
  let ready := fun (past : List ((Fin 32 × Fin 5) × Fin 222)) x S => representedBy x S ∧
    ∀ l, (observed S l : ℝ) ≤ max (((shared.L l).length+(shared.R l).length : ℕ) : ℝ) reserve+
      (past.map (fun a => growth (index a))).sum
  let prepared := fun k (past : List ((Fin 32 × Fin 5) × Fin 222)) S => privateReady (index k) (embStk (bank (index k)) S) ∧
    (observed S (idleTape i k) : ℝ) ≤ (((shared.L (idleTape i k)).length+(shared.R (idleTape i k)).length : ℕ) : ℝ)+
      (past.map (fun a => growth (index a))).sum
  refine ordinaryIdle_exec i parent units count _ localPass _ prepared ready ?_ x start u ?_ ?_
  · intro k past rest words S a order rep fresh
    let j := index k
    obtain ⟨y,D,z,n,run,time,user,output,returned,grows,act,kept⟩ := pass j words (embStk (bank j) S) _
      (by simpa [representedBy,embStk,bank,Function.comp_def,idlePassBank_owner] using rep.1) fresh.1
    obtain ⟨v,F,lifted,same,view,off⟩ := idlePassBank_exec width states j positive slots body (program j) a S z D n run
    have oldStock (l) : stock j (embStk (bank j) S) l = observed S l := by
      simp [stock,observed,embStk,bank,Function.comp_def,idlePassBank_owner]
    have newStock (l) : stock j D l = observed F l := by
      rw [← view]
      simp [stock,observed,embStk,Function.comp_def,idlePassBank_owner]
    refine ⟨y,F,v,1+n,lifted,?_,same.trans user,?_,?_,?_,?_⟩
    · have distinct : (past++k::rest).Nodup := order ▸ stageRuns_nodup.product (List.nodup_finRange _)
      have absent : k ∉ past := fun h => (List.disjoint_of_nodup_append distinct) h List.mem_cons_self
      have pos : idleCopies.idxOf k = past.length := by simp [← order,List.idxOf_append,absent]
      have earlier : idleCopies.take (idleCopies.idxOf k) = past := by rw [pos,← order]; simp
      have prior := fresh.2
      change (observed S (idleTape i k) : ℝ) ≤ _ at prior
      rw [oldStock,selected] at time
      dsimp only [charge]
      rw [earlier,Nat.cast_add,Nat.cast_one]
      change (n : ℝ) ≤ budget (index k)+6*(observed S (idleTape i k) : ℝ) at time
      linarith
    · rw [← view] at output
      refine ⟨by simpa [representedBy,embStk,Function.comp_def,idlePassBank_owner] using output,?_⟩
      intro l
      simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      by_cases hit : l = idleTape i k
      · subst l
        rw [newStock,selected] at returned
        have extra : 0 ≤ (past.map (fun a => growth (index a))).sum :=
          List.sum_nonneg (fun x hx => by obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx; exact nonneg _)
        have base := le_max_right (((shared.L (idleTape i k)).length+(shared.R (idleTape i k)).length : ℕ) : ℝ) reserve
        linarith only [returned,base,extra]
      · have delta := grows l (by rwa [selected])
        rw [newStock,oldStock] at delta
        exact delta.trans (by simpa only [add_assoc] using add_le_add_left (rep.2 l) (growth j))
    · intro k' ne old
      refine ⟨?_,?_⟩
      · intro l outside
        have diff : index k' ≠ j := fun eq => ne (by
          rw [← selected k',← selected k]
          exact congrArg (fun h : Fin jobs => copy h) eq)
        have loc : bank (index k') l = Fin.natAdd 142081 (Fallback.Record.exchangeScratch width (index k') l) := by
          unfold bank idlePassBank
          rw [Function.Embedding.trans_apply,returnChartBank_private _ _ _ outside,Fallback.Record.exchangeBank_private]
        obtain ⟨left,right⟩ := off _ diff l
        obtain ⟨priorL,priorR⟩ := old.1 l outside
        change F.L (bank _ l) = _ ∧ F.R (bank _ l) = _
        change S.L (bank _ l) = _ at priorL
        change S.R (bank _ l) = _ at priorR
        rw [loc] at priorL priorR ⊢
        exact ⟨left.trans priorL,right.trans priorR⟩
      · have changeStock := grows (idleTape i k') (by rw [selected]; exact (idleTape_injective i).ne ne)
        rw [oldStock,newStock] at changeStock
        have before := old.2
        change (observed F (idleTape i k') : ℝ) ≤ _ + ((past++[k]).map _).sum
        simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
        exact changeStock.trans (by simpa only [add_assoc] using add_le_add_left before (growth j))
    · simpa only [j,selected] using act
    · simpa only [j,selected] using kept
  · refine ⟨by simpa [representedBy,start,idlePassStacks] using represented,?_⟩
    intro l
    simpa [observed,start,idlePassStacks] using le_max_left (((shared.L l).length+(shared.R l).length : ℕ) : ℝ) reserve
  · intro k
    refine ⟨?_,by simp [observed,start,idlePassStacks]⟩
    change privateReady _ (embStk (bank _) start)
    rw [show embStk (bank (index k)) start = entry _ from idlePassStacks_view width slots shared entry _ (common _)]
    exact fun _ _ => ⟨rfl,rfl⟩

/-- Install the actual directory occurrences on a common owner bank. Later
passes inherit the output words and retain their own initial private stacks. -/
theorem ordinaryIdle_placed_exec {w R W parents : ℕ} {P U : Type} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (count : parents*(prime^(w+1))^(64*64) = R)
    (width states : Fin idleCopies.length → ℕ) (positive : ∀ j, 0 < states j)
    (slots : ∀ j, Fin 142081 ↪ Fin (width j))
    (body : ∀ j, P → Pr P (width j) (states j) prime U)
    (program : ∀ j, Pr P (width j) (states j) prime U)
    (reserve : ℝ) (budget growth : Fin idleCopies.length → ℝ) (entry : ∀ j, Stacks (width j) prime)
    (shared : Stacks 142081 prime) (common : ∀ j, embStk (slots j) (entry j) = shared) :
    PlacedIdleExecution (W := W) i parent count (fun j => idleCopies[j.val]) idleCopyIndex width states positive slots body program reserve budget growth entry shared :=
  placedIdleExecution_of_passes i parent units count _ idleCopyIndex idleCopyIndex_get width states positive
    slots body program reserve budget growth entry shared common

open Fallback in
/-- Choose the scheduled child branch and correct the returned columns with the caller's pivots. -/
noncomputable def weightedOrdinaryProgram [M8.Machine.Net] {P U : Type} {T : ℕ}
    (caller : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ caller j) (r g : ℕ) (f : P) : Pr P T columnCapacity prime U :=
  let placement := correctionColumnPlacement caller work apart
  let ports := columnPorts.trans placement
  let bank := columnBank.trans placement
  let cmp := ordinaryCutoffPorts bank (placement (Fin.last _)) (fun i => placement.injective.ne (Fin.castSucc_ne_last _))
  let pass := fun js => statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule ((r+g)+(r+g)) js)
  let is := ordinaryChildPackSchedule r g
  let emit := fun i j => let slot := correctionSlot r i j
                         readMatrixWord slot.2.val ((callerCorrectionPorts slot.1).trans caller)
  let write := LabelTraversal.sequence (fun i => LabelTraversal.sequence (emit i) (List.finRange 128)) (List.finRange 128)
  let prep := (bzero (caller 2) (caller 58) (caller 59)).seq (write.seq (bclear (caller 58)))
  let correction := (prep.seq (placedDiagonalPairs placement 127)).seq (dropWords (bank 2) (bank 34) (bank 0) (128*128))
  ((ordinaryCutoffTest cmp r).seq (.cond (fun u => symBit (u.scan (cmp 7)))
    ((pass is).seq ((Prog.call f).seq (pass is.reverse))) (pass (stoppedParentSchedule r g)))).seq correction

open Fallback RecursiveInterchangeLayout in
/-- Execute the scheduled ordinary exchange and apply the archived parent pivots. -/
theorem weightedOrdinaryChildDispatch_exec [M8.Machine.Net] {P U : Type} {T : ℕ}
    (caller : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ caller j) (body : P → Pr P T columnCapacity prime U) :
    let placement := correctionColumnPlacement caller work apart
    let ports := columnPorts.trans placement
    let cut := placement (Fin.last _)
    ∃ C : ℕ, ∀ (node : Descriptor) (i : Fin nodeChildren5.length) w (aligned : node.width = 64*(w+1)),
      let r := nodeChildren5[i.val]
      let g := 64-r
      let parent := role node 142080
      let W := CopyChildLayout.spectators parent
      0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let is := ordinaryChildPackSchedule r g
      let routeTime := (is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1
      let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
      let clean := fun (S : Stacks T prime) => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → S.L (ports k) = [] ∧ S.R (ports k) = []
      ∀ (v : HS T columnCapacity prime U) (S : Stacks T prime)
        (dest : ℤ → Fin 4) (q : ℤ)
        (before : Fin (M^d*W) → ZMod 2)
        (f : P) (budget cutoff L : ℕ),
      let saved := fun D : Stacks T prime => ∀ j, (∀ i, ports i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j
      let desc := ordinaryChildDescriptor r g w W
      let child := scheduledChild prime node i
      let same : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child := by
        simp only [child,scheduledChild,aligned,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
        rfl
      let layout := (ordinaryScheduledLayout parent r g w).trans (finCongr (congrArg (volume prime) same))
      let onTape := fun (word : Fin (volume prime child) → ZMod 2) (D : Stacks T prime) =>
        ∀ z, readAt blank (D.L (bank 24)) (D.R (bank 24)) z =
          M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (v := desc) (word ∘ layout) z
      ∀ pivot : Fin r → (ZMod M)ˣ,
      (∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) →
      S.R (caller 55) = (List.ofFn fun k => binSyms M.size (pivot k : ZMod M).val).flatten →
      S.R (caller 56) = (List.ofFn fun k => binSyms M.size (pivot k).inv.val).flatten →
      (∀ k ∈ ([58,59,61,62,63] : List (Fin 64)), S.R (caller k) = []) →
      cutoff < 2^L → desc.width.size ≤ L →
      S.R cut = binSyms L cutoff →
      (cutoff < desc.width → child.width < node.width → ∀ word u D, onTape word D → clean D → saved D → D.R cut = binSyms L cutoff → ∃ y G t, y.user = u.user ∧ t ≤ budget ∧
        Exec body (body f) (mk u D) t (mk y G) ∧
        onTape (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word) G ∧
        (∀ j : Fin 35, j ≠ 24 → G.L (bank j) = D.L (bank j) ∧ G.R (bank j) = D.R (bank j)) ∧ clean G ∧ saved G) →
      S.R (caller 2) = binSyms M.size M → S.R (caller 53) = binSyms W.size W →
      S.R (caller 28) = binSyms 1 1 → S.R (caller 44) = binSyms M.size (1 : ZMod M).val →
      (S.R (caller 45)).length = w →
      (∀ k ∈ shearWork, S.L (work (columnBank k)) = [] ∧ S.R (work (columnBank k)) = []) →
      (∀ z, readAt blank (S.L (caller 24)) (S.R (caller 24)) (z-0) =
        RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ before)) z)) →
      (∀ z, readAt blank (S.L (caller 25)) (S.R (caller 25)) (z-q) = RadixToBinary.binaryEncoding.encode (dest z)) →
      clean S → ∃ z F n after, z.user = v.user ∧
        n ≤ 4*w+23*desc.width+22*L+51+(if cutoff < desc.width then budget+2+2*(1+routeTime) else C*(desc.width*(M^d*W))) +
          ordinaryCorrectionTime U w W M.size W.size ∧
        Exec body (weightedOrdinaryProgram caller work apart r g f) (mk v S) n (mk z F) ∧
        (∀ (hg tg : Fin g → ZMod M) (x : IntegerMultBounds.Swap.Shear.State (Fin r) (ZMod M)) (j : Fin W),
          let address := fun y => let t := childFields hg tg y
                                  FlatCoordinateLayout.index (Fin.append t.1 t.2) j
          after (address (Weighted.child r (fun k => (pivot k : ZMod M)) (fun k => (pivot k).inv) x)) = before (address x)) ∧
        (∀ z, RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ after)) z) =
          readAt blank (F.L (caller 24)) (F.R (caller 24)) (z-0)) ∧ clean F ∧ F.R cut = binSyms L cutoff ∧
        (∀ j : Fin 64, (∀ k, correctionCallerSlots k ≠ j) → F.L (caller j) = S.L (caller j) ∧ F.R (caller j) = S.R (caller j)) ∧
        (∀ j, (∀ k, placement k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ c, Fast.Main.mnProgPush (weightedOrdinaryProgram (U := U) caller work apart r g f) ≤ c →
          (∀ f, Fast.Main.mnProgPush (body f) ≤ c) → StackGrowthExcept (caller 24) S F
            (c*((if cutoff < desc.width then 2*(1+routeTime) else C*(desc.width*(M^d*W))) +
              ordinaryCorrectionTime U w W M.size W.size)) := by
  intro placement ports cut
  obtain ⟨C,dispatch⟩ := ordinaryChildDispatch_exec placement body
  refine ⟨C,?_⟩
  intro node i w aligned r g parent W hW d M is routeTime bank clean v S dest q before f budget cutoff L
    saved desc child eqn layout onTape pivot empty pos inv fresh cutFits widthFits cutWord recurse modulus width one padded clock temps src dst free
  let weight := fun k : Fin (r+g) => if h : k.val < r then pivot ⟨k.val,h⟩ else 1
  let input := fun x : Fin d → ZMod M => (fun k : Fin (r+g) => x (k.castAdd (r+g)),fun k : Fin (r+g) => x (k.natAdd (r+g)))
  let record := S.R (caller 60)
  have start : ColumnRecordReady bank M.size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q before
      (fun x => Fin.append (input x).1 (input x).2) S := by
    refine ⟨before,correctionRecordEntry caller work apart M.size W.size d dest q S before modulus width one padded clock temps src dst,?_⟩
    intro x j
    exact congrArg (fun y => before (FlatCoordinateLayout.index y j)) (Fin.append_castAdd_natAdd (f := x))
  obtain ⟨u,D,t,user,paid,run,plain,scratch,frame,_,routeGrowth⟩ := dispatch node i w aligned hW v S record dest q before input f budget cutoff L
    cutFits widthFits cutWord recurse start free
  have rankBound : r ≤ 42 := nodeChildren5_le i
  have dim : r+g = 64 := by dsimp only [g]; omega
  obtain ⟨z,F,n,same,cost,done,weighted,clear,lastWord,callerFrame,off,correctionGrowth⟩ :=
    dispatchedCorrection_exec caller work apart dim (Nat.le_add_right r g) pivot M.size W.size
      (Nat.lt_size_self _) (Nat.lt_size_self _) hW body v S _ u D t record dest q empty before input
      pos inv fresh user run frame plain scratch
  obtain ⟨after,action,returned⟩ := weightedColumn_return bank M.size W.size record dest q F before
    (fun k => (weight k : ZMod M)) (fun k => (weight k).inv) weighted
  have payload : bank 24 = caller 24 := correctionColumnPlacement_shared caller work apart 1
  refine ⟨z,F,n,after,same,cost.trans (Nat.add_le_add_right paid _),done,?_,payload ▸ returned,clear,lastWord.trans cutWord,callerFrame,off,?_⟩
  · simpa only [weight,Fin.val_castAdd,Fin.isLt,dif_pos] using action
  · intro c hp hb j ne
    obtain ⟨branch,correct⟩ := max_le_iff.mp hp
    obtain ⟨active,stopped⟩ := max_le_iff.mp (max_le_iff.mp branch).2
    obtain ⟨enter,callExit⟩ := max_le_iff.mp active
    have route := routeGrowth c enter (max_le_iff.mp callExit).2 stopped hb
    have final := correctionGrowth c correct hb
    have together := route.trans final j (payload ▸ ne)
    change n ≤ t+ordinaryCorrectionTime U w W M.size W.size at cost
    have bound : n-t ≤ ordinaryCorrectionTime U w W M.size W.size := by omega
    have price := Nat.mul_le_mul_left c bound
    rw [Nat.mul_add]
    exact ⟨together.1.trans (Nat.add_le_add_left (Nat.add_le_add_left price _) _),
      together.2.trans (Nat.add_le_add_left (Nat.add_le_add_left price _) _)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
