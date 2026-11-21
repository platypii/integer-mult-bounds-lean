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

private theorem placedHoare_exec {k q T Q b : ℕ} {P U : Type}
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

open M8.Machine.Segments SharedPlacementAlphabet in
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord) in
open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Pack a live phase record, call the child once, and restore the parent's
digit order. Both basis passes share the payload port with the recursive call. -/
theorem scheduledPhasePacked_host [M8.Machine.Net] {P U : Type} {T Q k : ℕ}
    (p : ℕ × ℕ) (checked : Geometry.Moves.CheckedPair p) (paid : 0 < Geometry.moveRank p.1 p.2)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (body : P → Pr P T Q prime U) (f : P) (capacity : rowSwapBlock.states ≤ Q) :
    let lo := min (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    let hi := max (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    ∃ (C : Matrix (Fin 8) (Fin 8) ℚ) (rev : CopyBasisPass C.adjugate) (fwd : CopyBasisPass C),
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
    let output := fun stages x y => (setTape (caller x) 0 (word y) 0).append (basisWorkspace stages x)
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
    ∀ (slots : Fin k ↪ Fin T) (src : Fin k), slots src = bank 24 →
    (∀ j, j ≠ src → (∀ l, a l ≠ slots j) ∧ (∀ l, ports l ≠ slots j) ∧ (∀ l, b l ≠ slots j)) →
    ∀ (u : HS T Q prime U) (S : Stacks T prime) record dest q (data : Fin k → Fin V → ZMod 2) budget,
    let x := data src
    RepT (phaseOwners data) (embStk slots S).L (embStk slots S).R →
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
      SparseRoleCircuit.encode (fun _ => blank) dest 0 q
    RepT (input A x) (embStk a S).L (embStk a S).R →
    RepT (input B x) (embStk b S).L (embStk b S).R → stored x S → clean S →
    (desc.width < node.width → ∀ (u : HS T Q prime U) D word, stored word D → clean D →
      ∃ z F n changed, Exec body (body f) (mk u D) n (mk z F) ∧ n ≤ budget ∧ z.user = u.user ∧
        stored changed F ∧ clean F ∧ (∀ j, (∀ i, ports i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
        ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (word ∘ position) k) →
    ∃ mid y z G n, Exec body
        ((embProg a (Empty.elim : Empty → P) (foreign (liftQ (machine A) fitsA))).seq
          (middle.seq (embProg b (Empty.elim : Empty → P) (foreign (liftQ (machine B) fitsB)))))
        (mk u S) n (mk z G) ∧ n ≤ budget+(basisRate A+basisRate B+setup+16+swaps*swapVolumeRate w)*V ∧
      z.user = u.user ∧ RepT (phaseOwners (Function.update data src y)) (embStk slots G).L (embStk slots G).R ∧ stored y G ∧ clean G ∧ RepT (output B mid y) (embStk b G).L (embStk b G).R ∧
      (∀ j, (∀ k, a k ≠ j) → (∀ k, ports k ≠ j) → (∀ k, b k ≠ j) → G.L j = S.L j ∧ G.R j = S.R j) ∧
      ∀ s j, y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) p) s)) j) =
        x (index (AffineFieldCoordinates.embed s) j) := by
  intro lo hi
  obtain ⟨setup,swaps,prepare⟩ := phasePackedCall_exec capacity p checked paid ports body f
  obtain ⟨C,shape,rev,fwd⟩ := modular_move_profile.choose_spec.1 p checked
  refine ⟨C,rev,fwd,setup,swaps,?_⟩
  intro node i w B rows rank width split label M K W hW desc
  obtain ⟨position,offset,route⟩ := prepare node i w B rows rank width split label hW
  refine ⟨position,offset,?_⟩
  intro is bank clean pack middle V view size word caller input output
  intro A B' machine basisRate a b fitsA fitsB srcA srcB apart priv slots src shared outside u S record dest q data budget x initial stored readyA readyB start free child
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
  refine ⟨mid,y,z,G,_,Exec.seq runA (Exec.seq exec runB),?_,userB.trans (userM.trans userA),owners,finalRecord,?_,done,untouched,?_⟩
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

open M8.Machine.Segments SharedPlacementAlphabet in
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord) in
open Cover.Fallback IntegerMultBounds.Networks.Certificates.PR589 RecursiveInterchangeLayout in
/-- Execute the selected COPY conversion and its target updates with one scheduled rank-seven child. -/
theorem scheduledCopyFanout_host [M8.Machine.Net] {P U : Type} {T Q : ℕ}
    (stage : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (body : P → Pr P T Q prime U) (f : P) (capacity : rowSwapBlock.states ≤ Q) :
    let p := (life.sourceFrame,0)
    let src := ownerTape stage r d ⟨life.source,(Copy.source_bounds life scheduled).2⟩
    let tmp := Fin.last 142080
    let regs := life.targets.attach.map fun j =>
      (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
    let targets := regs.map (ownerTape stage r d)
    ∃ (q s : ℕ) (load : Program (142081+2) q prime) (finish : Program (142081+2) s prime),
    let lo := min (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    let hi := max (Geometry.Dimensions.value p.1) (Geometry.Dimensions.value p.2)
    ∃ (C : Matrix (Fin 8) (Fin 8) ℚ) (rev : CopyBasisPass C.adjugate) (fwd : CopyBasisPass C),
    ∃ setup swaps : ℕ, ∀ (node : Descriptor) (i : Fin nodeChildren5.length) (w B rows : ℕ),
    nodeChildren5[i.val] = 7 → node.width = 64*(w+1) →
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
    ∃ size : volume prime view = V,
    let word := fun y : Fin V → ZMod 2 => sourceWord (v := view) (fun k => y (k.cast size))
    let caller := fun y => (⟨fun _ => 0,fun _ => word y⟩ : Tapes 1 prime)
    let input := fun stages y => (caller y).append (basisWorkspace stages y)
    let A := description _ rev.good
    let forward := description _ fwd.good
    let machine := fun stages => Placement.placed (FlatCoordinateCleanSchedule.program stages)
      (sharedPlacement (0 : Fin 1) (segmentSource stages))
    let basisRate := fun stages => FlatCoordinateCleanSchedule.constant stages*(1+FlatCoordinateCleanSchedule.tapeCount stages+5)
    ∀ (a : Fin (1+FlatCoordinateCleanSchedule.tapeCount A) ↪ Fin T)
      (b : Fin (1+FlatCoordinateCleanSchedule.tapeCount forward) ↪ Fin T) (fitsA : _ ≤ Q) (fitsB : _ ≤ Q),
    a ((0 : Fin 1).castAdd _) = bank 24 → b ((0 : Fin 1).castAdd _) = bank 24 →
    (∀ j, ports j ≠ bank 24 → ∀ k, a k ≠ ports j) →
    (∀ j : Fin (FlatCoordinateCleanSchedule.tapeCount forward), (∀ k, a k ≠ b (j.natAdd 1)) ∧ (∀ k, ports k ≠ b (j.natAdd 1))) →
    ∀ (fan : Fin (142081+2) ↪ Fin T) (loadFits : q ≤ Q) (finishFits : s ≤ Q),
    let slots := (Fin.castAddEmb 2).trans fan
    slots tmp = bank 24 →
    (∀ j, j ≠ tmp → (∀ l, a l ≠ slots j) ∧ (∀ l, ports l ≠ slots j) ∧ (∀ l, b l ≠ slots j)) →
    (∀ i : Fin 2, (∀ l, a l ≠ fan (i.natAdd 142081)) ∧ (∀ l, ports l ≠ fan (i.natAdd 142081)) ∧
      (∀ l, b l ≠ fan (i.natAdd 142081))) →
    ∀ (u : HS T Q prime U) (S : Stacks T prime) record dest q' (data : Fin 142081 → Fin V → ZMod 2) budget,
    let x := data src
    let fanReady := fun X (D : Stacks T prime) => RepT (PointwiseRoleGate.bank (a := prime)
      (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) (FlatCoordinateSchedule.bits V))
      (embStk fan D).L (embStk fan D).R
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
      SparseRoleCircuit.encode (fun _ => blank) dest 0 q'
    fanReady data S →
    RepT (input A (data tmp)) (embStk a S).L (embStk a S).R →
    RepT (input forward (data tmp)) (embStk b S).L (embStk b S).R → stored (data tmp) S → clean S →
    (desc.width < node.width → ∀ (u : HS T Q prime U) D word, stored word D → clean D →
      ∃ z F n changed, Exec body (body f) (mk u D) n (mk z F) ∧ n ≤ budget ∧ z.user = u.user ∧
        stored changed F ∧ clean F ∧ (∀ j, (∀ i, ports i ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
        ∀ k, changed (position k) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (word ∘ position) k) →
    let convert := (embProg a (Empty.elim : Empty → P) (foreign (liftQ (machine A) fitsA))).seq
        (middle.seq (embProg b (Empty.elim : Empty → P) (foreign (liftQ (machine forward) fitsB))))
    let addr := copyAddress (Q := M) (W := W)
    let move := AffineFieldProgram.run (selectedWord (w+1) p)
    let common := fun i => x (addr.symm (move (addr i).1,(addr i).2))
    let result := Function.update (fun j i => if j ∈ targets then data j i + common i else data j i) tmp 0
    ∃ z F t, Exec body ((embProg fan (Empty.elim : Empty → P) (foreign (liftQ load loadFits))).seq
        (convert.seq (embProg fan (Empty.elim : Empty → P) (foreign (liftQ finish finishFits)))))
      (mk u S) t (mk z F) ∧
      t ≤ budget+(basisRate A+basisRate forward+setup+16+swaps*swapVolumeRate w)*V+76*(life.targets.length+2)*V*142088+12 ∧
      z.user = u.user ∧ fanReady result F ∧ CopyFanoutEffect stage r d life scheduled (w+1) B K data result ∧
      ∀ j, (∀ l, a l ≠ j) → (∀ l, ports l ≠ j) →
        (∀ l, b l ≠ j) → (∀ l, fan l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro p src tmp regs targets
  have mem := copySource_mem life scheduled
  have checked := retainedCopy_checked.1 _ mem
  have rank : Geometry.moveRank p.1 p.2 = 7 := by
    rw [Geometry.Moves.rank p checked]
    have h := List.mem_map_of_mem (f := Geometry.Moves.value) mem
    rw [retainedCopy_checked.2] at h
    exact (List.mem_replicate.mp h).2
  have paid : 0 < Geometry.moveRank p.1 p.2 := by omega
  obtain ⟨q,s,load,finish,fanout⟩ := copyFanout_host stage r d life scheduled
  obtain ⟨C,rev,fwd,setup,swaps,run⟩ := scheduledPhasePacked_host (k := 142081) p checked paid ports body f capacity
  refine ⟨q,s,load,finish,C,rev,fwd,setup,swaps,?_⟩
  intro node i w B rows seven width split label M K W hW desc
  obtain ⟨position,offset,step⟩ := run node i w B rows (seven.trans rank.symm) width split label hW
  refine ⟨position,offset,?_⟩
  intro is bank clean pack middle V view
  refine ⟨phaseIntervalChild_volume (phaseInterval_bounds checked paid).1.le (phaseInterval_bounds checked paid).2 (w+1) W,?_⟩
  intro word caller input A B' machine basisRate a b fitsA fitsB
    srcA srcB apart priv fan loadFits finishFits slots shared ownersOff controlsOff u S record dest q' data budget
    x fanReady stored ready initialA initialB initialRecord initialClean recurse convert addr move common result
  let keep := fun j => (∀ l, a l ≠ j) ∧ (∀ l, ports l ≠ j) ∧ (∀ l, b l ≠ j)
  obtain ⟨z,F,t,exec,time,user,done,off⟩ := fanout fan loadFits finishFits body convert
    (budget+(basisRate A+basisRate B'+setup+16+swaps*swapVolumeRate w)*V) keep data hW u S ready (by
      intro v D loaded outside
      let X := Function.update data tmp x
      have slot (k : Fin 142081) : slots k = fan (k.castAdd 2) := by apply congrArg fan; apply Fin.ext; rfl
      have enc (Y : Fin 142081 → Fin V → ZMod 2) (k : Fin 142081) : SparseRoleCircuit.encoded (a := prime) Y k =
          fun i => SparseRoleCircuit.encode (Y k i) := rfl
      have initial : RepT (phaseOwners X) (embStk slots D).L (embStk slots D).R := by
        intro k j
        simpa only [phaseOwners,enc,X,x,src,tmp,embStk,Function.comp_apply,slot,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left] using loaded (k.castAdd 2) j
      have kept (j) (separate : j ≠ bank 24) (used : ¬ keep j) : D.L j = S.L j ∧ D.R j = S.R j := by
        apply outside
        intro l
        induction l using Fin.addCases with
        | left k =>
          change slots k ≠ j
          by_cases ht : k = tmp
          · simpa only [ht,shared] using separate.symm
          · exact fun eq => used (eq ▸ ownersOff k ht)
        | right k => exact fun eq => used (eq ▸ controlsOff k)
      have portKeep (k) (ne : ports k ≠ bank 24) := kept _ ne (fun h => h.2.1 k rfl)
      have cell (j : ℤ) : putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (x i)) j =
          readAt blank (D.L (bank 24)) (D.R (bank 24)) j := by
        simpa only [phaseOwners,X,Function.update_self,embStk,Function.comp_apply,shared,sub_zero] using initial tmp j
      have encoded (j : ℤ) := encodedOwnerCell x j
      simp only [List.map_ofFn] at encoded
      have start : stored x D := initialRecord.returnPayload
        (fun k ne => portKeep _ (bank.injective.ne ne)) (fun j => by
          simpa only [sub_zero] using (encoded j).trans (cell j))
      have free : clean D := by
        intro k hk
        have ne : ports k ≠ bank 24 := ports.injective.ne (fun eq => by
          have v := congrArg Fin.val eq; change k.val = 24 at v; omega)
        obtain ⟨l,r⟩ := portKeep k ne
        exact ⟨l.trans (initialClean k hk).1,r.trans (initialClean k hk).2⟩
      have basis (stages : List (FlatCoordinateSchedule.Op 16))
          (e : Fin (1+FlatCoordinateCleanSchedule.tapeCount stages) ↪ Fin T)
          (site : e ((0 : Fin 1).castAdd _) = bank 24) (uses : ∀ k, ¬ keep (e k))
          (prior : RepT (input stages (data tmp)) (embStk e S).L (embStk e S).R) :
          RepT (input stages x) (embStk e D).L (embStk e D).R := by
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
          obtain ⟨l,r⟩ := kept _ ne (uses _)
          simpa only [input,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,l,r,
            basisWorkspace_eq stages x (data tmp)] using prior (k.natAdd 1) j
      have first := basis A a srcA (fun k h => h.1 k rfl) initialA
      have last := basis B' b srcB (fun k h => h.2.2 k rfl) initialB
      obtain ⟨mid,y,z,G,m,exec,time,user,owners,_,_,_,off,action⟩ :=
        step a b fitsA fitsB srcA srcB apart priv slots tmp shared ownersOff v D record dest q' X budget initial
          (by simpa only [X,Function.update_self] using first) (by simpa only [X,Function.update_self] using last)
          (by simpa only [X,Function.update_self] using start) free recurse
      refine ⟨z,G,m,y,exec,time,user,?_,?_,fun j h _ => off j h.1 h.2.1 h.2.2⟩
      · intro k j
        induction k using Fin.addCases with
        | left k =>
          simpa only [phaseOwners,enc,tmp,embStk,Function.comp_apply,slot,X,Function.update_idem,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left]
            using owners k j
        | right k =>
          obtain ⟨ha,hp,hb⟩ := controlsOff k
          obtain ⟨l,r⟩ := off _ ha hp hb
          simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,l,r]
            using loaded (k.natAdd 142081) j
      · simpa only [copyAddress_index,X,Function.update_self] using action)
  exact ⟨z,F,t,exec,time,user,done,copyFanout_effect stage r d life scheduled (w+1) B K data,
    fun j ha hp hb hj => off j ⟨ha,hp,hb⟩ hj⟩

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Sequence physical phase instructions on the common owner bank. Each gate
and positive-rank edge pays its own execution bound once. Rank-zero moves
consume the corresponding trace entry and leave the machine untouched. -/
theorem phaseInstructions_host {T Q w W : ℕ} {P U I : Type}
    (body : P → Pr P T Q prime U)
    (ready : I → (Fin W → ℕ → AddressStream (ZMod (prime^(w+1)))) → Stacks T prime → Prop)
    (gs : List (FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^(w+1))))))
    (ps : List (ℕ × ℕ)) (checked : ∀ p ∈ ps, Geometry.Moves.CheckedPair p)
    (gateTime : Circuit.Gate ℕ (ZMod 2) → ℕ) (edgeTime : ℕ × ℕ → ℕ)
    (gate : ∀ g, .gate g ∈ gs → ∃ code, ∀ ctx x u S, ready ctx x S →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ n ≤ gateTime g ∧ z.user = u.user ∧
        ready ctx (fun j => FramedCircuit.moduleGate g (x j)) F)
    (edge : ∀ r old next, .edge r old next ∈ gs → ∀ p ∈ ps, Geometry.moveRank p.1 p.2 ≠ 0 →
      ∃ code, ∀ ctx x u S, ready ctx x S → ∃ z F n, Exec body code (mk u S) n (mk z F) ∧
        n ≤ edgeTime p ∧ z.user = u.user ∧ ready ctx (fun j => Function.update (x j) r
          (fun s => x j r (AffineFieldProgram.run (selectedWord (w+1) p) s))) F) :
    let localCost := fun op : FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^(w+1)))) =>
      match op with | .gate g => gateTime g | .edge .. => 0
    let paid := fun p : ℕ × ℕ => if Geometry.moveRank p.1 p.2 = 0 then 0 else edgeTime p
    ∃ code, ∀ ctx x u S, ready ctx x S → ∃ z F n, Exec body code (mk u S) n (mk z F) ∧
      n ≤ (gs.map localCost).sum+(ps.map paid).sum+1 ∧ z.user = u.user ∧
      ready ctx (fun j => runPhase (selectedWord (w+1)) gs ps (x j)) F := by
  intro localCost paid
  induction gs generalizing ps with
  | nil =>
    exact ⟨.act .done,fun _ _ u S ok => ⟨u,S,1,Exec.act _ _,by simp,rfl,ok⟩⟩
  | cons op rest ih =>
    have gates := fun g (h : FramedCircuit.Instruction.gate g ∈ rest) => gate g (List.mem_cons_of_mem _ h)
    have edges := fun r old next (h : FramedCircuit.Instruction.edge r old next ∈ rest) =>
      edge r old next (List.mem_cons_of_mem _ h)
    cases op with
    | gate g =>
      obtain ⟨head,step⟩ := gate g List.mem_cons_self
      obtain ⟨tail,finish⟩ := ih ps checked gates edges
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
        obtain ⟨tail,finish⟩ := ih ps (fun q h => checked q (List.mem_cons_of_mem _ h)) gates
          (fun i a b h q hq => edges i a b h q (List.mem_cons_of_mem _ hq))
        by_cases zero : Geometry.moveRank p.1 p.2 = 0
        · refine ⟨tail,?_⟩
          intro ctx x u S ok
          obtain ⟨z,F,n,run,time,user,out⟩ := finish ctx x u S ok
          refine ⟨z,F,n,run,?_,user,?_⟩
          · simpa only [List.map_cons,List.sum_cons,localCost,paid,ite_eq_left zero,Nat.zero_add] using time
          · have unchanged (j : Fin W) : Function.update (x j) r
                (fun s => x j r (AffineFieldProgram.run (selectedWord (w+1) p) s)) = x j := by
              simp only [(modular_scatter (w+1)).choose_spec.2.2.1.zero p (checked p List.mem_cons_self) zero,
                Function.update_eq_self]
            simpa only [runPhase,unchanged] using out
        · obtain ⟨head,step⟩ := edge r old next List.mem_cons_self p List.mem_cons_self zero
          refine ⟨head.seq tail,?_⟩
          intro ctx x u S ok
          obtain ⟨v,D,t,run,time,user,mid⟩ := step ctx x u S ok
          obtain ⟨z,F,n,exec,bound,same,out⟩ := finish ctx _ v D mid
          refine ⟨z,F,_,Exec.seq run exec,?_,same.trans user,out⟩
          simp only [List.map_cons,List.sum_cons,localCost,ite_eq_right zero,paid,Nat.zero_add] at *
          omega

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Assemble either literal PR589 phase from physical scalar and MOVE
executions. The returned owner bank implements the compiled frame snapshot. -/
theorem invocationPhase_host {T Q k w W : ℕ} {P U : Type} (owner : Fin 661 ↪ Fin k)
    (body : P → Pr P T Q prime U) (afterScatter : Bool)
    (ready : (Fin k → Fin ((prime^(w+1))^16*W) → ZMod 2) → Stacks T prime → Prop)
    (moveTime : ℕ × ℕ → ℕ) :
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
    (∀ (r : Fin 661) p, p ∈ edges → Geometry.Moves.CheckedPair p → Geometry.moveRank p.1 p.2 ≠ 0 →
      ∃ code, ∀ data u S, ready data S → ∃ z F n y, Exec body code (mk u S) n (mk z F) ∧
        n ≤ moveTime p ∧ z.user = u.user ∧ ready (Function.update data (owner r) y) F ∧
        ∀ s j, y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) p) s)) j) =
          data (owner r) (index (AffineFieldCoordinates.embed s) j)) →
    ∃ code, ∀ data u S, ready data S → ∃ z F n out, Exec body code (mk u S) n (mk z F) ∧
      n ≤ (gates.map (fun g => gateTime g.toCircuit)).sum +
        ((edges.filter (fun p => Geometry.moveRank p.1 p.2 != 0)).map moveTime).sum+1 ∧
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
  have movesCost (ps : List (ℕ × ℕ)) :
      (ps.map (fun p => if Geometry.moveRank p.1 p.2 = 0 then 0 else moveTime p)).sum =
        ((ps.filter (fun p => Geometry.moveRank p.1 p.2 != 0)).map moveTime).sum := by
    induction ps with
    | nil => rfl
    | cons p ps ih => by_cases h : Geometry.moveRank p.1 p.2 = 0 <;> simp [h,ih]
  obtain ⟨code,run⟩ := phaseInstructions_host body represented instructions edges checked gateTime moveTime (by
    intro g member
    obtain ⟨raw,scheduled,rfl⟩ := valid (.gate g) member
    obtain ⟨code,step⟩ := gate raw scheduled
    refine ⟨code,?_⟩
    intro original x u S ⟨data,ok,fixed,hx⟩
    obtain ⟨z,F,n,out,exec,time,user,done,off,act⟩ := step data u S ok
    exact ⟨z,F,n,exec,time,user,out,done,fun i h => (off i h).trans (fixed i h),fun j => (phaseRead_gate owner raw scheduled data out act j).trans
      (congrArg _ (hx j))⟩) (by
    intro i a b member p hp paid
    let r : Fin 661 := ⟨i,valid (.edge i a b) member⟩
    obtain ⟨code,step⟩ := move r p hp (checked p hp) paid
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
  rwa [gatesCost gates (fun i => frame (current i)),movesCost edges] at time

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- One class invocation executes the two literal phases around the nine COPY
lifecycles and returns the selected register action at every cover label. -/
theorem invocation_host {T Q w B K : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (n : Fin 9) (r : Fin 32) (d : Fin 5) :
    let W := B*prime^(64*((w+1)*64))*K
    let V := (prime^(w+1))^16*W
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let view := fun (x : Fin 142081 → Fin V → ZMod 2) k t => x k (Fin.cast (copyLabel_volume (w+1) B K) t)
    let gateTime := fun g : Circuit.Gate ℕ (ZMod 2) => 76*g.terms.length*V*(142081+7)+6
    ∀ (ready : (Fin 142081 → Fin V → ZMod 2) → Stacks T prime → Prop)
      (moveTime : ℕ × ℕ → ℕ) (copyTime : Copy.Lifecycle → ℕ),
    (∀ g ∈ program, ∃ code, ∀ data u S, ready data S →
      ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧ t ≤ gateTime g.toCircuit ∧ z.user = u.user ∧
        ready out F ∧ (∀ i, (∀ j, owner j ≠ i) → out i = data i) ∧ ∀ j : Fin 661, ∀ k,
          out (owner j) k = g.toCircuit.run (Copy.extendStored (fun j => data (owner j) k)) j.val) →
    (∀ (j : Fin 661) p, p ∈ Geometry.Moves.phaseEdges → Geometry.Moves.CheckedPair p →
      Geometry.moveRank p.1 p.2 ≠ 0 → ∃ code, ∀ data u S, ready data S → ∃ z F t y,
        Exec body code (mk u S) t (mk z F) ∧ t ≤ moveTime p ∧ z.user = u.user ∧
        ready (Function.update data (owner j) y) F ∧ ∀ s l,
          y (index (AffineFieldCoordinates.embed (AffineFieldProgram.run (selectedWord (w+1) p) s)) l) =
            data (owner j) (index (AffineFieldCoordinates.embed s) l)) →
    (∀ life ∈ Copy.lifecycles, ∃ code, ∀ data u S, ready data S → ∃ z F t out,
      Exec body code (mk u S) t (mk z F) ∧ t ≤ copyTime life ∧ z.user = u.user ∧ ready out F ∧
      CopyWindowEffect n r d life (w+1) B K (view data) (view out)) →
    ∃ code, ∀ data u S, ready data S → ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
      t ≤ ((sectionD++sectionA++(sectionB++sectionC)).map (fun g => gateTime g.toCircuit)).sum +
        ((Geometry.Moves.phaseEdges.filter (fun p => Geometry.moveRank p.1 p.2 != 0)).map moveTime).sum +
        (Copy.lifecycles.map copyTime).sum+3 ∧ z.user = u.user ∧ ready out F ∧
        InvocationEffect n r d (w+1) B K data out := by
  intro W V owner view gateTime ready moveTime copyTime gates moves copies
  obtain ⟨left,enter⟩ := invocationPhase_host owner body false ready moveTime gates
    (fun j p hp => moves j p (List.mem_append_left _ hp))
  obtain ⟨right,leave⟩ := invocationPhase_host owner body true ready moveTime gates
    (fun j p hp => moves j p (List.mem_append_right _ hp))
  have scatter (ls : List Copy.Lifecycle) (inside : ∀ l ∈ ls, l ∈ Copy.lifecycles) :
      ∃ code, ∀ data u S, ready data S → ∃ z F t out, Exec body code (mk u S) t (mk z F) ∧
        t ≤ (ls.map copyTime).sum+1 ∧ z.user = u.user ∧ ready out F ∧
          CopyScheduleEffect n r d (w+1) B K ls (view data) (view out) := by
    induction ls with
    | nil => exact ⟨.act .done,fun x u S ok => ⟨u,S,1,x,Exec.act _ _,by simp,rfl,ok,rfl⟩⟩
    | cons l ls ih =>
      obtain ⟨head,step⟩ := copies l (inside _ List.mem_cons_self)
      obtain ⟨tail,finish⟩ := ih (fun x hx => inside _ (List.mem_cons_of_mem _ hx))
      refine ⟨head.seq tail,?_⟩
      intro x u S ok
      obtain ⟨v,D,t,y,a,ha,same,mid,act⟩ := step x u S ok
      obtain ⟨z,F,m,out,b,hb,user,done,rest⟩ := finish y v D mid
      refine ⟨z,F,_,out,Exec.seq a b,?_,user.trans same,done,view y,act,rest⟩
      simp only [List.map_cons,List.sum_cons]
      omega
  obtain ⟨middle,window⟩ := scatter Copy.lifecycles (fun _ h => h)
  refine ⟨left.seq (middle.seq right),?_⟩
  intro x u S ok
  obtain ⟨v,D,a,y,first,ha,ua,mid,offA,readA⟩ := enter x u S ok
  obtain ⟨h,G,b,z,copy,hb,ub,placed,effect⟩ := window y v D mid
  obtain ⟨q,F,c,out,last,hc,uc,done,offB,readB⟩ := leave z h G placed
  refine ⟨q,F,_,out,Exec.seq first (Exec.seq copy last),?_,uc.trans (ub.trans ua),done,?_,?_⟩
  · change a ≤ ((sectionD++sectionA).map (fun g => gateTime g.toCircuit)).sum+_+1 at ha
    change c ≤ ((sectionB++sectionC).map (fun g => gateTime g.toCircuit)).sum+_+1 at hc
    simp only [Geometry.Moves.phaseEdges,List.filter_append,List.map_append,List.sum_append,
      Bool.false_eq_true,ite_false,ite_true] at ha hc ⊢
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
