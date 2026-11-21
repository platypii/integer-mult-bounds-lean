module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Views
public import IntegerMultBounds.MathlibTM2.M6.BitCopyRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPackSchedule

/-! Coordinate correspondence between the COPY temporary and its rank-seven recursive child. -/
@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Machine IntegerMultBounds.Networks
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveInterchangeScaling (Address index)
open Shared50ModularControl (prime)
open Shared50RecursiveNodeTranspose (swapAddress)
open Cover.Fallback (rankDescriptor)

namespace CopyChildLayout

noncomputable def flatAddress (v : Descriptor) : Address v ≃ Fin (volume prime v) where
  toFun := index
  invFun i :=
    let (i, e) := finProdFinEquiv.symm i
    let (i, d) := finProdFinEquiv.symm i
    let (i, m) := finProdFinEquiv.symm i
    let (i, h) := finProdFinEquiv.symm i
    let (i, b) := finProdFinEquiv.symm i
    let (a, row) := finProdFinEquiv.symm i
    ⟨a,row,b,h,m,d,e⟩
  left_inv a := by cases a; simp [index, RecursiveInterchangeScaling.pack]
  right_inv i := by
    simp only [index, RecursiveInterchangeScaling.pack, Prod.eta, Equiv.apply_symm_apply]
    exact finProdFinEquiv.apply_symm_apply i

def spectators (v : Descriptor) := v.beforeRows*v.rows*v.beforeH*v.between*v.afterD

noncomputable def fields (v : Descriptor) : Address v ≃
    (Fin (prime^v.width) × Fin (prime^v.width)) × Fin (spectators v) where
  toFun a := ((a.h,a.d), finProdFinEquiv (finProdFinEquiv (finProdFinEquiv
    (finProdFinEquiv (a.beforeRows,a.row),a.before),a.middle),a.after))
  invFun p :=
    let (i,e) := finProdFinEquiv.symm p.2
    let (i,m) := finProdFinEquiv.symm i
    let (i,b) := finProdFinEquiv.symm i
    let (a,row) := finProdFinEquiv.symm i
    ⟨a,row,b,p.1.1,m,p.1.2,e⟩
  left_inv a := by cases a; simp
  right_inv p := by
    simp only [Prod.eta, Equiv.apply_symm_apply]
    exact congrArg (p.1, ·) (finProdFinEquiv.apply_symm_apply p.2)

noncomputable def changeLayout (v u : Descriptor) (width : v.width = u.width)
    (size : spectators v = spectators u) : Address v ≃ Address u :=
  (fields v).trans ((Equiv.prodCongr
    (Equiv.prodCongr (finCongr (congrArg (prime^·) width)) (finCongr (congrArg (prime^·) width)))
    (finCongr size)).trans (fields u).symm)

private theorem changeLayout_swap (v u : Descriptor) (width size) (a : Address v) :
    changeLayout v u width size (swapAddress a) = swapAddress (changeLayout v u width size a) := by
  rfl

/-- The orthogonal bank exposes eight of the parent's 64 coordinates in each
active field. The other 112 coordinates and the role spectators ride in W.
At every local rank this gives the spectator count of the scheduled child. -/
theorem orthogonalSpectators (v : Descriptor) (w rows r : ℕ) (hr : r ≤ 8)
    (splitRows : v.rows = 142080*rows) :
    let W := (prime^w)^112 * (v.beforeRows*rows*v.beforeH*v.between*v.afterD)
    spectators (M8.RevMachine.sub prime w 8 0 r ⟨1,1,1,8*w,1,W⟩) =
      spectators (rankDescriptor prime (r*w) ((64-r)*w) (role v 142080)) := by
  intro W
  have gap : 64-r = (8-r)+56 := by omega
  simp only [spectators,M8.RevMachine.sub,rankDescriptor,role,W,splitRows,
    Nat.mul_div_cancel_left _ (by decide : 0 < 142080),Nat.sub_zero,zero_mul,pow_zero,
    mul_one,one_mul,gap,Nat.add_mul,pow_add]
  rw [show 56*w = w*56 by omega,pow_mul]
  ring

/-- Reindexing the spectators transports a reversed interchange with the same
atom width and count. Both active fields keep their original digits. -/
theorem revT_changeLayout (v u : Descriptor) (n w : ℕ)
    (hv : v.width = n*w) (hu : u.width = n*w) (size : spectators v = spectators u)
    (x y : ℕ → ZMod 2) (read : M8.RevMachine.RevT prime w n u x y) :
    let f := changeLayout v u (hv.trans hu.symm) size
    let pull := fun (z : ℕ → ZMod 2) i => if hi : i < volume prime v then
      z (index (f ((flatAddress v).symm ⟨i,hi⟩))).val else 0
    M8.RevMachine.RevT prime w n v (pull x) (pull y) := by
  intro f pull a ha row hrow b hb h hh m hm d hd j hj
  let rev := M8.RevMachine.revAtoms (prime^w) n
  have bound (z : ℕ) : rev z < prime^v.width := by
    rw [hv,Nat.mul_comm,pow_mul]
    exact M8.RevMachine.revAtoms_lt (pow_pos Shared50ModularControl.prime_prime.pos _) _ _
  let src : Address v := ⟨⟨a,ha⟩,⟨row,hrow⟩,⟨b,hb⟩,⟨h,hv ▸ hh⟩,⟨m,hm⟩,⟨d,hv ▸ hd⟩,⟨j,hj⟩⟩
  let dst : Address v := {src with h := ⟨rev d,bound d⟩, d := ⟨rev h,bound h⟩}
  have atIndex (z : ℕ → ZMod 2) (p : Address v) :
      pull z (index p).val = z (index (f p)).val := by
    simp only [pull,(index p).isLt,↓reduceDIte]
    change z (index (f ((flatAddress v).symm (flatAddress v p)))).val = _
    rw [Equiv.symm_apply_apply]
  change pull y _ = pull x _
  rw [← show (index src).val = _ from RecursiveInterchangeScaling.index_val src,
      ← show (index dst).val = _ from RecursiveInterchangeScaling.index_val dst,
      atIndex,atIndex,RecursiveInterchangeScaling.index_val,RecursiveInterchangeScaling.index_val]
  let t := f src
  exact read _ t.beforeRows.isLt _ t.row.isLt _ t.before.isLt h hh _ t.middle.isLt d hd _ t.after.isLt

theorem copySpectators (v : Descriptor) (w rows : ℕ) (splitRows : v.rows = 142080*rows) :
    let W := (prime^w)^112 * (v.beforeRows*rows*v.beforeH*v.between*v.afterD)
    spectators (copyChild w W) = spectators (rankDescriptor prime (7*w) (57*w) (role v 142080)) := by
  intro W
  simp only [spectators, copyChild, rankDescriptor, role, W, splitRows,
      Nat.mul_div_cancel_left _ (by decide : 0 < 142080), one_mul,
      show 57*w = w*57 by omega, pow_mul]
  ring

/-- Put H and D first, retaining the original order of all spectator fields.
The two rectangular interchanges have shapes (middle,D) and (prefix,H×D). -/
noncomputable def packActive (v : Descriptor) : Fin (volume prime v) ≃
    Fin ((prime^v.width * prime^v.width) * spectators v) :=
  let p := v.beforeRows*v.rows*v.beforeH
  let h := prime^v.width
  let m := v.between
  let s := v.afterD
  (finCongr (by dsimp [volume,p,h,m,s]; ring)).trans
    ((Cover.Fallback.packMiddleTail (p*h) m h s).trans
      ((finCongr (show (p*h)*(h*(m*s)) = 1*(p*((h*h)*(m*s))) by ring)).trans
        ((Cover.Fallback.packMiddleTail 1 p (h*h) (m*s)).trans
          (finCongr (by dsimp [spectators,p,h,m,s]; ring)))))

theorem packActive_index (v : Descriptor) (a : Address v) :
    packActive v (index a) = finProdFinEquiv (finProdFinEquiv ((fields v a).1), (fields v a).2) := by
  let outer := finProdFinEquiv (finProdFinEquiv (a.beforeRows,a.row),a.before)
  let h : Fin (prime^v.width) := a.h
  let d : Fin (prime^v.width) := a.d
  let hd := finProdFinEquiv (h,d)
  let tail := finProdFinEquiv (a.middle,a.after)
  have start : (finCongr (by dsimp [volume,ActualAffineScaling.modulus]; ring) (index a)) =
      finProdFinEquiv (finProdFinEquiv (outer,h),finProdFinEquiv (a.middle,finProdFinEquiv (d,a.after))) := by
    apply Fin.ext
    change (index a).val = _
    rw [RecursiveInterchangeScaling.index_val]
    simp only [RecursiveInterchangeLayout.index, outer, h, d, finProdFinEquiv, Equiv.coe_fn_mk,ActualAffineScaling.modulus]
    ring
  have regroup : finCongr (by ring) (finProdFinEquiv (finProdFinEquiv (outer,h),finProdFinEquiv (d,tail))) =
      finProdFinEquiv ((0 : Fin 1),finProdFinEquiv (outer,finProdFinEquiv (hd,tail))) := by
    apply Fin.ext
    change (finProdFinEquiv (finProdFinEquiv (outer,h),finProdFinEquiv (d,tail))).val = _
    simp only [hd,finProdFinEquiv,Equiv.coe_fn_mk,Fin.val_zero]
    ring
  unfold packActive
  simp only [Equiv.trans_apply]
  rw [start, Cover.Fallback.packMiddleTail_index, regroup, Cover.Fallback.packMiddleTail_index]
  apply Fin.ext
  change (finProdFinEquiv ((0 : Fin 1),finProdFinEquiv (hd, finProdFinEquiv (outer,tail)))).val =
    (finProdFinEquiv (hd,finProdFinEquiv (finProdFinEquiv (outer,a.middle),a.after))).val
  simp only [finProdFinEquiv,Equiv.coe_fn_mk,Fin.val_zero,tail]
  ring

theorem packActive_change (v u : Descriptor) (width size) (a : Address v) :
    (packActive u (index (changeLayout v u width size a))).val = (packActive v (index a)).val := by
  rw [packActive_index, packActive_index]
  have coord := (fields u).apply_symm_apply
    ((Equiv.prodCongr
      (Equiv.prodCongr (finCongr (congrArg (prime^·) width)) (finCongr (congrArg (prime^·) width)))
      (finCongr size)) (fields v a))
  change fields u (changeLayout v u width size a) = _ at coord
  rw [coord]
  simp only [Equiv.prodCongr_apply,Prod.map,finCongr_apply,Fin.val_cast,finProdFinEquiv,Equiv.coe_fn_mk,width,size]

end CopyChildLayout

open CopyChildLayout

/-- Repack the two active fields and the five spectator fields in recursive descriptor order. -/
noncomputable def copyChildLayoutEquiv (v : Descriptor) (w rows : ℕ) (splitRows : v.rows = 142080*rows) :
    let W := (prime^w)^112 * (v.beforeRows*rows*v.beforeH*v.between*v.afterD)
    Fin (volume prime (copyChild w W)) ≃
      Fin (volume prime (rankDescriptor prime (7*w) (57*w) (role v 142080))) := by
  intro W
  let packed := copyChild w W
  let child := rankDescriptor prime (7*w) (57*w) (role v 142080)
  exact (flatAddress packed).symm.trans
    ((changeLayout packed child rfl (copySpectators v w rows splitRows)).trans (flatAddress child))

/-- The route consists of packing the temporary, then undoing the recursive
child's packing. The intermediate cast changes only the index's type. -/
theorem copyChildLayout_route (v : Descriptor) (w rows : ℕ) (splitRows : v.rows = 142080*rows) :
    let W := (prime^w)^112 * (v.beforeRows*rows*v.beforeH*v.between*v.afterD)
    let packed := copyChild w W
    let child := rankDescriptor prime (7*w) (57*w) (role v 142080)
    ∀ i, (packActive child (copyChildLayoutEquiv v w rows splitRows i)).val = (packActive packed i).val := by
  intro W packed child i
  obtain ⟨a,rfl⟩ := (flatAddress packed).surjective i
  let f := changeLayout packed child rfl (copySpectators v w rows splitRows)
  have entry : copyChildLayoutEquiv v w rows splitRows (flatAddress packed a) = flatAddress child (f a) :=
    congrArg (fun z => flatAddress child (f z)) ((flatAddress packed).symm_apply_apply a)
  rw [entry]
  exact packActive_change packed child rfl (copySpectators v w rows splitRows) a

/-- Repartitioning spectator coordinates preserves the transpose when both
active fields retain their width. -/
theorem transpose_changeLayout (packed child : Descriptor) (width : packed.width = child.width)
    (size : spectators packed = spectators child) :
    let f := changeLayout packed child width size
    let e := (flatAddress packed).symm.trans (f.trans (flatAddress child))
    ∀ {α : Type} (x : Fin (volume prime child) → α) i,
      Shared50RecursiveNodeRows.transpose (one_dvd packed.rows) (x ∘ e) i =
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x (e i) := by
  intro f e
  intro α x i
  obtain ⟨a,rfl⟩ := (flatAddress packed).surjective i
  have left := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)
    (one_dvd packed.rows) (x ∘ e) (swapAddress a)
  have right := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)
    (one_dvd child.rows) x (swapAddress (f a))
  change _ = x (e (flatAddress packed (swapAddress a))) at left
  change _ = x (flatAddress child (swapAddress (f a))) at right
  have entry (b : Address packed) : e (flatAddress packed b) = flatAddress child (f b) := by
    exact congrArg (fun z => flatAddress child (f z)) ((flatAddress packed).symm_apply_apply b)
  rw [entry]
  calc
    _ = x (e (flatAddress packed (swapAddress a))) := left
    _ = x (flatAddress child (swapAddress (f a))) := by
      rw [entry, show f (swapAddress a) = swapAddress (f a) from changeLayout_swap ..]
    _ = _ := right.symm

/-- Flattening the spectators of a rank-seven child gives the exact permutation
of the COPY temporary that intertwines the two physical payload transposes. -/
theorem copyChild_reindex (v : Descriptor) (w rows : ℕ) (splitRows : v.rows = 142080*rows) :
    let W := (prime^w)^112 * (v.beforeRows*rows*v.beforeH*v.between*v.afterD)
    let packed := copyChild w W
    let child := rankDescriptor prime (7*w) (57*w) (role v 142080)
    let e := copyChildLayoutEquiv v w rows splitRows
      ∀ {α : Type} (x : Fin (volume prime child) → α) i,
        Shared50RecursiveNodeRows.transpose (one_dvd packed.rows) (x ∘ e) i =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x (e i) := by
  intro W packed child e α x i
  exact transpose_changeLayout packed child rfl (copySpectators v w rows splitRows) x i

open Cover.Fallback Stack Host

/-- The temporary has fields H₇,u,D₇ followed by the untouched v and inherited suffix. -/
def copyPackSchedule : List ℕ := (middleTailSchedule 1 7).map (7+·)

local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Execute the seven adjacent exchanges on a prepared record bank, including
header costs, and leave both active fields contiguous in the output. -/
theorem copyPack_exec [M8.Machine.Net] {P U : Type} [Fintype P] (body : P → Pr P (N+35) Q prime U)
    :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let d := 15
      let M := prime^(w+1)
      let suffix := M*W
      let bank : Fin 35 ↪ Fin (N+35) := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let clean := fun (S : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → S.L k = [] ∧ S.R k = []
      ∀ (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (original : Fin (M^d*suffix) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M),
      let ready := ColumnRecordReady bank (Nat.size M) (Nat.size suffix) record SparseRoleCircuit.encode
        (fun _ => blank) dest 0 q original
      ready addr S → clean S → ∃ z F n packed, z.user = v.user ∧
        n ≤ (setup+swaps*swapVolumeRate w)*(M^d*suffix) ∧
        Exec body (packSchedule d copyPackSchedule) (mk v S) n (mk z F) ∧
        ready packed F ∧ clean F ∧
        ∀ x (head mid tail : List (ZMod M)), head.length = 7 → mid.length = 1 → tail.length = 7 →
          List.ofFn (addr x) = head++mid++tail → List.ofFn (packed x) = head++tail++mid := by
  obtain ⟨setup,swaps,bound⟩ := packTime_le body 15 copyPackSchedule (by decide)
  refine ⟨setup,swaps,?_⟩
  intro w W hW d M suffix bank clean v S record dest q original addr ready start free
  have hs : 0 < suffix := Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) hW
  obtain ⟨z,F,n,user,cost,run,placed,clear⟩ := packSchedule_exec copyPackSchedule
    (by decide +kernel : ∀ i ∈ copyPackSchedule, i+1 < 15) (Nat.size M) (Nat.size suffix)
    (Nat.size_le.mp le_rfl) (Nat.size_le.mp le_rfl) hs body v S record dest q original addr start free
  exact ⟨z,F,n,_,user,cost.trans (bound w suffix hs),run,placed,clear,
    fun x head mid tail h m t layout => by
      simpa only [copyPackSchedule,h,m,t] using packMiddleTail_fields (addr x) head mid tail layout⟩

open FlatCoordinateLayout (rank) in
private theorem rankAppend {M a b : ℕ} [NeZero M] (x : Fin a → ZMod M) (y : Fin b → ZMod M) :
    (rank (Fin.append x y)).val = (rank x).val*M^b+(rank y).val :=
  ArbitraryWidthSliceTranspose.rank_append x y

open FlatCoordinateLayout (rank) in
/-- Treating the final low atom as part of the suffix leaves the caller's input
at exactly the original COPY tape position. -/
theorem copyPackingInput_index {w W : ℕ} (h d : Fin 7 → ZMod (prime^(w+1)))
    (u v : Fin 1 → ZMod (prime^(w+1))) (j : Fin W) :
    let suffix := finProdFinEquiv ((rank v).cast (pow_one _),j)
    (FlatCoordinateLayout.index (Fin.append (Fin.append h u) d) suffix).val =
      (index (copyChildAddress h d u v j)).val := by
  intro suffix
  rw [FlatCoordinateLayout.index_val,rankAppend,rankAppend,RecursiveInterchangeScaling.index_val]
  simp only [copyChildAddress,copyChild,RecursiveInterchangeLayout.index,suffix,Fin.val_cast,
    Fin.val_zero,zero_mul,zero_add,pow_one,finProdFinEquiv,Equiv.coe_fn_mk]
  rw [show prime^(7*(w+1)) = (prime^(w+1))^7 by rw [← pow_mul,Nat.mul_comm]]

open FlatCoordinateLayout (rank) in
/-- The packed host record and the active-first descriptor address name the same tape cell. -/
theorem copyPacked_index {w W : ℕ} (h d : Fin 7 → ZMod (prime^(w+1)))
    (u v : Fin 1 → ZMod (prime^(w+1))) (j : Fin W) :
    let suffix := finProdFinEquiv ((rank v).cast (pow_one _), j)
    (FlatCoordinateLayout.index (Fin.append (Fin.append h d) u) suffix).val =
      (packActive (copyChild (w+1) W) (index (copyChildAddress h d u v j))).val := by
  intro suffix
  rw [packActive_index, FlatCoordinateLayout.index_val, rankAppend, rankAppend]
  let M := prime^(w+1)
  change _ = (j.val + W*(rank v).val + (M*W)*((rank u).val + M*(0+0+0))) +
    (1*1*1*M*(M*W))*((rank d).val + prime^(7*(w+1))*(rank h).val)
  dsimp only [M,suffix,finProdFinEquiv,Equiv.coe_fn_mk,Fin.val_cast]
  rw [show prime^(7*(w+1)) = (prime^(w+1))^7 by rw [← pow_mul, Nat.mul_comm]]
  ring

/-- Physical position of a recursive child cell on the packed COPY tape. -/
noncomputable def copyRecursivePosition (parent : Descriptor) (w rows : ℕ)
    (splitRows : parent.rows = 142080*rows) :
    let M := prime^(w+1)
    let W := M^112 * (parent.beforeRows*rows*parent.beforeH*parent.between*parent.afterD)
    let child := rankDescriptor prime (7*(w+1)) (57*(w+1)) (role parent 142080)
    Fin (volume prime child) ≃ Fin (M^15*(M*W)) := by
  intro M W child
  refine (packActive child).trans (finCongr ?_)
  have size := Fintype.card_congr ((copyChildLayoutEquiv parent (w+1) rows splitRows).trans (packActive child))
  simp only [Fintype.card_fin,copyChild_volume] at size
  rw [← size]
  change M^16*W = M^15*(M*W)
  ring

/-- A recursive transpose on the selected child, read in active-first order,
supplies the packed COPY swap at every physical suffix position. -/
theorem copyRecursivePacked_swap (parent : Descriptor) (w rows : ℕ)
    (splitRows : parent.rows = 142080*rows) :
    let M := prime^(w+1)
    let W := M^112 * (parent.beforeRows*rows*parent.beforeH*parent.between*parent.afterD)
    let child := rankDescriptor prime (7*(w+1)) (57*(w+1)) (role parent 142080)
    let position := copyRecursivePosition parent w rows splitRows
    ∀ {α : Type} (word changed : Fin (M^15*(M*W)) → α),
      (∀ i, changed (position i) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows)
        (word ∘ position) i) →
      ∀ (h d : Fin 7 → ZMod M) (u : Fin 1 → ZMod M) (j : Fin (M*W)),
        changed (FlatCoordinateLayout.index (Fin.append (Fin.append d h) u) j) =
          word (FlatCoordinateLayout.index (Fin.append (Fin.append h d) u) j) := by
  intro M W child position α word changed after h d u j
  let input := word ∘ position
  obtain ⟨⟨low,j⟩,rfl⟩ := finProdFinEquiv.surjective j
  let v := (FlatCoordinateLayout.rankEquiv : (Fin 1 → ZMod M) ≃ Fin (M^1)).symm
    (low.cast (pow_one M).symm)
  have digit : (FlatCoordinateLayout.rank v).cast (pow_one M) = low := by
    change ((FlatCoordinateLayout.rankEquiv _) : Fin (M^1)).cast _ = _
    simp [v]
  let e := copyChildLayoutEquiv parent (w+1) rows splitRows
  let addr := fun h d => index (copyChildAddress h d u v j)
  have location (h d : Fin 7 → ZMod M) :
      (FlatCoordinateLayout.index (Fin.append (Fin.append h d) u) (finProdFinEquiv (low,j))).val =
        (packActive child (e (addr h d))).val := by
    rw [copyChildLayout_route parent (w+1) rows splitRows]
    simpa only [digit] using copyPacked_index h d u v j
  have cell (h d : Fin 7 → ZMod M) :
      FlatCoordinateLayout.index (Fin.append (Fin.append h d) u) (finProdFinEquiv (low,j)) =
        position (e (addr h d)) := Fin.ext (location h d)
  rw [cell d h,cell h d,after]
  change Shared50RecursiveNodeRows.transpose (one_dvd child.rows) input _ = input _
  rw [← copyChild_reindex parent (w+1) rows splitRows input (addr d h)]
  exact Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd _)
    (input ∘ e) (copyChildAddress h d u v j)

/-- The packed swap equation determines the returned word on the entire
recursive descriptor, including all spectator cells. -/
theorem copyPacked_recursiveTranspose (parent : Descriptor) (w rows : ℕ)
    (splitRows : parent.rows = 142080*rows) :
    let M := prime^(w+1)
    let W := M^112 * (parent.beforeRows*rows*parent.beforeH*parent.between*parent.afterD)
    let position := copyRecursivePosition parent w rows splitRows
    ∀ {α : Type} (word changed : Fin (M^15*(M*W)) → α),
      (∀ (h d : Fin 7 → ZMod M) (u : Fin 1 → ZMod M) (j : Fin (M*W)),
        changed (FlatCoordinateLayout.index (Fin.append (Fin.append d h) u) j) =
          word (FlatCoordinateLayout.index (Fin.append (Fin.append h d) u) j)) →
      ∀ i, changed (position i) = Shared50RecursiveNodeRows.transpose (one_dvd _) (word ∘ position) i := by
  intro M W position α word changed swap
  let expected := Shared50RecursiveNodeRows.transpose (one_dvd _) (word ∘ position) ∘ position.symm
  have correct i : expected (position i) = Shared50RecursiveNodeRows.transpose (one_dvd _) (word ∘ position) i := by
    exact congrArg (Shared50RecursiveNodeRows.transpose (one_dvd _) (word ∘ position)) (position.symm_apply_apply i)
  have known := copyRecursivePacked_swap parent w rows splitRows word expected correct
  have same : changed = expected := by
    funext k
    obtain ⟨⟨a,j⟩,rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨x,rfl⟩ := (FlatCoordinateLayout.rankEquiv : (Fin 15 → ZMod M) ≃ Fin (M^15)).surjective a
    let dh := fun i : Fin 14 => x (i.castAdd 1)
    let d := fun i : Fin 7 => dh (i.castAdd 7)
    let h := fun i : Fin 7 => dh (i.natAdd 7)
    let u := fun i : Fin 1 => x (i.natAdd 14)
    have layout : Fin.append (Fin.append d h) u = x := by
      rw [show Fin.append d h = dh from Fin.append_castAdd_natAdd (m := 7) (n := 7)]
      exact Fin.append_castAdd_natAdd (m := 14) (n := 1)
    change changed (FlatCoordinateLayout.index x j) = expected (FlatCoordinateLayout.index x j)
    rw [← layout,swap,known]
  exact fun i => same ▸ correct i

/-- Invoke the recursive procedure on the packed record. The induction
hypothesis is needed only at the strict child width, and the stack call
adds two steps to the child's execution. -/
theorem copyPackedCall_exec [M8.Machine.Net] {P U : Type}
    (body : P → Pr P (N+35) Q prime U) (f : P) (parent : Descriptor) (w rows : ℕ)
    (width : parent.width = 64*(w+1)) (splitRows : parent.rows = 142080*rows) :
    let M := prime^(w+1)
    let W := M^112 * (parent.beforeRows*rows*parent.beforeH*parent.between*parent.afterD)
    let child := rankDescriptor prime (7*(w+1)) (57*(w+1)) (role parent 142080)
    let position := copyRecursivePosition parent w rows splitRows
    let bank : Fin 35 ↪ Fin (N+35) := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let stored := RecordReady (b := prime) (w := w) (d := 15) (W := M*W) bank M.size (M*W).size []
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun (D : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → D.L k = [] ∧ D.R k = []
    ∀ budget : ℕ,
      (child.width < parent.width → ∀ v S word, stored word S → clean S → ∃ z F n changed, z.user = v.user ∧
        n ≤ budget ∧ Exec body (body f) (mk v S) n (mk z F) ∧ stored changed F ∧ clean F ∧
        ∀ i, changed (position i) = Shared50RecursiveNodeRows.transpose (one_dvd _) (word ∘ position) i) →
      ∀ v S word, stored word S → clean S → ∃ z F n changed, z.user = v.user ∧ n ≤ budget+2 ∧
        Exec body (.call f) (mk v S) n (mk z F) ∧ stored changed F ∧ clean F ∧
        ∀ (h d : Fin 7 → ZMod M) (u : Fin 1 → ZMod M) (j : Fin (M*W)),
          changed (FlatCoordinateLayout.index (Fin.append (Fin.append d h) u) j) =
            word (FlatCoordinateLayout.index (Fin.append (Fin.append h d) u) j) := by
  intro M W child position bank stored clean budget recurse v S word ready free
  have smaller : child.width < parent.width := by
    rw [width]
    change 7*(w+1) < 64*(w+1)
    omega
  obtain ⟨z,F,n,changed,user,time,run,returned,clear,transpose⟩ := recurse smaller v S word ready free
  exact ⟨z,F,n+2,changed,user,Nat.add_le_add_right time 2,Exec.call run,returned,clear,
    copyRecursivePacked_swap parent w rows splitRows word changed transpose⟩

/-- The prepared output of the seven exchanges contains the incoming COPY bit
at its active-first descriptor position, including the final untouched atom. -/
theorem copyPacked_read {w W T H J : ℕ}
    (bank : Fin 35 ↪ Fin T) (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (S : Stacks T prime) (original : Fin ((prime^(w+1))^15*(prime^(w+1)*W)) → ZMod 2)
    (packed : (Fin 15 → ZMod (prime^(w+1))) → Fin 15 → ZMod (prime^(w+1)))
    (ready : ColumnRecordReady bank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original packed S)
    (order : ∀ x (head mid tail : List (ZMod (prime^(w+1)))), head.length = 7 → mid.length = 1 →
      tail.length = 7 → List.ofFn x = head++mid++tail → List.ofFn (packed x) = head++tail++mid) :
    ∃ word, RecordReady (b := prime) (w := w) (W := prime^(w+1)*W) (d := 15)
      bank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q word S ∧
      ∀ (h d : Fin 7 → ZMod (prime^(w+1))) (u v : Fin 1 → ZMod (prime^(w+1))) (j : Fin W),
        let suffix := finProdFinEquiv ((FlatCoordinateLayout.rank v).cast (pow_one _), j)
        ∃ k, k.val = (packActive (copyChild (w+1) W) (index (copyChildAddress h d u v j))).val ∧
          word k = original (FlatCoordinateLayout.index (Fin.append (Fin.append h u) d) suffix) := by
  obtain ⟨word, stored, reads⟩ := ready
  refine ⟨word, stored, ?_⟩
  intro h d u v j suffix
  let x := Fin.append (Fin.append h u) d
  have moved : packed x = Fin.append (Fin.append h d) u := by
    apply List.ofFn_injective
    simpa only [List.ofFn_fin_append] using order x (List.ofFn h) (List.ofFn u) (List.ofFn d)
      (by simp) (by simp) (by simp) (by change List.ofFn (Fin.append (Fin.append h u) d) = _; rw [List.ofFn_fin_append, List.ofFn_fin_append])
  refine ⟨_, copyPacked_index h d u v j, ?_⟩
  simpa only [moved] using reads x suffix

private theorem copyPack_fields {α : Type} (h d : Fin 7 → α) (u : Fin 1 → α) :
    copyPackSchedule.foldl adjacentFields (Fin.append (Fin.append h u) d) = Fin.append (Fin.append h d) u := by
  apply List.ofFn_injective
  have layout := packMiddleTail_fields (Fin.append (Fin.append h u) d)
    (List.ofFn h) (List.ofFn u) (List.ofFn d) (by rw [List.ofFn_fin_append,List.ofFn_fin_append])
  simpa only [List.length_ofFn,copyPackSchedule,List.ofFn_fin_append] using layout

open FlatCoordinateLayout (index) in
/-- Transport a packed seven-field swap back to the caller's coordinates. -/
theorem copySwap_reads {M W : ℕ} [NeZero M] {α : Type*}
    {input output word changed : Fin (M^15*W) → α}
    (read : ∀ x j, word (index (copyPackSchedule.foldl adjacentFields x) j) = input (index x j))
    (swap : ∀ (h d : Fin 7 → ZMod M) (u : Fin 1 → ZMod M) (j : Fin W),
      changed (index (Fin.append (Fin.append d h) u) j) = word (index (Fin.append (Fin.append h d) u) j))
    (logical : ∀ (h d : Fin 7 → ZMod M) (u : Fin 1 → ZMod M) (j : Fin W),
      output (index (Fin.append (Fin.append d u) h) j) = input (index (Fin.append (Fin.append h u) d) j)) :
    ∀ x j, changed (index (copyPackSchedule.foldl adjacentFields x) j) = output (index x j) := by
  intro x j
  let pre := fun i : Fin 8 => x (i.castAdd 7)
  let h := fun i : Fin 7 => pre (i.castAdd 1)
  let u := fun i : Fin 1 => pre (i.natAdd 7)
  let d := fun i : Fin 7 => x (i.natAdd 8)
  have split : Fin.append (Fin.append h u) d = x := by
    rw [show Fin.append h u = pre from Fin.append_castAdd_natAdd (m := 7) (n := 1)]
    exact Fin.append_castAdd_natAdd (m := 8) (n := 7)
  rw [← split]
  rw [copyPack_fields h d u,swap d h u j]
  apply Eq.trans _ (logical d h u j).symm
  simpa only [id_eq,copyPack_fields] using read (Fin.append (Fin.append d u) h) j

/-- The descriptor transpose satisfies the logical output equation of the
host wrapper at every suffix position. -/
theorem copyPacking_transpose {w W : ℕ}
    (input : Fin (volume prime (copyChild (w+1) W)) → ZMod 2) :
    let M := prime^(w+1)
    let size : M^15*(M*W) = volume prime (copyChild (w+1) W) := by
      rw [copyChild_volume]; change M^15*(M*W) = M^16*W; ring
    ∀ (h d : Fin 7 → ZMod M) (u : Fin 1 → ZMod M) (j : Fin (M*W)),
      Shared50RecursiveNodeRows.transpose (one_dvd _) input
        ((FlatCoordinateLayout.index (Fin.append (Fin.append d u) h) j).cast size) =
        input ((FlatCoordinateLayout.index (Fin.append (Fin.append h u) d) j).cast size) := by
  intro M size h d u j
  obtain ⟨⟨low,j⟩,rfl⟩ := finProdFinEquiv.surjective j
  let v := (FlatCoordinateLayout.rankEquiv : (Fin 1 → ZMod M) ≃ Fin (M^1)).symm
    (low.cast (pow_one M).symm)
  have digit : (FlatCoordinateLayout.rank v).cast (pow_one M) = low := by
    change ((FlatCoordinateLayout.rankEquiv _) : Fin (M^1)).cast _ = _
    simp [v]
  have addr (h d : Fin 7 → ZMod M) : (FlatCoordinateLayout.index (Fin.append (Fin.append h u) d)
      (finProdFinEquiv (low,j))).cast size = index (copyChildAddress h d u v j) := by
    apply Fin.ext
    simpa only [Fin.val_cast,digit] using copyPackingInput_index h d u v j
  rw [addr,addr]
  exact Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1) (one_dvd _) input (copyChildAddress h d u v j)

/-- Direct execution of the packed rank-seven swap, with its actual tape cost.
This gives a terminating child at widths where recursion stops. -/
theorem copyPackedBase_exec [M8.Machine.Net] {P U : Type} [Fintype P]
    (body : P → Pr P (N+35) Q prime U) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let bank : Fin 35 ↪ Fin (N+35) := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let clean := fun (D : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → D.L k = [] ∧ D.R k = []
      ∀ (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
        (word : Fin (M^15*W) → ZMod 2),
      let stored := RecordReady (b := prime) (w := w) (d := 15) (W := W) bank M.size W.size []
        SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      stored word S → clean S → ∃ z F n changed, z.user = v.user ∧
        n ≤ (setup+swaps*swapVolumeRate w)*(M^15*W) ∧
        Exec body (packSchedule 15 (middleTailSchedule 7 7)) (mk v S) n (mk z F) ∧
        stored changed F ∧ clean F ∧
        ∀ (h d : Fin 7 → ZMod M) (u : Fin 1 → ZMod M) (j : Fin W),
          changed (FlatCoordinateLayout.index (Fin.append (Fin.append d h) u) j) =
            word (FlatCoordinateLayout.index (Fin.append (Fin.append h d) u) j) := by
  let schedule := middleTailSchedule 7 7
  have fits : ∀ i ∈ schedule, i+1 < 15 := fun i hi =>
    Nat.lt_trans (middleTailSchedule_inside hi) (by decide)
  obtain ⟨setup,swaps,bill⟩ := packTime_le body 15 schedule (by decide)
  refine ⟨setup,swaps,?_⟩
  intro w W hW M bank clean v S word stored start free
  obtain ⟨z,F,n,user,time,run,⟨changed,ready,read⟩,clear⟩ := packSchedule_exec schedule fits
    M.size W.size (Nat.size_le.mp le_rfl) (Nat.size_le.mp le_rfl) hW body v S [] (fun _ => blank) 0 word id
    ⟨word,start,fun _ _ => rfl⟩ free
  refine ⟨z,F,n,changed,user,time.trans (bill w W hW),run,ready,clear,?_⟩
  intro h d u j
  have order : schedule.foldl adjacentFields (Fin.append (Fin.append h d) u) = Fin.append (Fin.append d h) u := by
    apply List.ofFn_injective
    rw [fold_adjacentFields _ _ fits]
    simpa only [List.ofFn_fin_append,List.length_ofFn,schedule] using
      middleTailSchedule_packs (List.ofFn h) (List.ofFn d) (List.ofFn u)
  simpa only [id_eq,order] using read (Fin.append (Fin.append h d) u) j

open FlatCoordinateLayout (index) in
/-- A child that swaps the two contiguous seven-atom fields suffices for COPY on
a prepared record. The reverse passes carry its changed word back to caller order. -/
theorem withCopyTranspose_exec [M8.Machine.Net] {P U : Type} [Fintype P]
    (body : P → Pr P (N+35) Q prime U) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let suffix := M*W
      let size : M^15*suffix = volume prime (copyChild (w+1) W) := by
        rw [copyChild_volume]; change M^15*(M*W) = M^16*W; ring
      let bank : Fin 35 ↪ Fin (N+35) := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let clean := fun (D : Stacks (N+35) prime) => ∀ k : Fin (N+35), 35 ≤ k.val → D.L k = [] ∧ D.R k = []
      ∀ (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (x : Fin (volume prime (copyChild (w+1) W)) → ZMod 2) (child : Pr P (N+35) Q prime U) (budget : ℕ),
      let input := fun i => x (Fin.cast size i)
      let output := fun i => Shared50RecursiveNodeRows.transpose (one_dvd _) x (Fin.cast size i)
      let stored := RecordReady (b := prime) (w := w) (d := 15) (W := suffix)
        bank (Nat.size M) (Nat.size suffix) record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      (∀ v D word, stored word D → clean D → ∃ z F n changed, z.user = v.user ∧ n ≤ budget ∧
        Exec body child (mk v D) n (mk z F) ∧ stored changed F ∧ clean F ∧
        ∀ (h d : Fin 7 → ZMod M) (u : Fin 1 → ZMod M) (j : Fin suffix),
          changed (FlatCoordinateLayout.index (Fin.append (Fin.append d h) u) j) =
          word (FlatCoordinateLayout.index (Fin.append (Fin.append h d) u) j)) →
      stored input S → clean S → ∃ z F n, z.user = v.user ∧
        n ≤ budget + 2*((setup+swaps*swapVolumeRate w)*(M^15*suffix)) ∧
        Exec body (.seq (packSchedule 15 copyPackSchedule) (.seq child (packSchedule 15 copyPackSchedule.reverse)))
          (mk v S) n (mk z F) ∧ stored output F ∧ clean F := by
  obtain ⟨setup,swaps,run⟩ := withPacking_exec body 15 copyPackSchedule (by decide) (by decide +kernel)
  refine ⟨setup,swaps,?_⟩
  intro w W hW M suffix size bank clean v S record dest q x child budget input output stored call start free
  have logical := copyPacking_transpose x
  have positive : 0 < suffix := Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) hW
  have step := run w suffix positive v S record dest q input output id child budget
  obtain ⟨z,F,n,user,bound,exec,⟨out,layout,reads⟩,clear⟩ := step (by
    intro v D prepared available
    obtain ⟨word,hw,read⟩ := prepared
    obtain ⟨z,F,n,changed,hz,hn,exec,placed,clear,swap⟩ := call v D word hw available
    refine ⟨z,F,n,hz,hn,exec,⟨changed,placed,?_⟩,clear⟩
    exact copySwap_reads read swap logical
    ) ⟨input,start,fun _ _ => rfl⟩ free
  have same : out = output := by
    funext i
    obtain ⟨⟨k,j⟩,rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨x,rfl⟩ := (FlatCoordinateLayout.rankEquiv : (Fin 15 → ZMod M) ≃ Fin (M^15)).surjective k
    exact reads x j
  exact ⟨z,F,n,user,bound,exec,same ▸ layout,clear⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
