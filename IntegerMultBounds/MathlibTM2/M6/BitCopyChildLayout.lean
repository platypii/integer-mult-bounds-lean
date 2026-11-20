module

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
  intro W packed child e
  let f := changeLayout packed child rfl (copySpectators v w rows splitRows)
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

end IntegerMultBounds.MathlibTM2.M6.BitNode
