module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperFanRun
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

private theorem intervalPack_index {lo hi w W : ℕ} (ordered : lo ≤ hi) (fits : hi ≤ 64)
    (x : Fin 128 → ZMod (prime^(w+1))) (j : Fin W) :
    let size := intervalChild_volume ordered fits (w+1) W
    let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
    FlatCoordinateLayout.index (is.foldl adjacentFields x) j =
      packedChildPosition _ size ((FlatCoordinateLayout.index x j).cast size.symm) := by
  intro size is
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
  apply Fin.ext
  change _ = (CopyChildLayout.packActive _ ((FlatCoordinateLayout.index x j).cast _)).val
  rw [entry]
  apply intervalPacked_offset a b h d u v j
  simpa only [mid,List.length_append,List.length_ofFn,is,List.append_assoc] using order

variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states

/-- Pack a split owner row at the exact positions read by the recursive child. -/
theorem intervalForward_exec {T capacity : ℕ} (fitsStates : Q ≤ capacity)
    (ports : Fin (N+35) ↪ Fin T) (body : P → Pr P T capacity prime U)
    (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) :
    ∃ setup swaps : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
      let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
      let clean := fun D : Stacks T prime => ∀ k : Fin (N+35), 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []
      ∀ (u : HS T capacity prime U) (S : Stacks T prime) record dest q
        (input : Fin (volume prime (phaseIntervalChild lo hi (w+1) W 64)) → ZMod 2),
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      let ready := RecordReady (b := prime) (w := w) (W := W) (d := 128) bank M.size W.size
        record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      ready (fun i => input (i.cast size.symm)) S → clean S → ∃ z F n, z.user = u.user ∧
        n ≤ 1+(setup+swaps*swapVolumeRate w)*(M^128*W) ∧
        Exec body (statePlacedNormalized ports fitsStates swapStates_pos Empty.elim (packSchedule 128 is))
          (mk u S) n (mk z F) ∧ ready (input ∘ position.symm) F ∧ clean F ∧
        ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
  have inside (i) (used : i ∈ is) : i+1 < 128 := by
    have := intervalPackSchedule_inside used
    omega
  obtain ⟨setup,swaps,price⟩ := packTime_le (P := Empty) (U := U) Empty.elim 128 is (by decide)
  refine ⟨setup,swaps,?_⟩
  intro w W hW M schedule bank clean u S record dest q input size position ready stored free
  obtain ⟨z,F,n,user,cost,exec,⟨word,out,read⟩,clear,frame⟩ := placedPackSchedule_exec fitsStates ports
    is inside body u S record dest q hW (fun i => input (i.cast size.symm)) id ⟨_,stored,fun _ _ => rfl⟩ free
  refine ⟨z,F,n,user,cost.trans (Nat.add_le_add_left (price w W hW) 1),exec,?_,clear,frame⟩
  suffices eq : word = input ∘ position.symm from eq ▸ out
  funext k
  obtain ⟨a,rfl⟩ := position.surjective k
  obtain ⟨i,rfl⟩ := (finCongr size.symm).surjective a
  obtain ⟨⟨digits,j⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨x,rfl⟩ := (FlatCoordinateLayout.rankEquiv : (Fin 128 → ZMod M) ≃ _).surjective digits
  change word (position ((FlatCoordinateLayout.index x j).cast size.symm)) = _
  rw [Function.comp_apply,Equiv.symm_apply_apply]
  exact (congrArg word (intervalPack_index ordered fits x j)).symm.trans (read x j)

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
    have moved : FlatCoordinateLayout.index (is.foldl adjacentFields x) j =
        position ((FlatCoordinateLayout.index x j).cast size.symm) := intervalPack_index ordered fits x j
    change word (FlatCoordinateLayout.index x j) = output ((FlatCoordinateLayout.index x j).cast size.symm)
    simpa only [id_eq,reverse_adjacentFields,Function.comp_apply,moved,Equiv.symm_apply_apply]
      using read (is.foldl adjacentFields x) j

theorem intervalPass_exec {T capacity : ℕ} (fitsStates : Q ≤ capacity)
    (ports : Fin (N+35) ↪ Fin T) (body : P → Pr P T capacity prime U)
    (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) (unpack : Bool) :
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
      ready (if unpack then output ∘ position.symm else fun i => output (i.cast size.symm)) S → clean S → ∃ z F n, z.user = u.user ∧
        n ≤ 1+(setup+swaps*swapVolumeRate w)*(M^128*W) ∧
        Exec body (statePlacedNormalized ports fitsStates swapStates_pos Empty.elim (packSchedule 128 (if unpack then is.reverse else is)))
          (mk u S) n (mk z F) ∧ ready (if unpack then fun i => output (i.cast size.symm) else output ∘ position.symm) F ∧ clean F ∧
        ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  cases unpack with
  | false => exact intervalForward_exec fitsStates ports body lo hi ordered fits
  | true => exact intervalReturn_exec fitsStates ports body lo hi ordered fits

omit [M8.Machine.Net] in
/-- Sequence the unpackers on disjoint record banks. Each completed row and
each pending input retains both stacks while another row is unpacked. -/
theorem returnRows_exec {ι : Type} {T A capacity B : ℕ} (body : P → Pr P T capacity A U)
    (ports : ι → Fin B ↪ Fin T) (apart : ∀ i j, i ≠ j → ∀ a b, ports i a ≠ ports j b)
    (code : ι → Pr P T capacity A U) (price : ι → ℕ)
    (ready doneRow : ι → Stacks T A → Prop)
    (localReady : ∀ i S F, (∀ k, F.L (ports i k) = S.L (ports i k) ∧
      F.R (ports i k) = S.R (ports i k)) → ready i S → ready i F)
    (localDone : ∀ i S F, (∀ k, F.L (ports i k) = S.L (ports i k) ∧
      F.R (ports i k) = S.R (ports i k)) → doneRow i S → doneRow i F)
    (shared : Stacks T A → Prop)
    (preserve : ∀ i S F, (∀ j, (∀ k, ports i k ≠ j) →
      F.L j = S.L j ∧ F.R j = S.R j) → shared S → shared F)
    (step : ∀ i u S, shared S → ready i S → ∃ z F n, Exec body (code i) (mk u S) n (mk z F) ∧
      n ≤ price i ∧ z.user = u.user ∧ doneRow i F ∧
      ∀ j, (∀ k, ports i k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j)
    (rows : List ι) (unique : rows.Nodup) (u : HS T capacity A U) (S : Stacks T A)
    (common : shared S) (inputs : ∀ i ∈ rows, ready i S) :
    ∃ z F n, Exec body (Prog.seqList (rows.map code)) (mk u S) n (mk z F) ∧
      n ≤ (rows.map price).sum+1 ∧ z.user = u.user ∧ (∀ i ∈ rows, doneRow i F) ∧
      ∀ j, (∀ i ∈ rows, ∀ k, ports i k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  induction rows generalizing u S with
  | nil => exact ⟨u,S,1,Exec.act .done _,by simp,rfl,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons i rows ih =>
    obtain ⟨fresh,distinct⟩ := List.nodup_cons.mp unique
    obtain ⟨v,D,t,run,paid,user,finished,keep⟩ := step i u S common (inputs i List.mem_cons_self)
    obtain ⟨z,F,n,tail,cost,same,returned,frame⟩ := ih distinct v D (preserve i S D keep common) (fun j hj =>
      localReady j S D (fun k => keep _ (fun a => apart i j (fun eq => fresh (eq ▸ hj)) a k))
        (inputs j (List.mem_cons_of_mem _ hj)))
    refine ⟨z,F,t+n,Exec.seq run tail,by simp only [List.map_cons,List.sum_cons]; omega,
      same.trans user,?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | member
      · exact localDone _ D F (fun k => frame _ (fun a ha b =>
          apart a j (fun eq => fresh (eq ▸ ha)) b k)) finished
      · exact returned j member
    · intro j outside
      have after := frame j (fun a ha => outside a (List.mem_cons_of_mem _ ha))
      have before := keep j (outside i List.mem_cons_self)
      exact ⟨after.1.trans before.1,after.2.trans before.2⟩

section
omit [M8.Machine.Net]

/-- Route each record's payload port to its existing owner. All other
ports use a separate block of registers indexed by owner and local port. -/
def intervalRecordBank {c T B : ℕ} (fan : Fin (c+2) ↪ Fin T) (payload : Fin B) (r : Fin c) :
    Fin B ↪ Fin (T+c*B) :=
  let place := fun k : Fin B => if k = payload then Sum.inl (fan (r.castAdd 2))
    else Sum.inr (finProdFinEquiv (r,k))
  (⟨place,by
    intro i j eq
    by_cases hi : i = payload <;> by_cases hj : j = payload <;>
      simp_all [place]⟩ : Fin B ↪ Fin T ⊕ Fin (c*B)).trans finSumFinEquiv.toEmbedding

theorem intervalRecordBank_payload {c T B : ℕ} (fan : Fin (c+2) ↪ Fin T) (p : Fin B) (r : Fin c) :
    intervalRecordBank fan p r p = (fan (r.castAdd 2)).castAdd (c*B) := by
  simp [intervalRecordBank]

theorem intervalRecordBank_apart {c T B : ℕ} (fan : Fin (c+2) ↪ Fin T) (p : Fin B)
    {r s : Fin c} (ne : r ≠ s) (i j : Fin B) :
    intervalRecordBank fan p r i ≠ intervalRecordBank fan p s j := by
  intro eq
  have same := finSumFinEquiv.injective eq
  by_cases hi : i = p <;> by_cases hj : j = p <;>
    simp_all [intervalRecordBank,fan.injective.eq_iff]

theorem intervalRecordBank_outside {c T B : ℕ} (fan : Fin (c+2) ↪ Fin T) (p : Fin B)
    (t : Fin T) (outside : ∀ r : Fin c, fan (r.castAdd 2) ≠ t) (r : Fin c) (i : Fin B) :
    intervalRecordBank fan p r i ≠ t.castAdd (c*B) := by
  intro eq
  change finSumFinEquiv _ = finSumFinEquiv (Sum.inl t) at eq
  have same := finSumFinEquiv.injective eq
  by_cases hi : i = p <;> simp_all

end

/-- Run either direction of interval packing across the cyclic owner rows. -/
theorem intervalPassBank_exec {T capacity : ℕ} (fitsStates : Q ≤ capacity)
    (ports : Fin 142080 → Fin (N+35) ↪ Fin T)
    (apart : ∀ i j, i ≠ j → ∀ a b, ports i a ≠ ports j b)
    (body : P → Pr P T capacity prime U) (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) (unpack : Bool) :
    ∃ setup swaps : Fin 142080 → ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
      let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      ∀ (u : HS T capacity prime U) (S : Stacks T prime) (record : Fin 142080 → List (Fin (prime+4)))
        (dest : Fin 142080 → ℤ → Fin 4) (q : Fin 142080 → ℤ)
        (output : Fin 142080 → Fin (volume prime (phaseIntervalChild lo hi (w+1) W 64)) → ZMod 2),
      let inherited := fun r (i : Fin (M^128*W)) => output r (i.cast size.symm)
      let packedRows := fun r => output r ∘ position.symm
      let fromRow := fun r => if unpack then packedRows r else inherited r
      let toRow := fun r => if unpack then inherited r else packedRows r
      let stored := fun r word F => RecordReady (b := prime) (w := w) (W := W) (d := 128)
        (small.trans (ports r)) M.size W.size (record r) SparseRoleCircuit.encode (fun _ => blank)
        (dest r) 0 (q r) word F ∧ ∀ k : Fin (N+35), 35 ≤ k.val →
          F.L (ports r k) = [] ∧ F.R (ports r k) = []
      ∀ fan : Fin (142080+2) ↪ Fin T,
      (∀ r : Fin 142080, ports r (small 24) = fan (r.castAdd 2)) →
      (∀ j : Fin 2, ∀ r k, ports r k ≠ fan (j.natAdd 142080)) →
      HelperFan fan fromRow S →
      (∀ r, ∃ word D, stored r word D ∧ ∀ k, k ≠ small 24 →
        S.L (ports r k) = D.L (ports r k) ∧ S.R (ports r k) = D.R (ports r k)) →
      let code := fun r => statePlacedNormalized (ports r) fitsStates swapStates_pos Empty.elim (packSchedule 128 (if unpack then is.reverse else is))
      ∃ z F n, Exec body (Prog.seqList ((List.finRange 142080).map code)) (mk u S) n (mk z F) ∧
        n ≤ ((List.finRange 142080).map (fun r => 1+(setup r+swaps r*swapVolumeRate w)*(M^128*W))).sum+1 ∧
        z.user = u.user ∧ HelperFan fan toRow F ∧
        (∀ r, stored r (toRow r) F) ∧
        ∀ j, (∀ r k, ports r k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  choose setup swaps run using fun r => intervalPass_exec fitsStates (ports r) body lo hi ordered fits unpack
  refine ⟨setup,swaps,?_⟩
  intro w W hW M is small size position u S record dest q output inherited packedRows fromRow toRow stored fan shared counters live saved code
  have transfer r word (D F : Stacks T prime)
      (keep : ∀ k, F.L (ports r k) = D.L (ports r k) ∧ F.R (ports r k) = D.R (ports r k))
      (ready : stored r word D) : stored r word F := by
    refine ⟨ready.1.returnPayload (fun i _ => keep (small i)) (fun z => ?_),?_⟩
    · change _ = readAt blank (F.L (ports r (small 24))) (F.R (ports r (small 24))) _
      rw [(keep _).1,(keep _).2]
      exact (ready.1.src z).symm
    · intro k hk
      exact ⟨(keep k).1.trans (ready.2 k hk).1,(keep k).2.trans (ready.2 k hk).2⟩
  have inputs r : stored r (fromRow r) S := by
    obtain ⟨word,D,old,keep⟩ := saved r
    refine ⟨old.1.returnPayload (fun i ne => keep (small i) (small.injective.ne ne)) (fun z => ?_),?_⟩
    · change _ = readAt blank (S.L (ports r (small 24))) (S.R (ports r (small 24))) _
      rw [shared]
      simpa only [List.map_ofFn] using (fanPayload live r z).symm
    · intro k hk
      have ne : k ≠ small 24 := by
        intro eq
        have h := congrArg Fin.val eq
        change k.val = 24 at h
        omega
      exact ⟨(keep k ne).1.trans (old.2 k hk).1,(keep k ne).2.trans (old.2 k hk).2⟩
  obtain ⟨z,F,n,exec,paid,user,doneRows,frame⟩ := returnRows_exec body ports apart code _
    (fun r => stored r (fromRow r)) (fun r => stored r (toRow r))
    (fun r => transfer r _) (fun r => transfer r _) (fun _ => True)
    (fun _ _ _ _ h => h) (fun r v D _ ready => by
      obtain ⟨z,F,n,user,paid,exec,out,clear,frame⟩ := run r w W hW v D (record r) (dest r) (q r)
        (output r) ready.1 ready.2
      exact ⟨z,F,n,exec,paid,user,⟨out,clear⟩,frame⟩)
    (List.finRange 142080) (List.nodup_finRange _) u S trivial (fun r _ => inputs r)
  refine ⟨z,F,n,exec,paid,user,?_,fun r => doneRows r (List.mem_finRange r),fun j h => frame j (fun r _ => h r)⟩

  intro i z
  induction i using Fin.addCases with
  | left r =>
    have cell := (doneRows r (List.mem_finRange r)).1.src z
    have encoded := encodedOwnerCell (toRow r) z
    rw [List.map_ofFn] at encoded
    rw [encoded] at cell
    simp only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply]
    change putWord _ 0 (List.ofFn fun i => SparseRoleCircuit.encode (toRow r i)) z =
      readAt blank _ _ _
    simpa only [Function.Embedding.trans_apply,shared] using cell.symm
  | right j =>
    have keep := frame (fan (j.natAdd 142080)) (fun r _ k => counters j r k)
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,
      keep.1,keep.2,CountedLoopReuseAlphabet.controls,ite_self] using live (j.natAdd 142080) z

theorem placedIntervalPass_exec {T capacity : ℕ} (fitsStates : Q ≤ capacity)
    (live : Fin (142080+2) ↪ Fin T)
    (body : P → Pr P (T+142080*(N+35)) capacity prime U) (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ 64) (unpack : Bool) :
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank live (small 24)
    let fan := live.trans (Fin.castAddEmb (142080*(N+35)))
    ∃ setup swaps : Fin 142080 → ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      let is := intervalPackSchedule lo (hi-lo) (64-hi+lo)
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      ∀ (u : HS (T+142080*(N+35)) capacity prime U) (S : Stacks (T+142080*(N+35)) prime) (record : Fin 142080 → List (Fin (prime+4)))
        (dest : Fin 142080 → ℤ → Fin 4) (q : Fin 142080 → ℤ)
        (output : Fin 142080 → Fin (volume prime (phaseIntervalChild lo hi (w+1) W 64)) → ZMod 2),
      let inherited := fun r (i : Fin (M^128*W)) => output r (i.cast size.symm)
      let packedRows := fun r => output r ∘ position.symm
      let fromRow := fun r => if unpack then packedRows r else inherited r
      let toRow := fun r => if unpack then inherited r else packedRows r
      let stored := fun r word F => RecordReady (b := prime) (w := w) (W := W) (d := 128)
        (small.trans (ports r)) M.size W.size (record r) SparseRoleCircuit.encode (fun _ => blank)
        (dest r) 0 (q r) word F ∧ ∀ k : Fin (N+35), 35 ≤ k.val →
          F.L (ports r k) = [] ∧ F.R (ports r k) = []
      HelperFan fan fromRow S →
      (∀ r, ∃ word D, stored r word D ∧ ∀ k, k ≠ small 24 →
        S.L (ports r k) = D.L (ports r k) ∧ S.R (ports r k) = D.R (ports r k)) →
      let code := fun r => statePlacedNormalized (ports r) fitsStates swapStates_pos Empty.elim (packSchedule 128 (if unpack then is.reverse else is))
      ∃ z F n, Exec body (Prog.seqList ((List.finRange 142080).map code)) (mk u S) n (mk z F) ∧
        n ≤ ((List.finRange 142080).map (fun r => 1+(setup r+swaps r*swapVolumeRate w)*(M^128*W))).sum+1 ∧
        z.user = u.user ∧ HelperFan fan toRow F ∧
        (∀ r, stored r (toRow r) F) ∧
        ∀ j, (∀ r : Fin 142080, live (r.castAdd 2) ≠ j) →
          let t := j.castAdd (142080*(N+35))
          F.L t = S.L t ∧ F.R t = S.R t := by
  intro small ports fan
  obtain ⟨setup,swaps,run⟩ := intervalPassBank_exec fitsStates ports
    (fun _ _ ne => intervalRecordBank_apart live _ ne) body lo hi ordered fits unpack
  refine ⟨setup,swaps,?_⟩
  intro w W hW M is size position u S record dest q output inherited packedRows fromRow toRow stored packed saved code
  obtain ⟨z,F,n,exec,paid,user,returned,records,frame⟩ :=
    run w W hW u S record dest q output fan (intervalRecordBank_payload live _)
      (fun j r k => intervalRecordBank_outside live _ _ (fun i => live.injective.ne (by
        intro eq
        have h := congrArg Fin.val eq
        change i.val = 142080+j.val at h
        omega)) r k) packed saved
  exact ⟨z,F,n,exec,paid,user,returned,records,fun j outside =>
    frame _ (intervalRecordBank_outside live _ j outside)⟩

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
