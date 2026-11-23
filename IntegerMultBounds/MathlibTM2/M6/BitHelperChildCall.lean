module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperSlotSchedule
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Call an inherited helper interval using the scheduled worker's record contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open RecursiveInterchangeRows Shared50RecursiveNodeRows in
/-- After a cyclic row split, reads on each returned role suffice for the whole
scheduled child, including when the role descriptor has several row groups. -/
theorem inheritedTranspose_of_roleReads {V c : ℕ} {child physical : Descriptor}
    {size : volume prime physical = V} {position : Fin (volume prime child) ≃ Fin V}
    (coords : InheritedIntervalPositions child physical size position) (width : physical.width = child.width)
    (positive : 0 < c) (stock : c ∣ physical.rows) {α : Type} (word changed : Fin V → α) :
    let span := (volume_split prime c physical stock).symm.trans size
    let cell := fun g (j : Fin c) k => (pack g (pack j k)).cast span
    (∀ g j k, changed (cell g j k) = word (cell g j (swapSuffix k))) →
    ∀ k, changed (position k) = transpose (one_dvd child.rows) (word ∘ position) k := by
  intro span cell reads
  apply (coords.transpose_iff width word changed).2
  rw [Shared50RecursiveChildPermutation.transpose_independent (by decide : 0 < 1) positive
    (one_dvd physical.rows) stock]
  funext k
  obtain ⟨⟨g,r⟩,eq⟩ := finProdFinEquiv.surjective (k.cast span.symm)
  obtain ⟨⟨j,z⟩,rfl⟩ := finProdFinEquiv.surjective r
  have h : k = cell g j z := Fin.ext (congrArg Fin.val eq).symm
  subst k
  exact (reads g j z).trans (transpose_entry stock (fun i => word (i.cast size)) g j z).symm

open RecursiveInterchangeRows Shared50RecursiveNodeRows in
/-- The role descriptor retains the group's suffix fields, so its own transpose
performs exactly the read needed at the cyclic merge. -/
theorem transpose_roleIndex {α : Type*} (v : Descriptor) (c : ℕ)
    (word : Fin (volume prime (role v c)) → α) (g : Fin (groups c v)) (k : Fin (rowLength prime v)) :
    transpose (one_dvd (role v c).rows) word (roleIndex prime c v g k) =
      word (roleIndex prime c v g (swapSuffix k)) := by
  let lane := role v c
  have count : groups 1 lane = groups c v := by simp [groups,lane,role]
  let group := g.cast count.symm
  have cell (z : Fin (rowLength prime v)) :
      ((pack group (pack (0 : Fin 1) z)).cast (volume_split prime 1 lane (one_dvd _)).symm) =
        roleIndex prime c v g z := by
    apply Fin.ext
    change (pack group (pack (0 : Fin 1) z)).val = (pack g z).val
    simp only [pack_val,group,Fin.val_cast,Fin.val_zero,zero_mul,zero_add,one_mul]
  rw [← cell k,← cell (swapSuffix k)]
  exact transpose_entry (one_dvd lane.rows) word group 0 k

open RecursiveInterchangeRows Shared50RecursiveNodeRows FlatCoordinateSchedule in
/-- Merge returned role tapes at their origins into the transposed physical word.
Both counters are canonical; the bound includes every group in the descriptor. -/
theorem helperRoleMerge_runs {c : ℕ} (physical : Descriptor) (positive : physical.Positive)
    (hc : 0 < c) (stock : c ∣ physical.rows) (word : Fin (volume prime physical) → ZMod 2)
    (returned : Fin c → Fin (volume prime (role physical c)) → ZMod 2)
    (dest : ℤ → Fin (prime+4)) (sources : Fin c → ℤ → Fin (prime+4)) (p : ℤ) (origins : Fin c → ℤ) :
    let span := (volume_split prime c physical stock).symm
    let bs := bits (rowLength prime physical)
    let gs := bits (groups c physical)
    let tapes := fun j => putWord (sources j) (origins j) (List.ofFn fun z => SparseRoleCircuit.encode (returned j z))
    let output := transpose (one_dvd physical.rows) word
    (∀ g j k, returned j (roleIndex prime c physical g k) =
      word ((pack g (pack j (swapSuffix k))).cast span)) →
    HoareTime (CyclicRowNormalized.mergeProgram c prime)
      (· = CyclicRowSplit.bank (CyclicRowCopy.bank dest tapes p origins bs) gs)
      (· = CyclicRowSplit.bank (CyclicRowCopy.bank
        (putWord dest p (List.ofFn fun k => SparseRoleCircuit.encode (output k))) tapes
        p origins bs) gs)
      (149*volume prime physical) := by
  intro span bs gs tapes output reads
  let encoded := fun k => SparseRoleCircuit.encode (a := prime) (output k)
  have words j : roleArray prime c physical stock encoded j =
      fun z => SparseRoleCircuit.encode (a := prime) (returned j z) := by
    funext z
    obtain ⟨⟨g,k⟩,eq⟩ := finProdFinEquiv.surjective (z.cast (role_volume prime c physical))
    have hz : z = roleIndex prime c physical g k := Fin.ext (congrArg Fin.val eq).symm
    subst z
    simp only [roleArray,roleIndex,Fin.cast_cast,Fin.cast_refl,id_eq,pack,Equiv.symm_apply_apply,view,encoded,output]
    apply congrArg SparseRoleCircuit.encode
    rw [Shared50RecursiveChildPermutation.transpose_independent (by decide : 0 < 1) hc
      (one_dvd physical.rows) stock word]
    exact (transpose_entry stock word g j k).trans (reads g j k).symm
  have merge := RecursiveInterchangeRowsNormalized.merge_hoare prime c physical stock encoded dest sources p origins bs gs (bits_value _) (bits_value _)
  simp only [words] at merge
  exact merge.consequence (fun _ h => h) (fun _ h => h) (RecursiveInterchangeRowsNormalized.cost_linear prime c physical stock
    Shared50ModularControl.prime_prime.pos hc positive bs gs (bits_value _) (bits_value _)
    (bits_canonical _) (bits_canonical _))

open RecursiveInterchangeRows FlatCoordinateSchedule in
/-- The row-length and group-count descriptors suffice to construct the role
volume word on the product machine; its scratch returns blank. -/
theorem helperRoleVolume_runs (v : Descriptor) (positive : v.Positive) (c : ℕ) :
    let B := rowLength prime v
    let G := groups c v
    let V := volume prime (role v c)
    let output := DimensionProductDescriptor.output (q := prime) (bits B) (bits G) G B
    HoareTime (DimensionProductDescriptor.program (q := prime))
      (· = DimensionProductDescriptor.input (bits B) (bits G)) (· = output) (53*V+28) ∧
      output.head 1 = 1 ∧ output.tape 1 = RadixZeroFill.encodedBinary (bits V) := by
  intro B G V output
  have size : V = G*B := role_volume prime c v
  have rowPos : 0 < B := by
    obtain ⟨_,_,h,m,d⟩ := positive
    dsimp [B,rowLength]
    have := Shared50ModularControl.prime_prime.pos
    positivity
  refine ⟨size.symm ▸ DimensionProductDescriptor.construct_hoare _ _ G B rowPos
    (bits_value _) (bits_value _) (bits_canonical _) (bits_canonical _),rfl,?_⟩
  apply congrArg RadixZeroFill.encodedBinary
  exact BinaryCanonicalData.value_injective _ _ (DimensionProductDescriptor.bits_canonical _ _)
    (bits_canonical _) ((DimensionProductDescriptor.bits_value _ _).trans (size.symm.trans (bits_value _).symm))

/-- The cyclic splitter's outer counter counts groups. Supply the node's two
volume controls separately and reuse the split payload tapes in place. -/
theorem helperFan_of_splitRows {T c V : ℕ} (place : Fin (((1+c)+2)+2) ↪ Fin T)
    (fan : Fin (c+2) ↪ Fin T) (owner : ℤ → Fin (prime+4)) (data : Fin c → Fin V → ZMod 2)
    (bs gs : List Bool) (S : Stacks T prime)
    (atRole : ∀ j : Fin c, fan (j.castAdd 2) = place (((j.natAdd 1).castAdd 2).castAdd 2)) :
    let roles := fun j => putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encoded (a := prime) data j))
    let bank := CyclicRowSplit.bank (CyclicRowCopy.bank owner roles 0 (fun _ => 0) bs) gs
    let controls := CountedLoopReuseAlphabet.controls (a := prime) CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary (FlatCoordinateSchedule.bits V)) 1 1
    let controlPorts := (Fin.natAddEmb c (m := 2)).trans fan
    RepT bank (embStk place S).L (embStk place S).R →
    RepT controls (embStk controlPorts S).L (embStk controlPorts S).R → HelperFan fan data S := by
  intro roles bank controls controlPorts ready counters i z
  induction i using Fin.addCases with
  | left j =>
    simpa only [bank,roles,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
      CountedLoopReuseAlphabet.bank,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,
      embStk,Function.comp_apply,atRole] using ready (((j.natAdd 1).castAdd 2).castAdd 2) z
  | right j =>
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,controls,controlPorts,
      embStk,Function.comp_apply,Function.Embedding.trans_apply,Fin.natAddEmb_apply] using counters j z

/-- Replace the splitter's role and outer-clock ports by the returned fan.
The four remaining ports still refer to the caller's owner and descriptors. -/
theorem helperMergePlacement {T c : ℕ} (place : Fin (((1+c)+2)+2) ↪ Fin T)
    (fan : Fin (c+2) ↪ Fin T) :
    let role := fun j : Fin c => ((j.natAdd 1).castAdd 2).castAdd 2
    let clock := (0 : Fin 2).natAdd ((1+c)+2)
    let retained := fun i => (∀ j, i ≠ role j) ∧ i ≠ clock
    (∀ i, retained i → ∀ k, place i ≠ fan k) →
    ∃ mergePlace : Fin (((1+c)+2)+2) ↪ Fin T,
      (∀ j, fan (j.castAdd 2) = mergePlace (role j)) ∧
      fan ((0 : Fin 2).natAdd c) = mergePlace clock ∧
      ∀ i, retained i → mergePlace i = place i := by
  classical
  intro role clock retained apart
  let port i := if h : ∃ j, i = role j then fan (h.choose.castAdd 2)
    else if i = clock then fan ((0 : Fin 2).natAdd c) else place i
  have inj : Function.Injective role := by
    intro x y h
    have eq := congrArg Fin.val h
    apply Fin.ext
    change 1+x.val = 1+y.val at eq
    omega
  have different j : role j ≠ clock := by
    intro h
    have eq := congrArg Fin.val h
    change 1+j.val = 1+c+2+0 at eq
    omega
  have onRole j : port (role j) = fan (j.castAdd 2) := by
    have hit : ∃ k, role j = role k := ⟨j,rfl⟩
    simp only [port,dite_eq_left hit,← inj hit.choose_spec]
  have onClock : port clock = fan ((0 : Fin 2).natAdd c) := by
    simp [port,fun j => (different j).symm]
  have off i (h : retained i) : port i = place i := by
    simp [port,h.1,h.2]
  have parts i : (∃ j, i = role j) ∨ i = clock ∨ retained i := by
    by_cases h : ∃ j, i = role j
    · exact Or.inl h
    by_cases e : i = clock
    · exact Or.inr (Or.inl e)
    exact Or.inr (Or.inr ⟨fun j hj => h ⟨j,hj⟩,e⟩)
  refine ⟨⟨port,?_⟩,fun j => (onRole j).symm,onClock.symm,off⟩
  intro x y eq
  rcases parts x with ⟨j,rfl⟩ | rfl | hx <;> rcases parts y with ⟨k,rfl⟩ | rfl | hy
  all_goals try rw [off _ hx] at eq
  all_goals try rw [off _ hy] at eq
  all_goals simp only [onRole,onClock,fan.injective.eq_iff,
    place.injective.eq_iff,Fin.castAdd_inj] at eq
  all_goals try subst_vars
  all_goals try rfl
  all_goals try exact False.elim (apart _ hx _ eq)
  all_goals try exact False.elim (apart _ hy _ eq.symm)
  all_goals have hv := congrArg Fin.val eq; simp at hv; omega

/-- Recover the merge bank from the returned roles and their shared clock.
Only the owner, the inner controls and the group descriptor need a frame. -/
theorem splitRows_of_helperFan {T c V : ℕ} (place mergePlace : Fin (((1+c)+2)+2) ↪ Fin T)
    (fan : Fin (c+2) ↪ Fin T) (owner : ℤ → Fin (prime+4)) (input output : Fin c → Fin V → ZMod 2)
    (bs gs : List Bool) (S F : Stacks T prime)
    (atRole : ∀ j : Fin c, fan (j.castAdd 2) = mergePlace (((j.natAdd 1).castAdd 2).castAdd 2))
    (atClock : fan ((0 : Fin 2).natAdd c) = mergePlace ((0 : Fin 2).natAdd ((1+c)+2))) :
    let roles := fun data j => putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encoded (a := prime) data j))
    let bank := fun data => CyclicRowSplit.bank (CyclicRowCopy.bank owner (roles data) 0 (fun _ => 0) bs) gs
    RepT (bank input) (embStk place S).L (embStk place S).R → HelperFan fan output F →
    (∀ i, (∀ j : Fin c, i ≠ ((j.natAdd 1).castAdd 2).castAdd 2) →
      i ≠ (0 : Fin 2).natAdd ((1+c)+2) →
      F.L (mergePlace i) = S.L (place i) ∧ F.R (mergePlace i) = S.R (place i)) →
    RepT (bank output) (embStk mergePlace F).L (embStk mergePlace F).R := by
  intro roles bank ready returned frame i z
  by_cases payload : ∃ j : Fin c, i = ((j.natAdd 1).castAdd 2).castAdd 2
  · obtain ⟨j,rfl⟩ := payload
    simpa only [bank,roles,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
      CountedLoopReuseAlphabet.bank,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right,
      embStk,Function.comp_apply,atRole] using returned (j.castAdd 2) z
  by_cases clock : i = (0 : Fin 2).natAdd ((1+c)+2)
  · subst i
    simpa [bank,CyclicRowSplit.bank,CountedLoopReuseAlphabet.bank,PointwiseRoleGate.bank,Tapes.append,
      CountedLoopReuseAlphabet.controls,embStk,atClock] using returned ((0 : Fin 2).natAdd c) z
  obtain ⟨left,right⟩ := frame i (fun j h => payload ⟨j,h⟩) clock
  have old := ready i z
  simp only [embStk,Function.comp_apply,left,right]
  induction i using Fin.addCases
  case left i =>
    induction i using Fin.addCases
    case left i =>
      induction i using Fin.addCases
      case right j => exact (payload ⟨j,rfl⟩).elim
      case left j => simpa [bank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
        CountedLoopReuseAlphabet.bank,Tapes.append,embStk] using old
    case right j => simpa [bank,CyclicRowSplit.bank,CyclicRowCopy.bank,CountedLoopReuseAlphabet.bank,
      Tapes.append,embStk] using old
  case right j => simpa [bank,CyclicRowSplit.bank,CountedLoopReuseAlphabet.bank,Tapes.append,embStk] using old

/-- A child bank may share the live controls with the caller. Its returned
roles can still feed the merge directly, keeping the caller's other tapes. -/
theorem inheritedChildMerge {c T N H : ℕ} (place : Fin (((1+c)+2)+2) ↪ Fin T)
    (caller : Fin T ↪ Fin H) (bank : Fin N ↪ Fin H) (live : Fin (c+2) ↪ Fin T)
    (returned : Fin (c+2) ↪ Fin N)
    (clockPort : live ((0 : Fin 2).natAdd c) = place ((0 : Fin 2).natAdd ((1+c)+2)))
    (volumeFresh : ∀ i, place i ≠ live ((1 : Fin 2).natAdd c))
    (apart : ∀ t, (∀ j : Fin 2, live (j.natAdd c) ≠ t) → ∀ k, bank k ≠ caller t) :
    let fan := returned.trans bank
    ∃ mergePlace : Fin (((1+c)+2)+2) ↪ Fin H, mergePlace 0 = caller (place 0) ∧
      ∀ {V : ℕ} (owner : ℤ → Fin (prime+4)) (input output : Fin c → Fin V → ZMod 2)
        (bs gs : List Bool) (S F : Stacks H prime),
      let roles := fun data j => putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encoded (a := prime) data j))
      let rows := fun data => CyclicRowSplit.bank (CyclicRowCopy.bank owner (roles data) 0 (fun _ => 0) bs) gs
      RepT (rows input) (embStk (place.trans caller) S).L (embStk (place.trans caller) S).R →
      HelperFan fan output F →
      (∀ t, (∀ j : Fin 2, live (j.natAdd c) ≠ t) →
        F.L (caller t) = S.L (caller t) ∧ F.R (caller t) = S.R (caller t)) →
      RepT (rows output) (embStk mergePlace F).L (embStk mergePlace F).R := by
  intro fan
  let clock := (0 : Fin 2).natAdd ((1+c)+2)
  have off i (other : i ≠ clock) (j : Fin 2) : live (j.natAdd c) ≠ place i := by
    fin_cases j
    · change live ((0 : Fin 2).natAdd c) ≠ place i
      rw [clockPort]
      exact place.injective.ne other.symm
    · exact (volumeFresh i).symm
  obtain ⟨mergePlace,atRole,atClock,kept⟩ :=
    helperMergePlacement (place.trans caller) fan (fun i hi k => (apart _ (off i hi.2) (returned k)).symm)
  refine ⟨mergePlace,kept 0 ⟨?_,?_⟩,?_⟩
  · intro j h
    have eq := congrArg Fin.val h
    change 0 = 1+j.val at eq
    omega
  · intro h
    have eq := congrArg Fin.val h
    change 0 = 1+c+2+0 at eq
    omega
  intro V owner input output bs gs S F roles rows ready result frame
  apply splitRows_of_helperFan (place.trans caller) mergePlace fan owner input output bs gs S F
    atRole atClock ready result
  intro i outside other
  rw [kept i ⟨outside,other⟩]
  exact frame (place i) (off i other)

private theorem helperRows_place {P U : Type} {t T q Q bound : ℕ} (body : P → Pr P T Q prime U)
    (place : Fin t ↪ Fin T) (machine : Program t q prime) (capacity : q ≤ Q) {input output}
    (run : HoareTime machine (· = input) (· = output) bound) (u : HS T Q prime U) (S : Stacks T prime)
    (ready : RepT input (embStk place S).L (embStk place S).R) :
    ∃ z F n, Exec body (embProg place Empty.elim (foreign (liftQ machine capacity))) (mk u S) n (mk z F) ∧
      n ≤ bound*(t+5)+6 ∧ z.user = u.user ∧ RepT output (embStk place F).L (embStk place F).R ∧
      ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨v,D,_,rfl,out,user,_,_,_,n,cost,ran⟩ := foreign_exec (body := (Empty.elim : Empty → _))
    (liftQ machine capacity) (HoareTime.liftQ capacity run) (embDn place u) (embStk place S) input rfl ready
  obtain ⟨z,F,exec,_,same,view,keep⟩ := exec_emb (body' := body) (ι := Empty.elim)
    place.injective (fun e => nomatch e) ran u rfl S rfl
  exact ⟨z,F,n,exec,cost,same.trans user,view.symm ▸ out,keep⟩

open RecursiveInterchangeRows FlatCoordinateSchedule in
/-- Build the volume descriptor directly on the fan's header tape. The split
role tapes and the marked clock are retained throughout the computation. -/
theorem helperFanVolume_exec {P U : Type} {T Q c : ℕ} (body : P → Pr P T Q prime U)
    (place : Fin (((1+c)+2)+2) ↪ Fin T) (fan : Fin (c+2) ↪ Fin T) (product : Fin 6 ↪ Fin T)
    (v : Descriptor) (positive : v.Positive) (capacity : 40 ≤ Q)
    (atRole : ∀ j : Fin c, fan (j.castAdd 2) = place (((j.natAdd 1).castAdd 2).castAdd 2))
    (atRow : product 3 = place (((1 : Fin 2).natAdd (1+c)).castAdd 2))
    (atGroups : product 5 = place ((1 : Fin 2).natAdd ((1+c)+2)))
    (atClock : fan ((0 : Fin 2).natAdd c) = place ((0 : Fin 2).natAdd ((1+c)+2)))
    (atVolume : fan ((1 : Fin 2).natAdd c) = product 1)
    (volumeFresh : ∀ i, place i ≠ product 1) :
    let B := rowLength prime v
    let G := groups c v
    let V := volume prime (role v c)
    let code := embProg product Empty.elim (foreign (liftQ (DimensionProductDescriptor.program (q := prime)) capacity))
    ∀ (owner : ℤ → Fin (prime+4)) (data : Fin c → Fin V → ZMod 2) u S,
    let roles := fun j => putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encoded (a := prime) data j))
    let bank := CyclicRowSplit.bank (CyclicRowCopy.bank owner roles 0 (fun _ => 0) (bits B)) (bits G)
    RepT bank (embStk place S).L (embStk place S).R →
    (∀ k : Fin 6, k ≠ 3 → k ≠ 5 → S.L (product k) = [] ∧ S.R (product k) = []) →
    ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ n ≤ (53*V+28)*11+6 ∧ z.user = u.user ∧
      HelperFan fan data F ∧ RepT bank (embStk place F).L (embStk place F).R ∧
      ∀ j, (∀ k, product k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro B G V code owner data u S roles bank split free
  have row := split (((1 : Fin 2).natAdd (1+c)).castAdd 2)
  have groupsReady := split ((1 : Fin 2).natAdd ((1+c)+2))
  simp only [bank,CyclicRowSplit.bank,CyclicRowCopy.bank,CountedLoopReuseAlphabet.bank,
    Tapes.append,Fin.addCases_left,Fin.addCases_right,CountedLoopReuseAlphabet.controls,
    embStk,Function.comp_apply] at row groupsReady
  have encoding : RadixZeroFill.encodedBinary (q := prime) = CountedLoopReuseAlphabet.binary :=
    funext (fun bs => CountedLoopReuseAlphabet.encoding_binary bs)
  have input : RepT (DimensionProductDescriptor.input (bits B) (bits G))
      (embStk product S).L (embStk product S).R := by
    intro k z
    by_cases hr : k = 3
    · subst k
      simpa [DimensionProductDescriptor.input,embStk,atRow,encoding] using row z
    by_cases hg : k = 5
    · subst k
      simpa [DimensionProductDescriptor.input,embStk,atGroups,encoding] using groupsReady z
    obtain ⟨left,right⟩ := free k hr hg
    fin_cases k <;> simp_all [DimensionProductDescriptor.input,embStk,readAt]
  obtain ⟨construct,head,tape⟩ := helperRoleVolume_runs v positive c
  obtain ⟨z,F,n,run,cost,user,out,frame⟩ := helperRows_place body product _ capacity construct u S input
  have retained : RepT bank (embStk place F).L (embStk place F).R := by
    intro i a
    have old := split i a
    change bank.tape i a = readAt blank (F.L (place i)) (F.R (place i)) (a-bank.head i)
    by_cases shared : ∃ k, product k = place i
    · obtain ⟨k,hk⟩ := shared
      have other : k ≠ 1 := fun h => volumeFresh i (h ▸ hk.symm)
      let src := DimensionProductDescriptor.input (q := prime) (bits B) (bits G)
      let dst := DimensionProductDescriptor.output (q := prime) (bits B) (bits G) G B
      have heads : dst.head k = src.head k := by fin_cases k <;> first | rfl | exact (other rfl).elim
      have cells : dst.tape k = src.tape k := by fin_cases k <;> first | rfl | exact (other rfl).elim
      let d := a-bank.head i
      have before := input k (d+src.head k)
      have after := out k (d+src.head k)
      change dst.tape k _ = readAt blank (F.L (product k)) (F.R (product k)) (_-dst.head k) at after
      change src.tape k _ = readAt blank (S.L (product k)) (S.R (product k)) (_-src.head k) at before
      rw [heads,cells,hk,add_sub_cancel_right] at after
      rw [hk,add_sub_cancel_right] at before
      exact old.trans (before.symm.trans after)
    · obtain ⟨left,right⟩ := frame _ (fun k h => shared ⟨k,h⟩)
      rw [left,right]
      exact old
  refine ⟨z,F,n,run,cost,user,?_,retained,frame⟩
  apply helperFan_of_splitRows place fan owner data (bits B) (bits G) F atRole retained
  intro j a
  fin_cases j
  · have marked := retained ((0 : Fin 2).natAdd ((1+c)+2)) a
    simpa [bank,CyclicRowSplit.bank,CountedLoopReuseAlphabet.bank,Tapes.append,
      embStk,CountedLoopReuseAlphabet.controls,atClock] using marked
  · have h := out 1 a
    rw [head,tape,encoding] at h
    simpa [embStk,CountedLoopReuseAlphabet.controls,atVolume,V] using h

open RecursiveInterchangeRows FlatCoordinateSchedule in
/-- Prepare the volume controls, run the role worker and return the split bank
with its new payloads in the form consumed by the merge. -/
theorem helperFanWorker_exec {P U : Type} {T Q c : ℕ} (body : P → Pr P T Q prime U)
    (worker : Pr P T Q prime U) (budget : ℕ) (framed : Fin T → Prop)
    (place mergePlace : Fin (((1+c)+2)+2) ↪ Fin T) (fan returnedFan : Fin (c+2) ↪ Fin T) (product : Fin 6 ↪ Fin T)
    (v : Descriptor) (positive : v.Positive) (capacity : 40 ≤ Q)
    (atRole : ∀ j : Fin c, fan (j.castAdd 2) = place (((j.natAdd 1).castAdd 2).castAdd 2))
    (returnedRole : ∀ j : Fin c, returnedFan (j.castAdd 2) = mergePlace (((j.natAdd 1).castAdd 2).castAdd 2))
    (returnedClock : returnedFan ((0 : Fin 2).natAdd c) = mergePlace ((0 : Fin 2).natAdd ((1+c)+2)))
    (atRow : product 3 = place (((1 : Fin 2).natAdd (1+c)).castAdd 2))
    (atGroups : product 5 = place ((1 : Fin 2).natAdd ((1+c)+2)))
    (atClock : fan ((0 : Fin 2).natAdd c) = place ((0 : Fin 2).natAdd ((1+c)+2)))
    (atVolume : fan ((1 : Fin 2).natAdd c) = product 1)
    (volumeFresh : ∀ i, place i ≠ product 1) :
    let B := rowLength prime v
    let G := groups c v
    let V := volume prime (role v c)
    let code := embProg product Empty.elim (foreign (liftQ (DimensionProductDescriptor.program (q := prime)) capacity))
    ∀ (owner : ℤ → Fin (prime+4)) (input output : Fin c → Fin V → ZMod 2) u S,
    let roles := fun data j => putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encoded (a := prime) data j))
    let bank := fun data => CyclicRowSplit.bank (CyclicRowCopy.bank owner (roles data) 0 (fun _ => 0) (bits B)) (bits G)
    RepT (bank input) (embStk place S).L (embStk place S).R →
    (∀ k : Fin 6, k ≠ 3 → k ≠ 5 → S.L (product k) = [] ∧ S.R (product k) = []) →
    (∀ j, framed j → ∀ k, product k ≠ j) →
    (∀ x D, HelperFan fan input D →
      (∀ j, (∀ k, product k ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
      ∃ y F m, Exec body worker (mk x D) m (mk y F) ∧ m ≤ budget ∧ y.user = x.user ∧
        HelperFan returnedFan output F ∧
        (∀ i, (∀ j : Fin c, i ≠ ((j.natAdd 1).castAdd 2).castAdd 2) →
          i ≠ (0 : Fin 2).natAdd ((1+c)+2) →
          F.L (mergePlace i) = D.L (place i) ∧ F.R (mergePlace i) = D.R (place i)) ∧
        ∀ j, framed j → F.L j = D.L j ∧ F.R j = D.R j) →
    ∃ y F n, Exec body (code.seq worker) (mk u S) n (mk y F) ∧ n ≤ (53*V+28)*11+6+budget ∧
      y.user = u.user ∧ RepT (bank output) (embStk mergePlace F).L (embStk mergePlace F).R ∧
      ∀ j, framed j → F.L j = S.L j ∧ F.R j = S.R j := by
  intro B G V code owner input output u S roles bank ready free outside work
  obtain ⟨x,D,k,setup,paid,xu,fanReady,retained,preserved⟩ :=
    helperFanVolume_exec body place fan product v positive capacity atRole atRow atGroups atClock
      atVolume volumeFresh owner input u S ready free
  obtain ⟨y,F,m,run,cost,yx,returned,headers,frame⟩ := work x D fanReady preserved
  refine ⟨y,F,_,setup.seq run,Nat.add_le_add paid cost,yx.trans xu,?_,?_⟩
  · exact splitRows_of_helperFan place mergePlace returnedFan owner input output (bits B) (bits G) D F
      returnedRole returnedClock retained returned headers
  · intro j hj
    obtain ⟨left,right⟩ := preserved j (outside j hj)
    exact ⟨(frame j hj).1.trans left,(frame j hj).2.trans right⟩

open RecursiveInterchangeRows Shared50RecursiveNodeRows FlatCoordinateSchedule in
/-- Run the role computation between a normalized split and merge. The merge can read the
worker's returned role tapes directly, even when its input and output banks differ. -/
theorem helperRows_exec {P U : Type} {c T Q : ℕ} (physical : Descriptor) (positive : physical.Positive)
    (hc : 0 < c) (stock : c ∣ physical.rows) (word : Fin (volume prime physical) → ZMod 2)
    (dest : ℤ → Fin (prime+4)) (sources : Fin c → ℤ → Fin (prime+4)) (p : ℤ) (origins : Fin c → ℤ)
    (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U) (budget : ℕ)
    (place mergePlace : Fin (((1+c)+2)+2) ↪ Fin T) (framed : Fin T → Prop)
    (outside : ∀ j, framed j → ∀ i, place i ≠ j)
    (outsideMerge : ∀ j, framed j → ∀ i, mergePlace i ≠ j)
    (capacity : let q := 7+(CyclicRowCycle.states c+5)+4; q+q ≤ Q) :
    let V := volume prime physical
    let bs := bits (rowLength prime physical)
    let gs := bits (groups c physical)
    let bank := fun owner roles => CyclicRowSplit.bank (CyclicRowCopy.bank owner roles p origins bs) gs
    let encoded := fun k => SparseRoleCircuit.encode (a := prime) (word k)
    let owner := putWord dest p (List.ofFn encoded)
    let tapes := fun (data : Fin c → Fin (volume prime (role physical c)) → ZMod 2) j =>
      putWord (sources j) (origins j) (List.ofFn fun k => SparseRoleCircuit.encode (data j k))
    let input := fun (j : Fin c) (z : Fin (volume prime (role physical c))) =>
      let gk := finProdFinEquiv.symm (z.cast (role_volume prime c physical))
      word ((pack gk.1 (pack j gk.2)).cast (volume_split prime c physical stock).symm)
    let returned := fun j => transpose (one_dvd (role physical c).rows) (input j)
    let project := fun (D : Stacks T prime) => embStk place D
    let splitCode := embProg place Empty.elim (foreign (liftQ (CyclicRowNormalized.splitProgram c prime) capacity))
    let mergeCode := embProg mergePlace Empty.elim (foreign (liftQ (CyclicRowNormalized.mergeProgram c prime) capacity))
    ∀ u S, RepT (bank owner sources) (project S).L (project S).R →
      (∀ v D, RepT (bank owner (tapes input)) (project D).L (project D).R →
        (∀ j, (∀ i, place i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ z F n, Exec body worker (mk v D) n (mk z F) ∧ n ≤ budget ∧ z.user = v.user ∧
          RepT (bank owner (tapes returned)) (embStk mergePlace F).L (embStk mergePlace F).R ∧
          ∀ j, framed j → F.L j = D.L j ∧ F.R j = D.R j) →
      ∃ z F n, Exec body (splitCode.seq (worker.seq mergeCode)) (mk u S) n (mk z F) ∧
        n ≤ 298*V*((((1+c)+2)+2)+5)+budget+12 ∧ z.user = u.user ∧
        RepT (bank (putWord owner p (List.ofFn fun k =>
          SparseRoleCircuit.encode (transpose (one_dvd physical.rows) word k))) (tapes returned))
          (embStk mergePlace F).L (embStk mergePlace F).R ∧
        ∀ j, framed j → F.L j = S.L j ∧ F.R j = S.R j := by
  intro V bs gs bank encoded owner tapes input returned project splitCode mergeCode u S ready work
  have reads g j k : returned j (roleIndex prime c physical g k) =
      word ((pack g (pack j (swapSuffix k))).cast (volume_split prime c physical stock).symm) := by
    change transpose (one_dvd (role physical c).rows) (input j) _ = _
    rw [transpose_roleIndex]
    simp only [input,roleIndex,Fin.cast_cast,Fin.cast_refl,id_eq,pack,Equiv.symm_apply_apply]
  have split := RecursiveInterchangeRowsNormalized.split_hoare prime c physical stock encoded dest sources p origins
    bs gs (bits_value _) (bits_value _)
  have paid := RecursiveInterchangeRowsNormalized.cost_linear prime c physical stock Shared50ModularControl.prime_prime.pos
    hc positive bs gs (bits_value _) (bits_value _) (bits_canonical _) (bits_canonical _)
  have start := split.consequence (fun _ h => h) (fun _ h => h) paid
  have merge := helperRoleMerge_runs physical positive hc stock word returned owner sources p origins reads
  obtain ⟨v,D,k,splitRun,splitCost,vu,prepared,frame⟩ :=
    helperRows_place body place _ capacity start u S ready
  obtain ⟨y,G,m,mid,midCost,yv,changed,midFrame⟩ := work v D prepared frame
  obtain ⟨z,F,n,merged,mergeCost,zy,out,lastFrame⟩ :=
    helperRows_place body mergePlace _ capacity merge y G changed
  refine ⟨z,F,_,splitRun.seq (mid.seq merged),?_,zy.trans (yv.trans vu),out,?_⟩
  · dsimp only [V]
    rw [show 298*volume prime physical = 149*volume prime physical+149*volume prime physical by omega,Nat.add_mul]
    omega
  · intro j hj
    obtain ⟨l,r⟩ := frame j (outside j hj)
    obtain ⟨ml,mr⟩ := midFrame j hj
    obtain ⟨fl,fr⟩ := lastFrame j (outsideMerge j hj)
    exact ⟨fl.trans (ml.trans l),fr.trans (mr.trans r)⟩

/-- An implementation transposing the physical interval on the record supplies the
scheduled worker contract at every address map preserving the two active fields. -/
theorem scheduledChildExec_of_inherited [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (f : P) (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (record : List (Fin (prime+4))) (parent child physical : Descriptor) (w W budget : ℕ)
    (size : volume prime physical = (prime^(w+1))^16*W)
    (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W))
    (coords : InheritedIntervalPositions child physical size position) (width : physical.width = child.width) :
    let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) (scheduledRecordPorts ports)
      (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
    let clean := fun (S : Stacks T prime) => ∀ j : Fin (rowSwapBlock.tapes+35), 35 ≤ j.val →
      S.L (ports j) = [] ∧ S.R (ports j) = []
    (child.width < parent.width → ∀ u S word, stored word S → clean S →
      ∃ z F n, Exec body (body f) (mk u S) n (mk z F) ∧ n ≤ budget ∧ z.user = u.user ∧
        stored (fun k => Shared50RecursiveNodeRows.transpose (one_dvd physical.rows)
          (fun j => word (j.cast size)) (k.cast size.symm)) F ∧ clean F ∧
        ∀ j, (∀ l, ports l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) →
    ScheduledChildExec parent child w W ports record position body f budget := by
  intro stored clean physicalRun smaller u S word ready free
  obtain ⟨z,F,n,ran,paid,user,out,blank,frame⟩ := physicalRun smaller u S word ready free
  exact ⟨z,F,n,_,ran,paid,user,out,blank,frame,(coords.transpose_iff width word _).2 rfl⟩

open Certificates.PR589 in
/-- A paid helper MOVE calls the scheduled worker with its record, restores its scratch,
and preserves the stacks outside the worker ports. -/
theorem helperRecordCall_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U)
    (f : Fin nodeChildren5.length → P) (budget : Fin nodeChildren5.length → ℕ)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (record : List (Fin (prime+4)))
    (parent : Descriptor) (stage : Fin 9) (run : Fin 32 × Fin 5) (helper : Fin 439)
    (w : ℕ) (width : parent.width = 64*(w+1)) :
    let edges := Geometry.Moves.phaseEdges.filter fun p => Geometry.moveRank p.1 p.2 != 0
    ∀ j : Fin edges.length, let edge := edges[j.val]
      let a := Geometry.Dimensions.value edge.1
      let d := Geometry.Dimensions.value edge.2
      let lo := min a d
      let hi := max a d
      let start := (helperPosition (stage,helper)).val
      let physical := inheritedInterval (role parent 142080) ((start+lo)*(w+1)) ((hi-lo)*(w+1)) ((64-(start+hi))*(w+1))
      let i := phaseChildPositions.choose (stage,run,j)
      let child := scheduledChild prime parent i
      let W := (prime^(w+1))^112 * CopyChildLayout.spectators (role parent 142080)
      ∃ size : volume prime physical = (prime^(w+1))^16*W,
        let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) (scheduledRecordPorts ports)
          (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
        let clean := fun (S : Stacks T prime) => ∀ j : Fin (rowSwapBlock.tapes+35), 35 ≤ j.val →
          S.L (ports j) = [] ∧ S.R (ports j) = []
        ∃ position, InheritedIntervalPositions child physical size position ∧
          (ScheduledChildExec parent child w W ports record position body (f i) (budget i) →
          ∀ u S word, stored word S → clean S →
          ∃ z F n, Exec body (.call (f i)) (mk u S) n (mk z F) ∧ n ≤ budget i+2 ∧ z.user = u.user ∧
            stored (fun k => Shared50RecursiveNodeRows.transpose (one_dvd physical.rows)
              (fun j => word (j.cast size)) (k.cast size.symm)) F ∧ clean F ∧
            ∀ j, (∀ l, ports l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) := by
  intro edges j edge a d lo hi start physical i child W
  have shape := helperMove_shape parent stage run helper (w+1) width j
  have mem := List.mem_filter.mp (List.getElem_mem (l := edges) (n := j.val) j.isLt)
  have bounds := phaseInterval_bounds (Geometry.Moves.phase_checked edge mem.1)
    (Nat.pos_of_ne_zero (bne_iff_ne.mp mem.2))
  have ordered : lo ≤ hi := bounds.1.le
  have fits : hi ≤ 8 := bounds.2
  have lower : start < 56 := (helperPosition (stage,helper)).isLt
  have split : (role parent 142080).width = (start+lo)*(w+1)+(hi-lo)*(w+1)+(64-(start+hi))*(w+1) := by
    rw [← Nat.add_mul,← Nat.add_mul]
    change parent.width = _
    rw [width]
    congr 1
    omega
  have size : volume prime physical = (prime^(w+1))^16*W := by
    rw [inheritedInterval_volume _ _ _ _ split]
    simp only [volume,role,CopyChildLayout.spectators,W,width,Nat.mul_comm 64 (w+1),pow_mul]
    ring
  refine ⟨size,?_⟩
  intro stored clean
  obtain ⟨e,coords,transpose⟩ := scheduledTranspose_onOwner shape
  let position := e.trans (finCongr size)
  refine ⟨position,?_,?_⟩
  · intro k
    change _ = (CopyChildLayout.packActive physical (((e k).cast size).cast size.symm)).val
    simp only [Fin.cast_cast,Fin.cast_refl,id_eq]
    exact (coords k).symm
  intro worker u S word ready free
  have smaller : child.width < parent.width := by
    simpa only [child,scheduledChild,rankDescriptor,width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
      using Nat.mul_lt_mul_of_pos_right ((nodeChildren5_le i).trans_lt (by decide : 42 < 64)) (Nat.succ_pos w)
  obtain ⟨z,F,n,y,run,cost,user,out,blank,frame,reads⟩ := worker smaller u S word ready free
  refine ⟨z,F,_,Exec.call run,by omega,user,?_,blank,frame⟩
  convert out using 1
  funext k
  obtain ⟨h,rfl⟩ := position.surjective k
  exact ((reads h).trans (congrFun (transpose (fun j => word (j.cast size))) h)).symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
