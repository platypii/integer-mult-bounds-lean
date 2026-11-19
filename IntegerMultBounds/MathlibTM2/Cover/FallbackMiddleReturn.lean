module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackMiddleShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackDimension
public import IntegerMultBounds.MathlibTM2.Cover.LabelExchange
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout
public import IntegerMultBounds.Machine.BlockNegationData
import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

/-! Install the row descriptor, shear the payload and return it to its original port. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable {T A P M G B : ℕ} {U F : Type}

def middleWork : Fin 30 ↪ Fin 31 := Fin.castLEEmb (by decide)
def middleDescriptorPorts : Fin 11 ↪ Fin 31 := ⟨![28,2,29,4,30,5,6,7,8,9,10],by decide⟩
def middleReturnPorts : Fin 8 ↪ Fin 31 := ⟨![23,22,17,18,19,20,14,30],by decide⟩

def returnedMiddleShear (r : Fin 31 ↪ Fin T) : Pr F T 217 A U :=
  .seq (middleRowDescriptor (middleDescriptorPorts.trans r))
    (middleShearAndReturn (middleWork.trans r) (middleReturnPorts.trans r))

theorem returnedMiddleShear_exec (body : F → Pr F T 217 A U) (r : Fin 31 ↪ Fin T)
    (w c : ℕ) (radix : M = prime^(w+1)) (hc : c < M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin ((P*M*G)*(M*B)) → Fin 4)
    (bs ms : List Bool) (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (v : HS T 217 A U) (S : Stacks T A)
    (heads : S.R (r 28) = binSyms P.size P) (ticks : S.R (r 29) = binSyms G.size G)
    (free : ∀ i : Fin 30, 24 ≤ i → i ≤ 27 → S.R (r (middleWork i)) = [])
    (ready : MiddleGroupReady middleArithmetic M.size c 0 M (embStk (middleWork.trans r) S))
    (marker : S.L (r 30) = [separator]) (fresh : S.R (r 30) = [])
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (TranslationExecutionReuse.bank (putWord source p (List.ofFn word)) dest p q bs ms []))
      (S.L ∘ r ∘ middleWork ∘ middleTranslation) (S.R ∘ r ∘ middleWork ∘ middleTranslation))
    (empty : ∀ z, q ≤ z → z < q+((P*M*G)*(M*B) : ℕ) → dest z = blank) :
    let N := (P*M*G)*(M*B)
    let out := FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)
    ∃ z D n, z.user = v.user ∧ n ≤ (210*(2*(Nat.size prime+1)^2)+16120)*N ∧
      Exec body (returnedMiddleShear r) (mk v S) n (mk z D) ∧
      (∀ x, readAt blank (D.L (r 22)) (D.R (r 22)) (x-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p out x)) ∧
      ∀ x, readAt blank (D.L (r 23)) (D.R (r 23)) (x-q) = RadixToBinary.binaryEncoding.encode (dest x) := by
  intro N out
  have hM : 0 < M := radix ▸ pow_pos prime_prime.pos _
  obtain ⟨ps,u,n,cp,hp,hu,hn,setup⟩ := middleRowDescriptor_exec body (middleDescriptorPorts.trans r)
    P M G hP hM hG v S heads ready.2.2.1 ticks (by
      intro i lo hi
      fin_cases i <;> first
        | contradiction | exact fresh | exact ready.2.2.2.1 4 (by decide) (by decide)
        | exact ready.2.2.2.1 5 (by decide) (by decide) | exact ready.2.2.2.1 6 (by decide) (by decide)
        | exact ready.2.2.2.1 7 (by decide) (by decide) | exact ready.2.2.2.1 8 (by decide) (by decide)
        | exact ready.2.2.2.1 9 (by decide) (by decide))
  let E : Stacks T A := {S with R := Function.update S.R (r 30) (ps.map bitSymbol)}
  have keep (i : Fin 30) : E.R (r (middleWork i)) = S.R (r (middleWork i)) :=
    Function.update_of_ne (r.injective.ne ((by decide : ∀ j, middleWork j ≠ 30) i)) _ _
  have eq : embStk (middleWork.trans r) E = embStk (middleWork.trans r) S :=
    Stacks.ext rfl rfl rfl (funext keep)
  obtain ⟨z,D,m,hz,ht,run,tapes⟩ := middleShearAndReturn_exec body (middleWork.trans r)
    (middleReturnPorts.trans r) (fun i => congrArg r ((by decide : ∀ i : Fin 7,
      middleReturnPorts i.castSucc = middleWork (middleTranslation (![11,10,4,5,6,7,1] i))) i))
    (fun i => r.injective.ne ((by decide : ∀ j, middleWork j ≠ middleReturnPorts 7) i))
    w c radix hc hP hG hB source dest p q word bs ms ps hb hm hp cb cm cp u E
    ((keep 28).trans heads) ((keep 29).trans ticks) (fun i lo hi => (keep i).trans (free i lo hi))
    (eq ▸ ready) (by intro i x; exact (rep i x).trans (by simp only [Function.comp_apply,Function.Embedding.trans_apply,keep]; rfl))
    (by intro x
        change _ = readAt blank (S.L (r 30)) (Function.update S.R (r 30) _ (r 30)) _
        simp only [marker,Function.update_self,readAt_single]
        rw [← CountedLoopReuseAlphabet.encoding_binary]
        exact congrFun (encodedBinary_eq ps) x) empty
  change m ≤ (210*(2*(Nat.size prime+1)^2)+15688)*N at ht
  have rows : P*M*G ≤ N := Nat.le_mul_of_pos_right _ (Nat.mul_pos hM hB)
  exact ⟨z,D,n+m,hz.trans hu,by nlinarith only [hn,ht,rows],Exec.seq setup run,
    fun x => (tapes 1 x).symm,fun x => (tapes 0 x).symm⟩

/-- At a leaf descriptor's physical address, the returned word adds the
weighted head digit to the tail digit while retaining every spectator. -/
theorem middleShear_leaf_entry {α : Type*} (v : RecursiveInterchangeLayout.Descriptor) (q : ℕ)
    [NeZero M] (radix : q^v.width = M) (c h t : ZMod M)
    (a : Fin v.beforeRows) (row : Fin v.rows) (pre : Fin v.beforeH)
    (mid : Fin v.between) (post : Fin v.afterD)
    (word : Fin ((((v.beforeRows*v.rows*v.beforeH)*M)*v.between)*(M*v.afterD)) → α) :
    let out := FiberLayoutData.translated word (fun i => c.val*(i.val/v.between%M)%M)
    out[RecursiveInterchangeLayout.index q v a row pre h.val mid (t+c*h).val post]? =
      (List.ofFn word)[RecursiveInterchangeLayout.index q v a row pre h.val mid t.val post]? := by
  intro out
  let prefixRow := finProdFinEquiv (finProdFinEquiv (a,row),pre)
  let h' : Fin M := ⟨h.val,h.val_lt⟩
  let t' : Fin M := ⟨t.val,t.val_lt⟩
  let src := FiberLayoutData.index (finProdFinEquiv (finProdFinEquiv (prefixRow,h'),mid)) t' post
  have addr : RecursiveInterchangeLayout.index q v a row pre h.val mid t.val post = src.val := by
    simp [RecursiveInterchangeLayout.index,src,prefixRow,h',t',finProdFinEquiv,radix]
    ring
  rw [addr,List.getElem?_eq_getElem (l := List.ofFn word) (by simp : src.val < (List.ofFn word).length),List.getElem_ofFn]
  let fiber := finProdFinEquiv (finProdFinEquiv (prefixRow,h'),mid)
  have control : fiber.val/v.between%M = h.val := by
    simp [fiber,finProdFinEquiv,Nat.add_mul_div_left,Nat.div_eq_of_lt mid.isLt,
      Nat.zero_lt_of_lt mid.isLt,Nat.mod_eq_of_lt h.val_lt,h']
  have step := FiberLayoutData.translated_entry word
    (fun i => c.val*(i.val/v.between%M)%M) fiber t' post
  simp only [control,Nat.add_mod_mod] at step
  have digit : (t+c*h).val = (t.val+c.val*h.val)%M := by
    simp [ZMod.val_add,ZMod.val_mul,Nat.add_mod_mod]
  have target : RecursiveInterchangeLayout.index q v a row pre h.val mid (t+c*h).val post =
      (finProdFinEquiv (finProdFinEquiv (prefixRow,h'),mid)).val*(M*v.afterD) +
        ((t'.val+c.val*h'.val)%M)*v.afterD+post.val := by
    simp [RecursiveInterchangeLayout.index,radix,digit,prefixRow,h',t',finProdFinEquiv]
    ring
  rw [target]
  exact step

/-- On the parent word the same shear updates just the reversed tail
partner of the selected rank coordinate. -/
theorem middleShear_rank_entry {α : Type*} {r : ℕ} (v : RecursiveInterchangeLayout.Descriptor) (width : v.width = r)
    [NeZero M] (q w : ℕ) (radix : M = q^w) (i : Fin r) (c : ZMod M)
    (x y : Fin r → ZMod M) (a : Fin v.beforeRows) (row : Fin v.rows)
    (before : Fin v.beforeH) (middle : Fin v.between) (after : Fin v.afterD) :
    let view := {(RecursiveInterchangeLayout.child M 1 1 v i i.rev) with width := w}
    ∀ word : Fin ((((view.beforeRows*view.rows*view.beforeH)*M)*view.between)*(M*view.afterD)) → α,
      let out := FiberLayoutData.translated word (fun j => c.val*(j.val/view.between%M)%M)
      out[RecursiveInterchangeLayout.index M v a row before (FlatCoordinateLayout.rank x).val middle
        (FlatCoordinateLayout.rank (Function.update y i.rev (y i.rev+c*x i))).val after]? =
      (List.ofFn word)[RecursiveInterchangeLayout.index M v a row before (FlatCoordinateLayout.rank x).val
        middle (FlatCoordinateLayout.rank y).val after]? := by
  intro view word out
  have step := leafPair_apply v width q w radix i (fun p => (p.1,p.2+c*p.1))
    (fun j => (List.ofFn word)[j]?) (fun j => out[j]?) x y a row before middle after
    before.isLt middle.isLt after.isLt (by
      intro pre hp mid hm post he h t
      exact middleShear_leaf_entry view q radix.symm c h t a
        ⟨row.val,by simp [view,RecursiveInterchangeLayout.child]⟩
        ⟨pre,hp⟩ ⟨mid,hm⟩ ⟨post,he⟩ word)
  simpa using step

/-- The two ordinary exchanges and the sign correction connect the three
translated words at the same physical leaf descriptor. -/
theorem middleShears_weighted_entry {α : Type*} (v : RecursiveInterchangeLayout.Descriptor) (q : ℕ)
    [NeZero M] (radix : q^v.width = M) (weight inv : ZMod M) (unit : weight*inv = 1)
    (a : Fin v.beforeRows) (row : Fin v.rows) (pre : Fin v.beforeH)
    (mid : Fin v.between) (post : Fin v.afterD) :
    let N := (((v.beforeRows*v.rows*v.beforeH)*M)*v.between)*(M*v.afterD)
    let pos := fun p : ZMod M × ZMod M =>
      RecursiveInterchangeLayout.index q v a row pre p.1.val mid p.2.val post
    let shifted := fun (c : ZMod M) (word : Fin N → α) =>
      FiberLayoutData.translated word (fun i => c.val*(i.val/v.between%M)%M)
    ∀ (input swapped swappedBack : Fin N → α) (output : List α),
      (∀ p, (List.ofFn swapped)[pos p.swap]? = (shifted inv input)[pos p]?) →
      (∀ p, (List.ofFn swappedBack)[pos p.swap]? = (shifted (-weight) swapped)[pos p]?) →
      (∀ p : ZMod M × ZMod M, output[pos (-p.1,p.2)]? = (shifted inv swappedBack)[pos p]?) →
      ∀ h t, output[pos (weight*t,inv*h)]? = (List.ofFn input)[pos (h,t)]? := by
  intro N pos shifted input swapped swappedBack output swap undo sign h t
  let shear := Weighted.shear (R := ZMod M)
  let x := shear inv (h,t)
  let y := shear (-weight) x.swap
  let z := shear inv y.swap
  have step (c : ZMod M) (p : ZMod M × ZMod M) (word : Fin N → α) :
      (shifted c word)[pos (shear c p)]? = (List.ofFn word)[pos p]? :=
    middleShear_leaf_entry v q radix c p.1 p.2 a row pre mid post word
  have result := (sign z).trans ((step inv y.swap swappedBack).trans ((undo y).trans
    ((step (-weight) x.swap swapped).trans ((swap x).trans (step inv (h,t) input)))))
  have action : (-z.1,z.2) = (weight*t,inv*h) := Weighted.leaf_word weight inv unit (h,t)
  rwa [action] at result

open M8.RevMachine RecursiveInterchangeLayout in
/-- Feed the translated bit list directly to the ordinary leaf interchange.
Its output is indexed at the shear's original volume. -/
noncomputable def swapLeafList (v : Descriptor) {N : ℕ} (size : N = volume prime v)
    (xs : List (ZMod 2)) (length : xs.length = N) : Fin N → ZMod 2 :=
  fun j => RevSemantics.leafOut (v := v) v rfl
    (fun i => xs.get (i.cast (length.trans size).symm)) (j.cast size)

open M8.RevMachine RecursiveInterchangeLayout in
theorem swapLeafList_entry (v : Descriptor) {N : ℕ} (size : N = volume prime v)
    (xs : List (ZMod 2)) (length : xs.length = N)
    (a : Fin v.beforeRows) (row : Fin v.rows) (pre : Fin v.beforeH)
    (mid : Fin v.between) (post : Fin v.afterD) (h t : Fin (prime^v.width)) :
    (List.ofFn (swapLeafList v size xs length))[index prime v a row pre t mid h post]? =
      xs[index prime v a row pre h mid t post]? := by
  let input := fun i : Fin (volume prime v) => xs.get (i.cast (length.trans size).symm)
  have bounds (i j : Fin (prime^v.width)) := RevSemantics.index_lt a.isLt row.isLt pre.isLt
    i.isLt mid.isLt j.isLt post.isLt
  have swapped := LabelExchange.leafOut_swapped (u := v) (v := v) rfl input
    a a.isLt row row.isLt pre pre.isLt t t.isLt mid mid.isLt h h.isLt post post.isLt
  simp only [ext,dite_eq_left (bounds t h),dite_eq_left (bounds h t)] at swapped
  have left : index prime v a row pre t mid h post < (List.ofFn (swapLeafList v size xs length)).length :=
    by simpa only [List.length_ofFn,size] using bounds t h
  have right : index prime v a row pre h mid t post < xs.length := by simpa only [length,size] using bounds h t
  rw [List.getElem?_eq_getElem left,List.getElem?_eq_getElem right,List.getElem_ofFn]
  exact congrArg some swapped

open RecursiveInterchangeLayout in
theorem weightedLeafSwaps_entry (v : Descriptor) [NeZero M] (radix : prime^v.width = M)
    (weight inv : ZMod M) (unit : weight*inv = 1) :
    let N := (((v.beforeRows*v.rows*v.beforeH)*M)*v.between)*(M*v.afterD)
    let size : N = volume prime v := by simp [N,volume,radix,Nat.mul_assoc]
    let shifted := fun (c : ZMod M) (word : Fin N → ZMod 2) =>
      FiberLayoutData.translated word (fun i => c.val*(i.val/v.between%M)%M)
    let swap := fun c word => swapLeafList v size (shifted c word) (FiberLayoutData.translated_length ..)
    ∀ input (output : List (ZMod 2)) (a : Fin v.beforeRows) (row : Fin v.rows) (pre : Fin v.beforeH)
      (mid : Fin v.between) (post : Fin v.afterD),
      let pos := fun p : ZMod M × ZMod M => index prime v a row pre p.1.val mid p.2.val post
      (∀ p : ZMod M × ZMod M, output[pos (-p.1,p.2)]? =
        (shifted inv (swap (-weight) (swap inv input)))[pos p]?) →
      ∀ h t, output[pos (weight*t,inv*h)]? = (List.ofFn input)[pos (h,t)]? := by
  intro N size shifted swap input output a row pre mid post pos sign
  apply middleShears_weighted_entry v prime radix weight inv unit a row pre mid post
    input (swap inv input) (swap (-weight) (swap inv input)) output _ _ sign
  all_goals
    intro p
    exact swapLeafList_entry v size _ _ a row pre mid post
      ⟨p.1.val,radix.symm ▸ p.1.val_lt⟩ ⟨p.2.val,radix.symm ▸ p.2.val_lt⟩

/-- Negate the head atom on each prefix fiber, retaining the whole suffix
as one block for the block-negation program. -/
def negateLeafHead {α : Type*} {P M B : ℕ} (word : Fin (P*(M*B)) → α) : List α :=
  (List.ofFn (fun p : Fin P => (BlockNegationData.negate (FiberLayoutData.fiber word p)).flatten)).flatten

theorem negateLeafHead_entry {α : Type*} {P M B : ℕ} [NeZero M] (word : Fin (P*(M*B)) → α)
    (p : Fin P) (h : ZMod M) (j : Fin B) :
    (negateLeafHead word)[p.val*(M*B)+((-h).val*B+j.val)]? =
      (List.ofFn word)[p.val*(M*B)+(h.val*B+j.val)]? := by
  have uniform (i : Fin P) := FiberLayoutData.fiber_uniform word i
  have len (i : Fin P) : (FiberLayoutData.fiber word i).flatten.length = M*B := by
    rw [BlockRotationData.uniform_volume B _ (uniform i),FiberLayoutData.fiber_length]
  have inside (x : ZMod M) : x.val*B+j.val < M*B := by
    have bound := Nat.mul_le_mul_right B (Nat.succ_le_of_lt x.val_lt)
    nlinarith only [bound,j.isLt]
  unfold negateLeafHead
  rw [BlockRotationData.flatten_index (M*B) _ (by
    intro b hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    simpa only [BlockNegationData.payload_length] using len i) p.val _ (by simp) (inside (-h))]
  rw [← FiberLayoutData.flatten_fibers,BlockRotationData.flatten_index (M*B) _ (by
    intro b hb
    obtain ⟨blocks,member,rfl⟩ := List.mem_map.mp hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    exact len i) p.val _ (by simp [FiberLayoutData.fibers]) (inside h)]
  simp only [FiberLayoutData.fibers,List.getElem_map,List.getElem_ofFn,Fin.eta]
  have neg : (-h).val = (M-h.val)%M := by
    by_cases zero : h = 0
    · simp [zero]
    · have : NeZero h := ⟨zero⟩
      rw [ZMod.val_neg_of_ne_zero,Nat.mod_eq_of_lt]
      have pos : 0 < h.val := Nat.pos_of_ne_zero (fun eq => zero (ZMod.val_injective M (by simpa using eq)))
      have := h.val_lt
      omega
  rw [neg]
  simpa only [FiberLayoutData.fiber_length] using BlockNegationData.payload_destination B
    (FiberLayoutData.fiber word p) (uniform p) h.val j.val (by simpa using h.val_lt) j.isLt

open RecursiveInterchangeLayout in
theorem weightedLeafOutput_entry (v : Descriptor) [NeZero M] (radix : prime^v.width = M)
    (weight inv : ZMod M) (unit : weight*inv = 1) :
    let N := (((v.beforeRows*v.rows*v.beforeH)*M)*v.between)*(M*v.afterD)
    let size : N = volume prime v := by simp [N,volume,radix,Nat.mul_assoc]
    let shifted := fun (c : ZMod M) (word : Fin N → ZMod 2) =>
      FiberLayoutData.translated word (fun i => c.val*(i.val/v.between%M)%M)
    let swap := fun c word => swapLeafList v size (shifted c word) (FiberLayoutData.translated_length ..)
    ∀ input,
      let xs := shifted inv (swap (-weight) (swap inv input))
      let prefixCount := v.beforeRows*v.rows*v.beforeH
      let suffix := v.between*(M*v.afterD)
      let length : xs.length = prefixCount*(M*suffix) := by
        rw [FiberLayoutData.translated_length]; simp [prefixCount,suffix,Nat.mul_assoc]
      let output := negateLeafHead (P := prefixCount) (M := M) (B := suffix)
        (fun j => xs.get (j.cast length.symm))
      ∀ (a : Fin v.beforeRows) (row : Fin v.rows) (pre : Fin v.beforeH)
        (mid : Fin v.between) (post : Fin v.afterD) (h t : ZMod M),
        output[index prime v a row pre (weight*t).val mid (inv*h).val post]? =
          (List.ofFn input)[index prime v a row pre h.val mid t.val post]? := by
  intro N size shifted swap input xs prefixCount suffix length output a row pre mid post h t
  apply weightedLeafSwaps_entry v radix weight inv unit input output a row pre mid post _ h t
  intro p
  let pref := finProdFinEquiv (finProdFinEquiv (a,row),pre)
  let tail := finProdFinEquiv (mid,finProdFinEquiv ((⟨p.2.val,p.2.val_lt⟩ : Fin M),post))
  have addr (x : ZMod M) : index prime v a row pre x.val mid p.2.val post =
      pref.val*(M*suffix)+(x.val*suffix+tail.val) := by
    simp [index,radix,pref,tail,suffix,finProdFinEquiv]; ring
  change output[index prime v a row pre (-p.1).val mid p.2.val post]? =
    xs[index prime v a row pre p.1.val mid p.2.val post]?
  rw [addr,addr]
  have data : List.ofFn (fun j : Fin (prefixCount*(M*suffix)) => xs.get (j.cast length.symm)) = xs := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using length.symm
    · intros; simp
  rw [← data] -- Read the same suffix position in the unmodified word.
  exact negateLeafHead_entry _ pref p.1 tail

/-- Literal role tape used by both the returned shear and the leaf interchange. -/
noncomputable def leafBitTape (xs : List (ZMod 2)) : ℤ → Fin (prime+4) := fun z =>
  RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (xs.map SparseRoleCircuit.encode) z)

open M8.Machine.ArbitraryWidthHighExchangeShared RecursiveInterchangeLayout in
private theorem sourceWord_leafBitTape (v : Descriptor) (word : Fin (volume prime v) → ZMod 2) :
    sourceWord word = leafBitTape (List.ofFn word) := by
  unfold leafBitTape
  rw [List.map_ofFn]
  rfl

open M8.RevMachine RecursiveInterchangeLayout in
theorem swapLeafList_runs [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    {N : ℕ} (size : N = volume prime v) (xs : List (ZMod 2)) (length : xs.length = N)
    (io : Fin T) (roles : Tapes T prime) (head : roles.head io = 0) (payload : roles.tape io = leafBitTape xs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    GraphContract.Runs (LeafCore.core io)
      (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st)
      (CommonBank.bank (SharedPlacementAlphabet.setTape roles io
        (leafBitTape (List.ofFn (swapLeafList v size xs length))) 0)
        (Routines.hdr v) f p node scalar ctr st)
      (LeafCore.coreCost (volume prime v) v.width) := by
  subst N
  let word := fun j : Fin (volume prime v) => xs.get (j.cast length.symm)
  have input : List.ofFn word = xs := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using length.symm
    · intros; simp [word]
  have run := LabelExchange.leafOut_runs (u := v) rfl positive io roles word head
    (by rwa [sourceWord_leafBitTape,input]) f p node scalar ctr st
  dsimp only at run
  rw [sourceWord_leafBitTape] at run
  exact run

theorem translated_map {α β : Type*} (encode : α → β) (word : Fin (P*(M*B)) → α) (offset : Fin P → ℕ) :
    (FiberLayoutData.translated word offset).map encode = FiberLayoutData.translated (encode ∘ word) offset := by
  simp [FiberLayoutData.translated,FiberLayoutData.fiber,BlockRotationData.rotate,List.map_flatten,
    List.map_ofFn,List.map_drop,List.map_take,Function.comp_def]

open M8.RevMachine RecursiveInterchangeLayout SharedBankStageInput in
/-- Replace a single represented role after an in-place tape operation. -/
theorem leafBank_writeRole [M8.Machine.Net] (v : Descriptor) (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) (tape : ℤ → Fin (prime+4)) :
    let block := LeafCore.core io
    let bank := fun t => raw (CommonBank.bank (SharedPlacementAlphabet.setTape roles io t 0)
      (Routines.hdr v) f p node scalar ctr st) block.tapes
    ∀ {K : ℕ} (ports : Fin block.tapes ↪ Fin K) (S E : Stacks K prime) (slot : Fin block.tapes),
      slot.val = io.val →
      RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
      (∀ i, i ≠ slot → E.L (ports i) = S.L (ports i) ∧ E.R (ports i) = S.R (ports i)) →
      (∀ x, readAt blank (E.L (ports slot)) (E.R (ports slot)) x = tape x) →
      RepT (bank tape) (E.L ∘ ports) (E.R ∘ ports) := by
  intro block bank K ports S E slot leading initial frame payload
  have view (tape : ℤ → Fin (prime+4)) : (bank tape).head slot = 0 ∧ (bank tape).tape slot = tape := by
    have lt : slot.val < CommonBank.count T := leading ▸ (LeafCore.roleSlot io).isLt
    have eq : (⟨slot.val,lt⟩ : Fin (CommonBank.count T)) = LeafCore.roleSlot io := Fin.ext leading
    have h := LeafCore.bank_role (SharedPlacementAlphabet.setTape roles io tape 0) (Routines.hdr v)
      f p node scalar ctr st io
    simpa only [bank,raw,dite_eq_left lt,eq,SharedPlacementAlphabet.setTape,Function.update_self] using h
  intro i x
  by_cases h : i = slot
  · subst i
    rw [(view _).1,(view _).2,sub_zero]
    exact (payload x).symm
  · simp only [Function.comp_apply]
    rw [(frame i h).1,(frame i h).2]
    have cell := initial i x
    by_cases inside : i.val < CommonBank.count T
    · have different : (⟨i.val,inside⟩ : Fin (CommonBank.count T)) ≠ LeafCore.roleSlot io :=
        fun eq => h (Fin.ext ((congrArg Fin.val eq).trans leading.symm))
      obtain ⟨hh,ht⟩ := LeafCore.bank_set roles (Routines.hdr v) f p node scalar ctr st io
        tape _ different
      simpa only [embStk,Function.comp_apply,bank,raw,dite_eq_left inside,hh,ht] using cell
    · simpa only [embStk,Function.comp_apply,bank,raw,dite_eq_right inside] using cell

open M8.RevMachine RecursiveInterchangeLayout SharedBankStageInput in
/-- Execute the ordinary swap on host stacks after a shear. The selected role
comes from the returned stack read; the caller supplies the other tape views. -/
theorem swapReturnedShear_exec [M8.Machine.Net] (v : Descriptor) (positive : v.Positive)
    (size : P*(M*B) = volume prime v) (word : Fin (P*(M*B)) → ZMod 2) (offset : Fin P → ℕ)
    (io : Fin T) (roles : Tapes T prime) (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let block := LeafCore.core io
    let xs := FiberLayoutData.translated word offset
    let y := swapLeafList v size xs (FiberLayoutData.translated_length ..)
    let bank := fun tape => raw (CommonBank.bank (SharedPlacementAlphabet.setTape roles io tape 0)
      (Routines.hdr v) f p node scalar ctr st) block.tapes
    ∀ {K : ℕ} (ports : Fin block.tapes ↪ Fin K) (body : F → Pr F K block.states prime U) (shear : Pr F K block.states prime U)
      (u y' : HS K block.states prime U) (S E : Stacks K prime)
      (slot : Fin block.tapes) (steps : ℕ), slot.val = io.val →
      RepT (raw (CommonBank.bank roles (Routines.hdr v) f p node scalar ctr st) block.tapes) (S.L ∘ ports) (S.R ∘ ports) →
      Exec body shear (mk u S) steps (mk y' E) → y'.user = u.user →
      (∀ i, i ≠ slot → E.L (ports i) = S.L (ports i) ∧ E.R (ports i) = S.R (ports i)) →
      (∀ z, readAt blank (E.L (ports slot)) (E.R (ports slot)) z = RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 (FiberLayoutData.translated (SparseRoleCircuit.encode ∘ word) offset) z)) →
      ∃ z D n, z.user = u.user ∧ n ≤ steps+(LeafCore.coreCost (volume prime v) v.width*(block.tapes+5)+6) ∧
        Exec body (.seq shear (embProg ports Empty.elim (foreign block.program))) (mk u S) n (mk z D) ∧
        RepT (bank (leafBitTape (List.ofFn y))) (D.L ∘ ports) (D.R ∘ ports) ∧
        (∀ x, readAt blank (D.L (ports slot)) (D.R (ports slot)) x = leafBitTape (List.ofFn y) x) ∧
        ∀ j, (∀ i, ports i ≠ j) → D.L j = E.L j ∧ D.R j = E.R j := by
  intro block xs y bank K ports body shear u y' S E slot steps leading initial firstRun user frame payload
  have view (tape : ℤ → Fin (prime+4)) : (bank tape).head slot = 0 ∧ (bank tape).tape slot = tape := by
    have lt : slot.val < CommonBank.count T := leading ▸ (LeafCore.roleSlot io).isLt
    have eq : (⟨slot.val,lt⟩ : Fin (CommonBank.count T)) = LeafCore.roleSlot io := Fin.ext leading
    have h := LeafCore.bank_role (SharedPlacementAlphabet.setTape roles io tape 0) (Routines.hdr v)
      f p node scalar ctr st io
    simpa only [bank,raw,dite_eq_left lt,eq,SharedPlacementAlphabet.setTape,Function.update_self] using h
  have ready := leafBank_writeRole v io roles f p node scalar ctr st (leafBitTape xs) ports S E slot
    leading initial frame (by intro x; simpa only [xs,leafBitTape,translated_map] using payload x)
  have run := swapLeafList_runs v positive size xs (FiberLayoutData.translated_length ..) io
    (SharedPlacementAlphabet.setTape roles io (leafBitTape xs) 0) (by simp [SharedPlacementAlphabet.setTape])
    (by simp [SharedPlacementAlphabet.setTape]) f p node scalar ctr st
  obtain ⟨z,D,_,rfl,rep,hu,_,_,_,n,hn,exec⟩ := foreign_exec (P := Empty) Empty.elim block.program run
    (embDn ports y') (embStk ports E) _ rfl ready
  obtain ⟨u',D',placed,_,user',eq,keep⟩ := exec_emb (body' := body) (ι := Empty.elim)
    ports.injective (fun e => nomatch e) exec y' rfl E rfl
  rw [← eq] at rep
  have result : RepT (bank (leafBitTape (List.ofFn y))) (D'.L ∘ ports) (D'.R ∘ ports) := by
    simpa only [embStk,Function.comp_apply,bank,y,SharedPlacementAlphabet.setTape,Function.update_idem] using rep
  refine ⟨u',D',steps+n,user'.trans (hu.trans user),Nat.add_le_add_left hn _,Exec.seq firstRun placed,result,?_,keep⟩
  intro x
  simpa only [embStk,Function.comp_apply,(view _).1,(view _).2,sub_zero] using (result slot x).symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback
