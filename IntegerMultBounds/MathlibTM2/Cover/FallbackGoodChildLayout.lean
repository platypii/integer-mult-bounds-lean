module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodPayload
import IntegerMultBounds.Machine.RecursiveInterchangeVolume

/-! The rank child reads both active fields in place, with the inactive digits
packed into the middle field of the recursive interchange descriptor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine FlatCoordinateLayout
variable {r g M W : ℕ} [NeZero M]

/-- The stopped leaf acts on head digit i and its reversed tail partner.
Changing either digit uses the same one-atom view for every swap and shear. -/
theorem leafPair_index (v : RecursiveInterchangeLayout.Descriptor) (width : v.width = r)
    (i : Fin r) (x y : Fin r → ZMod M) (h t : ZMod M) (a row before middle after : ℕ) :
    let j := i.rev
    let view := RecursiveInterchangeLayout.child M 1 1 v i j
    RecursiveInterchangeLayout.index M view a row (before*M^i.val+prefixIndex x i) h.val
      ((((rank x).val % M^suffixFields i)*v.between+middle)*M^j.val+prefixIndex y j) t.val
      (((rank y).val % M^suffixFields j)*v.afterD+after) =
    RecursiveInterchangeLayout.index M v a row before (rank (Function.update x i h)).val middle
      (rank (Function.update y j t)).val after := by
  have split (z : Fin r → ZMod M) (k : Fin r) (u : ZMod M) :
      (prefixIndex z k*M+u.val)*M^suffixFields k+(rank z).val%M^suffixFields k =
        (rank (Function.update z k u)).val := by
    simpa [index_val,suffixSize,suffix,Nat.add_mul,Nat.mul_assoc] using
      (index_update z k u (0 : Fin 1)).symm
  have atPair := RecursiveInterchangeLayout.child_index M 1 1 v i i.rev (by simpa using width)
    a row before (prefixIndex x i) h.val ((rank x).val % M^suffixFields i) middle
    (prefixIndex y i.rev) t.val ((rank y).val % M^suffixFields i.rev) after
  simp only [Nat.mul_one,pow_one,suffixFields] at atPair
  simp only [suffixFields] at split
  rw [split x i h,split y i.rev t] at atPair
  simpa only [suffixFields,RecursiveInterchangeLayout.role,Nat.div_one] using atPair

/-- An atom-pair operation on the descriptor transports the whole payload.
The same hypothesis applies to a shear, sign change or interchange. -/
theorem leafPair_apply {α : Type*} (v : RecursiveInterchangeLayout.Descriptor) (width : v.width = r)
    (q w : ℕ) (radix : M = q^w) (i : Fin r) (op : ZMod M × ZMod M → ZMod M × ZMod M) (src dst : ℕ → α)
    (x y : Fin r → ZMod M) (a row before middle after : ℕ)
    (hb : before < v.beforeH)
    (hm : middle < v.between) (he : after < v.afterD) :
    let view := {(RecursiveInterchangeLayout.child M 1 1 v i i.rev) with width := w}
    (∀ pre < view.beforeH, ∀ mid < view.between, ∀ post < view.afterD, ∀ h t : ZMod M,
      let z := op (h,t)
      dst (RecursiveInterchangeLayout.index q view a row pre z.1.val mid z.2.val post) =
        src (RecursiveInterchangeLayout.index q view a row pre h.val mid t.val post)) →
    let z := op (x i,y i.rev)
    dst (RecursiveInterchangeLayout.index M v a row before (rank (Function.update x i z.1)).val
      middle (rank (Function.update y i.rev z.2)).val after) =
      src (RecursiveInterchangeLayout.index M v a row before (rank x).val middle (rank y).val after) := by
  intro view run z
  have pack {p n q m : ℕ} (hp : p < n) (hq : q < m) : p*m+q < n*m := by
    nlinarith [Nat.mul_le_mul_right m (Nat.succ_le_of_lt hp)]
  have gap (u : Fin r → ZMod M) (k : Fin r) :
      (rank u).val % M^suffixFields k < M^suffixFields k := Nat.mod_lt _ (pow_pos (NeZero.pos M) _)
  have pre := pack hb (prefix_lt x i)
  have mid := pack (pack (gap x i) hm) (prefix_lt y i.rev)
  have post := pack (gap y i.rev) he
  have step := run (before*M^i.val+prefixIndex x i) (by simpa [view,RecursiveInterchangeLayout.child,prefixSize] using pre)
    ((((rank x).val % M^suffixFields i)*v.between+middle)*M^i.rev.val+prefixIndex y i.rev)
    (by simpa [view,RecursiveInterchangeLayout.child,prefixSize,suffixFields] using mid)
    (((rank y).val % M^suffixFields i.rev)*v.afterD+after)
    (by simpa [view,RecursiveInterchangeLayout.child,suffixFields] using post) (x i) (y i.rev)
  have addr (pre h mid t post : ℕ) : RecursiveInterchangeLayout.index q view a row pre h mid t post =
      RecursiveInterchangeLayout.index M (RecursiveInterchangeLayout.child M 1 1 v i i.rev)
        a row pre h mid t post := by
    simp only [RecursiveInterchangeLayout.index,view,RecursiveInterchangeLayout.child,pow_one,radix]
  simpa only [addr,leafPair_index v width,Function.update_eq_self] using step

/-- A nested good child keeps the inherited middle field between the two
new gaps. The before-row, row, prefix and trailing ranges are inherited. -/
def rankDescriptor (M r g : ℕ) (v : RecursiveInterchangeLayout.Descriptor) :
    RecursiveInterchangeLayout.Descriptor :=
  {v with width := r, between := M^g * v.between * M^g}

omit [NeZero M] in
theorem rankDescriptor_fits (v : RecursiveInterchangeLayout.Descriptor) {H K : ℕ}
    (base : M < 2^H) (seed : v.between < 2^K) :
    (rankDescriptor M r g v).between < 2^((g+g)*H+K) := by
  calc
    _ = M^(g+g)*v.between := by simp only [rankDescriptor,pow_add]; ring
    _ ≤ (2^H)^(g+g)*v.between := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left base.le _)
    _ < (2^H)^(g+g)*2^K := Nat.mul_lt_mul_of_pos_left seed (by positivity)
    _ = _ := by rw [← pow_mul,Nat.mul_comm H,pow_add]

omit [NeZero M] in
theorem rankDescriptor_index (v : RecursiveInterchangeLayout.Descriptor)
    (width : v.width = r+g) (a row before h hg middle tg t suffix : ℕ) :
    RecursiveInterchangeLayout.index M (rankDescriptor M r g v) a row before h
        ((hg*v.between+middle)*M^g+tg) t suffix =
      RecursiveInterchangeLayout.index M v a row before (h*M^g+hg) middle
        (tg*M^r+t) suffix := by
  simp only [RecursiveInterchangeLayout.index,rankDescriptor,width,pow_add]
  ring

omit [NeZero M] in
theorem rankDescriptor_volume (v : RecursiveInterchangeLayout.Descriptor) (width : v.width = r+g) :
    RecursiveInterchangeLayout.volume M (rankDescriptor M r g v) =
      RecursiveInterchangeLayout.volume M v := by
  simp only [RecursiveInterchangeLayout.volume,rankDescriptor,width,pow_add]
  ring

omit [NeZero M] in
/-- Splitting the rows among roles and retaining the active atoms gives the
width ratio and volume weight of the same recursive descriptor. -/
theorem rankDescriptor_role_size (v : RecursiveInterchangeLayout.Descriptor)
    (roles atoms b : ℕ) (width : v.width = atoms*b) (fits : r ≤ atoms)
    (divides : roles ∣ v.rows) :
    let child := rankDescriptor M (r*b) ((atoms-r)*b) (RecursiveInterchangeLayout.role v roles)
    child.width*atoms = r*v.width ∧
      RecursiveInterchangeLayout.volume M child*roles = RecursiveInterchangeLayout.volume M v := by
  intro child
  constructor
  · change r*b*atoms = r*v.width
    rw [width]
    ring
  · have split : (RecursiveInterchangeLayout.role v roles).width = r*b+(atoms-r)*b := by
      change v.width = _
      rw [width, ← Nat.add_mul, Nat.add_sub_of_le fits]
    exact (congrArg (· * roles) (rankDescriptor_volume _ split)).trans
      (RecursiveInterchangeLayout.role_volume_mul M roles v divides)

omit [NeZero M] in
/-- When the parent width has a remainder, keep that remainder in the middle
field. The same child satisfies the rank bound and the exact role-volume bill. -/
theorem rankDescriptor_quotient_size (v : RecursiveInterchangeLayout.Descriptor)
    (roles fields : ℕ) (fits : r ≤ fields) (divides : roles ∣ v.rows) :
    let b := v.width/fields
    let child := rankDescriptor M (r*b) (v.width-r*b) (RecursiveInterchangeLayout.role v roles)
    child.width*fields ≤ r*v.width ∧
      RecursiveInterchangeLayout.volume M child*roles = RecursiveInterchangeLayout.volume M v := by
  intro b child
  have used : b*fields ≤ v.width := Nat.div_mul_le_self _ _
  have active : r*b ≤ v.width := (Nat.mul_le_mul_right b fits).trans (Nat.mul_comm fields b ▸ used)
  constructor
  · change r*b*fields ≤ r*v.width
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left r used
  · have split : (RecursiveInterchangeLayout.role v roles).width = r*b+(v.width-r*b) :=
      (Nat.add_sub_of_le active).symm
    exact (congrArg (· * roles) (rankDescriptor_volume _ split)).trans
      (RecursiveInterchangeLayout.role_volume_mul M roles v divides)

omit [NeZero M] in
/-- Along a chain of recursive calls the gaps accumulate on both sides of the
same inherited middle field. -/
theorem rankDescriptor_chain (v : RecursiveInterchangeLayout.Descriptor) (gaps : List ℕ) :
    gaps.foldl (fun u g => rankDescriptor M (u.width-g) g u) v =
      rankDescriptor M (v.width-gaps.sum) gaps.sum v := by
  induction gaps generalizing v with
  | nil => cases v; simp [rankDescriptor]
  | cons g gs ih =>
    rw [List.foldl_cons,ih,List.sum_cons]
    cases v
    simp [rankDescriptor,Nat.sub_sub,pow_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

omit [NeZero M] in
theorem rankDescriptor_chain_volume (v : RecursiveInterchangeLayout.Descriptor)
    (gaps : List ℕ) (fits : gaps.sum ≤ v.width) :
    RecursiveInterchangeLayout.volume M
      (gaps.foldl (fun u g => rankDescriptor M (u.width-g) g u) v) =
      RecursiveInterchangeLayout.volume M v := by
  rw [rankDescriptor_chain]
  exact rankDescriptor_volume v (Nat.sub_add_cancel fits).symm

omit [NeZero M] in
/-- A parent pays its child's time once. The terminal bill is evaluated on
the final descriptor, and every record overhead uses the original volume. -/
theorem rankDescriptor_chain_time {ι : Type*} (gap overhead : ι → ℕ)
    (time : List ι → RecursiveInterchangeLayout.Descriptor → ℕ)
    (step : ∀ i is v, gap i ≤ v.width → time (i :: is) v ≤
      time is (rankDescriptor M (v.width-gap i) (gap i) v) + overhead i * RecursiveInterchangeLayout.volume M v)
    (records : List ι) (v : RecursiveInterchangeLayout.Descriptor)
    (fits : (records.map gap).sum ≤ v.width) :
    time records v ≤ time [] (rankDescriptor M (v.width-(records.map gap).sum) (records.map gap).sum v) +
      (records.map overhead).sum * RecursiveInterchangeLayout.volume M v := by
  rw [← rankDescriptor_chain]
  induction records generalizing v with
  | nil => simp
  | cons i is ih =>
    simp only [List.map_cons,List.sum_cons] at fits ⊢
    have headFits : gap i ≤ v.width := by omega
    let child := rankDescriptor M (v.width-gap i) (gap i) v
    have tailFits : (is.map gap).sum ≤ child.width := by
      change _ ≤ v.width-gap i
      omega
    have tail := ih child tailFits
    have vol : RecursiveInterchangeLayout.volume M child = RecursiveInterchangeLayout.volume M v :=
      rankDescriptor_volume v (Nat.sub_add_cancel headFits).symm
    rw [vol] at tail
    exact (step i is v headFits).trans ((Nat.add_le_add_right tail _).trans_eq (by
      simp only [List.foldl_cons,Nat.add_mul,child]
      omega))

def goodChildDescriptor (M r g W : ℕ) : RecursiveInterchangeLayout.Descriptor :=
  ⟨1,1,1,r,M^(g+g),W⟩

omit [NeZero M] in
/-- The first call has an empty inherited middle field. -/
theorem rankDescriptor_goodChild :
    rankDescriptor M r g ⟨1,1,1,r+g,1,W⟩ = goodChildDescriptor M r g W := by
  simp [rankDescriptor,goodChildDescriptor,pow_add]

omit [NeZero M] in
/-- An inherited middle made of whole atoms stays atom-aligned down the
entire chain. Outer record axes and the suffix keep their original ranges. -/
theorem rankDescriptor_chain_atoms (v : RecursiveInterchangeLayout.Descriptor)
    (middle : ℕ) (aligned : v.between = M^middle) (gaps : List ℕ) :
    gaps.foldl (fun u g => rankDescriptor M (u.width-g) g u) v =
      {v with width := v.width-gaps.sum, between := M^(gaps.sum+middle+gaps.sum)} := by
  rw [rankDescriptor_chain]
  simp only [rankDescriptor,aligned,pow_add]

omit [NeZero M] in
/-- At entry from a physical child path, separate the arbitrary root radix
from the atoms introduced by both kinds of descent. -/
theorem rankDescriptor_path_middle {roles m n atoms width : ℕ}
    {root v : RecursiveInterchangeLayout.Descriptor}
    (path : RecursiveInterchangeVolume.Path M roles m root n v)
    (split : v.width = atoms*width) (gaps : List ℕ) :
    let child := gaps.foldl (fun u g => rankDescriptor (M^width) (u.width-g) g u)
      {v with width := atoms}
    ∃ k : ℕ, child.between = root.between*(M^width)^(gaps.sum+atoms*k+gaps.sum) ∧
      k+2 ≤ 2*m^n := by
  intro child
  obtain ⟨k,mid,bound⟩ := path.middle_blocks
  refine ⟨k,?_,bound⟩
  dsimp only [child]
  rw [rankDescriptor_chain]
  simp only [rankDescriptor,mid,split,pow_add,← pow_mul]
  rw [show atoms*width*k = width*(atoms*k) by ring]
  ring

theorem goodChildVolume (M r g W : ℕ) :
    RecursiveInterchangeLayout.volume M (goodChildDescriptor M r g W) = M^((r+g)+(r+g))*W := by
  simp only [RecursiveInterchangeLayout.volume,goodChildDescriptor,one_mul,pow_add]
  ring

private theorem rank_join {a b : ℕ} (x : Fin a → ZMod M) (y : Fin b → ZMod M) :
    (rank (Fin.append x y)).val = (rank x).val*M^b+(rank y).val :=
  ArbitraryWidthSliceTranspose.rank_append x y

private theorem rank_cast {a b : ℕ} (h : a = b) (x : Fin b → ZMod M) :
    (rank (fun i : Fin a => x (i.cast h))).val = (rank x).val := by subst b; rfl

/-- The physical address is preserved when a nested call moves its two
spectator slices into an already occupied middle field. -/
theorem rankDescriptor_childFields_index (v : RecursiveInterchangeLayout.Descriptor)
    (width : v.width = r+g) (hg tg : Fin g → ZMod M)
    (s : (Fin r → ZMod M) × (Fin r → ZMod M)) (a row before middle suffix : ℕ) :
    let t := childFields hg tg s
    RecursiveInterchangeLayout.index M v a row before (rank t.1).val middle (rank t.2).val suffix =
      RecursiveInterchangeLayout.index M (rankDescriptor M r g v) a row before (rank s.1).val
        (((rank hg).val*v.between+middle)*M^g+(rank tg).val) (rank s.2).val suffix := by
  dsimp only [childFields]
  rw [rank_join,rank_cast,rank_join,rankDescriptor_index v width]

theorem goodChildIndex (hg tg : Fin g → ZMod M) (s : (Fin r → ZMod M) × (Fin r → ZMod M)) (j : Fin W) :
    let t := childFields hg tg s
    (index (Fin.append t.1 t.2) j).val =
      RecursiveInterchangeLayout.index M (goodChildDescriptor M r g W) 0 0 0
        (rank s.1).val (rank (Fin.append hg tg)).val (rank s.2).val j.val := by
  dsimp only [childFields]
  rw [index_val,rank_join,rank_join,rank_cast,rank_join,rank_join]
  simp only [RecursiveInterchangeLayout.index,goodChildDescriptor,Nat.zero_mul,Nat.zero_add,pow_add]
  ring

/-- Positions of the adjacent atom exchanges packing a tail after the head.
Each successive tail atom crosses the middle, starting at its right edge. -/
def middleTailSchedule (middle tail : ℕ) : List ℕ :=
  (List.range tail).flatMap fun t => (List.range middle).reverse.map (t+·)

theorem middleTailSchedule_length (middle tail : ℕ) :
    (middleTailSchedule middle tail).length = tail*middle := by
  induction tail with
  | zero => simp [middleTailSchedule]
  | succ t ih => simpa [middleTailSchedule,List.range_succ,Nat.succ_mul] using ih

theorem middleTailSchedule_inside {middle tail i : ℕ} (used : i ∈ middleTailSchedule middle tail) :
    i+1 < middle+tail := by
  obtain ⟨t,ht,slot⟩ := List.mem_flatMap.mp used
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp slot
  simp only [List.mem_reverse,List.mem_range] at ht hj
  omega

/-- A schedule entry is measured from the first atom after the unchanged head. -/
def swapAtomAt {α : Type*} : ℕ → List α → List α
  | 0,x::y::xs => y::x::xs
  | n+1,x::xs => x::swapAtomAt n xs
  | _,xs => xs

private theorem swapAtomAt_prefix {α : Type*} (pre xs : List α) (i : ℕ) :
    swapAtomAt (pre.length+i) (pre++xs) = pre++swapAtomAt i xs := by
  induction pre with
  | nil => simp
  | cons x pre ih => simp [Nat.succ_add,swapAtomAt,ih]

theorem fold_swapAtomAt_prefix {α : Type*} (pre : List α) (is : List ℕ) (xs : List α) :
    is.foldl (fun ys i => swapAtomAt (pre.length+i) ys) (pre++xs) =
      pre++is.foldl (fun ys i => swapAtomAt i ys) xs := by
  induction is generalizing xs with
  | nil => rfl
  | cons i is ih => simp only [List.foldl_cons,swapAtomAt_prefix,ih]

private theorem slideAtom {α : Type*} (mid : List α) (x : α) (rest : List α) :
    (List.range mid.length).reverse.foldl (fun xs i => swapAtomAt i xs) (mid++x::rest) =
      x::(mid++rest) := by
  induction mid using List.reverseRecOn generalizing x rest with
  | nil => rfl
  | append_singleton mid y ih =>
    simp only [List.length_append,List.length_singleton,List.range_succ,List.reverse_append,
      List.reverse_singleton,List.singleton_append,List.foldl_cons,List.append_assoc,List.cons_append,List.nil_append]
    rw [← Nat.add_zero mid.length,swapAtomAt_prefix]
    simpa [swapAtomAt] using ih x (y::rest)

theorem middleTailSchedule_packs {α : Type*} (mid tail suffix : List α) :
    (middleTailSchedule mid.length tail.length).foldl (fun xs i => swapAtomAt i xs)
      (mid++tail++suffix) = tail++mid++suffix := by
  induction tail using List.reverseRecOn generalizing suffix with
  | nil => simp [middleTailSchedule]
  | append_singleton tail x ih =>
    simp only [List.length_append,List.length_singleton,middleTailSchedule,List.range_succ,
      List.flatMap_append,List.flatMap_singleton,List.foldl_append,List.foldl_map]
    have first := ih (x::suffix)
    simp only [middleTailSchedule,List.append_assoc] at first
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [first]
    rw [fold_swapAtomAt_prefix,slideAtom]

/-- Move the inherited middle field past the active tail. The signed scan
stores the head and tail consecutively and carries the middle in its suffix. -/
def packMiddleTail (heads middle tails suffix : ℕ) :
    Fin (heads*(middle*(tails*suffix))) ≃ Fin (heads*(tails*(middle*suffix))) :=
  let exchange : Fin middle × Fin tails × Fin suffix ≃ Fin tails × Fin middle × Fin suffix :=
    ⟨fun (m,t,j) => (t,m,j),fun (t,m,j) => (m,t,j),fun _ => rfl,fun _ => rfl⟩
  let swap := finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin middle)) finProdFinEquiv.symm).trans
      (exchange.trans
        ((Equiv.prodCongr (Equiv.refl (Fin tails)) finProdFinEquiv).trans finProdFinEquiv)))
  finProdFinEquiv.symm.trans ((Equiv.prodCongr (Equiv.refl (Fin heads)) swap).trans finProdFinEquiv)

theorem packMiddleTail_index {heads middle tails suffix : ℕ} (h : Fin heads) (m : Fin middle)
    (t : Fin tails) (j : Fin suffix) :
    packMiddleTail heads middle tails suffix
      (finProdFinEquiv (h,finProdFinEquiv (m,finProdFinEquiv (t,j)))) =
      finProdFinEquiv (h,finProdFinEquiv (t,finProdFinEquiv (m,j))) := by
  simp [packMiddleTail]

omit [NeZero M] in
/-- Packing a descriptor preserves its outer record number. Its entire middle
field, including any inherited spectator, becomes the high part of the suffix. -/
theorem descriptor_packed_index (v : RecursiveInterchangeLayout.Descriptor)
    (a : Fin v.beforeRows) (row : Fin v.rows) (b : Fin v.beforeH)
    (h t : Fin (M^v.width)) (m : Fin v.between) (j : Fin v.afterD) :
    let records := v.beforeRows*v.rows*v.beforeH
    let outer : Fin records := finProdFinEquiv (finProdFinEquiv (a,row),b)
    let head := finProdFinEquiv (outer,h)
    let src := finProdFinEquiv (head,finProdFinEquiv (m,finProdFinEquiv (t,j)))
    let dst := packMiddleTail (records*M^v.width) v.between (M^v.width) v.afterD src
    src.val = RecursiveInterchangeLayout.index M v a row b h m t j ∧
      dst.val = (finProdFinEquiv (outer,finProdFinEquiv (finProdFinEquiv (h,t),finProdFinEquiv (m,j))) :
        Fin (records*((M^v.width*M^v.width)*(v.between*v.afterD)))).val := by
  intro records outer head src dst
  constructor
  · simp only [src,head,outer,finProdFinEquiv,Equiv.coe_fn_mk,RecursiveInterchangeLayout.index]
    ring
  · dsimp only [dst,src]
    rw [packMiddleTail_index]
    simp only [head,finProdFinEquiv,Equiv.coe_fn_mk]
    ring

/-- At atom rank the packed address is precisely the signed pass's outer
record, flat coordinate index, and unchanged inherited suffix. -/
theorem descriptor_signed_index (v : RecursiveInterchangeLayout.Descriptor) (width : v.width = r)
    (a : Fin v.beforeRows) (row : Fin v.rows) (b : Fin v.beforeH)
    (x y : Fin r → ZMod M) (m : Fin v.between) (j : Fin v.afterD) :
    let outer := finProdFinEquiv (finProdFinEquiv (a,row),b)
    let head := finProdFinEquiv (outer,rank x)
    let src := finProdFinEquiv (head,finProdFinEquiv (m,finProdFinEquiv (rank y,j)))
    let dst := packMiddleTail ((v.beforeRows*v.rows*v.beforeH)*M^r) v.between (M^r) v.afterD src
    src.val = RecursiveInterchangeLayout.index M v a row b (rank x) m (rank y) j ∧
      dst.val = (finProdFinEquiv (outer,index (Fin.append x y) (finProdFinEquiv (m,j)))).val := by
  subst r
  intro outer head src dst
  obtain ⟨source,target⟩ := descriptor_packed_index v a row b (rank x) (rank y) m j
  refine ⟨source,target.trans ?_⟩
  simp only [outer,index,finProdFinEquiv,Equiv.coe_fn_mk,rank_join,pow_add]
  ring

/-- In the parent record this is one rectangular transpose for each head.
Both inactive digit slices form a single middle index. -/
theorem goodChild_packed_index (hg tg : Fin g → ZMod M)
    (s : (Fin r → ZMod M) × (Fin r → ZMod M)) (j : Fin W) :
    let middle := rank (Fin.append hg tg)
    let addr := index (Fin.append (childFields hg tg s).1 (childFields hg tg s).2) j
    let size : M^((r+g)+(r+g))*W = M^r*(M^(g+g)*(M^r*W)) := by simp only [pow_add]; ring
    packMiddleTail (M^r) (M^(g+g)) (M^r) W (addr.cast size) =
      finProdFinEquiv (rank s.1,finProdFinEquiv (rank s.2,finProdFinEquiv (middle,j))) := by
  intro middle addr size
  rw [← packMiddleTail_index]
  apply congrArg
  apply Fin.ext
  simp only [Fin.val_cast,addr,goodChildIndex,RecursiveInterchangeLayout.index,goodChildDescriptor,
    Nat.zero_mul,Nat.zero_add,finProdFinEquiv,Equiv.coe_fn_mk,middle]
  ring

theorem childFields_surjective {R : Type*} (x y : Fin (r+g) → R) :
    ∃ hg tg s, childFields hg tg s = (x,y) := by
  let z := fun i : Fin (g+r) => y (i.cast (Nat.add_comm g r))
  refine ⟨fun i => x (i.natAdd r),fun i => z (i.castAdd r),
    (fun i => x (i.castAdd g),fun i => z (i.natAdd g)),?_⟩
  have split {a b : ℕ} (f : Fin (a+b) → R) :
      Fin.append (fun i => f (i.castAdd b)) (fun i => f (i.natAdd a)) = f := by
    funext i
    induction i using Fin.addCases <;> simp
  apply Prod.ext
  · exact split x
  · funext i
    dsimp only [childFields]
    rw [split z]
    rfl

/-- A child run on every valid middle-field value acts on the parent's active
coordinates while preserving its inherited spectator digits. -/
theorem rankDescriptor_child_effect {α : Type*} (v : RecursiveInterchangeLayout.Descriptor)
    (width : v.width = r+g) (w inv : Fin (r+g) → ZMod M) (word out : ℕ → α)
    (a row before suffix : ℕ)
    (run : ∀ mid < (rankDescriptor M r g v).between, ∀ s : (Fin r → ZMod M) × (Fin r → ZMod M),
      let addr := fun u : (Fin r → ZMod M) × (Fin r → ZMod M) =>
        RecursiveInterchangeLayout.index M (rankDescriptor M r g v) a row before
          (rank u.1).val mid (rank u.2).val suffix
      out (addr (Weighted.child r (fun i => w (i.castAdd g)) (fun i => inv (i.castAdd g)) s)) = word (addr s))
    (x y : Fin (r+g) → ZMod M) (middle : ℕ) (hm : middle < v.between) :
    let t := Weighted.child r w inv (x,y)
    out (RecursiveInterchangeLayout.index M v a row before (rank t.1).val middle (rank t.2).val suffix) =
      word (RecursiveInterchangeLayout.index M v a row before (rank x).val middle (rank y).val suffix) := by
  obtain ⟨hg,tg,s,eq⟩ := childFields_surjective x y
  have digit {i n j b : ℕ} (hi : i < n) (hj : j < b) : i*b+j < n*b := calc
    i*b+j < i*b+b := Nat.add_lt_add_left hj _
    _ = (i+1)*b := (Nat.succ_mul ..).symm
    _ ≤ n*b := Nat.mul_le_mul_right _ hi
  have action := run _ (digit (digit (rank hg).isLt hm) (rank tg).isLt) s
  dsimp only at action ⊢
  rw [← rankDescriptor_childFields_index v width hg tg,← rankDescriptor_childFields_index v width hg tg] at action
  rw [← childFields_apply w inv hg tg s,eq] at action
  exact action

/-- A recursive action on the two rank fields induces the parent action at every
serialized address, including both spectator fields and every trailing symbol. -/
theorem goodChild_effect {α : Type*} (w w' : Fin (r+g) → ZMod M)
    (word out : Fin (M^((r+g)+(r+g))*W) → α)
    (run : ∀ (hg tg : Fin g → ZMod M) (s : (Fin r → ZMod M) × (Fin r → ZMod M)) (j : Fin W),
      let encode := fun u => let t := childFields hg tg u; index (Fin.append t.1 t.2) j
      out (encode (Weighted.child r (fun i => w (i.castAdd g)) (fun i => w' (i.castAdd g)) s)) =
        word (encode s))
    (x y : Fin (r+g) → ZMod M) (j : Fin W) :
    let t := Weighted.child r w w' (x,y)
    out (index (Fin.append t.1 t.2) j) = word (index (Fin.append x y) j) := by
  obtain ⟨hg,tg,s,eq⟩ := childFields_surjective x y
  have h := run hg tg s j
  dsimp only at h
  rw [← childFields_apply w w' hg tg s,eq] at h
  exact h

end IntegerMultBounds.MathlibTM2.Cover.Fallback
