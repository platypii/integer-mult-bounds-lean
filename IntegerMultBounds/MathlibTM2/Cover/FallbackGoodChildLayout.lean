module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodPayload

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

def goodChildDescriptor (M r g W : ℕ) : RecursiveInterchangeLayout.Descriptor :=
  ⟨1,1,1,r,M^(g+g),W⟩

omit [NeZero M] in
/-- The first call has an empty inherited middle field. -/
theorem rankDescriptor_goodChild :
    rankDescriptor M r g ⟨1,1,1,r+g,1,W⟩ = goodChildDescriptor M r g W := by
  simp [rankDescriptor,goodChildDescriptor,pow_add]

theorem goodChildVolume (M r g W : ℕ) :
    RecursiveInterchangeLayout.volume M (goodChildDescriptor M r g W) = M^((r+g)+(r+g))*W := by
  simp only [RecursiveInterchangeLayout.volume,goodChildDescriptor,one_mul,pow_add]
  ring

private theorem rank_join {a b : ℕ} (x : Fin a → ZMod M) (y : Fin b → ZMod M) :
    (rank (Fin.append x y)).val = (rank x).val*M^b+(rank y).val :=
  ArbitraryWidthSliceTranspose.rank_append x y

private theorem rank_cast {a b : ℕ} (h : a = b) (x : Fin b → ZMod M) :
    (rank (fun i : Fin a => x (i.cast h))).val = (rank x).val := by subst b; rfl

theorem goodChildIndex (hg tg : Fin g → ZMod M) (s : (Fin r → ZMod M) × (Fin r → ZMod M)) (j : Fin W) :
    let t := childFields hg tg s
    (index (Fin.append t.1 t.2) j).val =
      RecursiveInterchangeLayout.index M (goodChildDescriptor M r g W) 0 0 0
        (rank s.1).val (rank (Fin.append hg tg)).val (rank s.2).val j.val := by
  dsimp only [childFields]
  rw [index_val,rank_join,rank_join,rank_cast,rank_join,rank_join]
  simp only [RecursiveInterchangeLayout.index,goodChildDescriptor,Nat.zero_mul,Nat.zero_add,pow_add]
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
