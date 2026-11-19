module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCrossGroup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadLayout

/-! Run both mixed blocks of one pivot using its two prepared reciprocal words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout LabelTraversal GoodForm Matrix
open M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear HeadPivotLayout
variable {P U α : Type} {T A d M W : ℕ} [NeZero M]

omit [NeZero M] in
private theorem changeReciprocal (host : Fin 53 ↪ Fin T) (a b : Bool) (H J : ℕ)
    (stage parent pivot other : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4)
    (p q : ℤ) (word : Fin (M^d*W) → α) (S : Stacks T A)
    (h : HeadColumnReady ((coeff a).trans host) (shear.trans host) H J stage parent pivot sym source dest p q word S)
    (value : S.R (host (coeff b 14)) = other) :
    HeadColumnReady ((coeff b).trans host) (shear.trans host) H J stage parent other sym source dest p q word S := by
  have same (j : Fin 17) (ne : j ≠ 14) : host (coeff b j) = host (coeff a j) :=
    congrArg host ((by cases a <;> cases b <;> decide : ∀ j : Fin 17, j ≠ 14 → coeff b j = coeff a j) j ne)
  have keep (j : Fin 17) (ne : j ≠ 14) := congrArg S.R (same j ne)
  exact ⟨(keep 13 (by decide)).trans h.stage,(keep 16 (by decide)).trans h.weights,value,
    (keep 2 (by decide)).trans h.modulus,fun j hj => (keep j (by omega)).trans (h.coeffWork j hj),
    h.base,h.one,h.width,h.scratch,h.src,h.dst⟩

def crossPivotGroups (negative : Bool) (k : Fin d) (host : Fin 53 ↪ Fin T) (ts : List (Fin d)) :
    Pr P T 217 A U :=
  .seq (crossGroup true k ((coeff negative).trans host) (shear.trans host) ts)
    (crossGroup false k ((coeff (!negative)).trans host) (shear.trans host) ts)

theorem crossPivotGroups_exec [Fintype P] (body : P → Pr P T 217 A U)
    (host : Fin 53 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ t (ht : t < rank), IsUnit (lead (t+1) (lt_of_lt_of_le ht hr) G).det)
    (idem : G*G = G) (L : Matrix (Fin d) (Fin rank) (ZMod M)) (R : Matrix (Fin rank) (Fin d) (ZMod M))
    (factor : G = L*R) (inv : Fin d → ZMod M) (a : Fin rank) (negative : Bool)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W) (tail rest : List (Fin (A+4)))
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+d)*W : ℕ) → dest z = blank) :
    let k := a.castLE hr
    let N := (stageAt G rank hr minor a.val a.isLt.le).M
    let S := stageAt G rank hr minor rank le_rfl
    let δ := fun t : Fin d => if t.val < rank then S.M t t else 1
    let δ' := fun t : Fin d => if t.val < rank then Ring.inverse (S.M t t) else 1
    let K := kMat (pivotMatrix (revPivots d rank))
      (rev d * S.U * rev d * rev d * (S.L * diagonal δ)) * diagonal (fun t => inv t * δ' t)
    let reciprocal := Ring.inverse (S.M k k)
    let bank := shear.trans host
    let ports := fun sign => (coeff sign).trans host
    let signed := fun sign : Bool => binSyms (A := A) H (if sign then -reciprocal else reciprocal).val
    let ready := HeadColumnReady (ports negative) bank H J (matrixWords A H N ++ tail)
      ((List.ofFn fun t => binSyms H (inv t).val).flatten ++ rest) (signed negative)
      sym source dest p q (M := M) (d := d+d) (W := W)
    let ops := fun src (ts : List (Fin d)) => ts.map fun t => let e := crossPair src k t
                                                              crossEntryShear (if negative then -K else K) e.1 e.2
    let cost := fun src (ts : List (Fin d)) => (ts.map fun t => let e := crossPair src k t
                                                               crossShearTime body (ports (if src then negative else !negative))
                                                                 bank e.1 e.2 M W H J).sum+1
    ∀ ts : List (Fin d), (∀ t ∈ ts, rank ≤ t.val) → ∀ v S word, ready word S →
      S.R (ports (!negative) 14) = signed (!negative) →
      ∃ z F n out, z.user = v.user ∧ n ≤ cost true ts + cost false ts ∧
        Exec body (crossPivotGroups negative k host ts) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ b, bank b ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ x l, out (index ((ops true ts ++ ops false ts).foldl (fun y op => op.apply y) x) l) = word (index x l) := by
  intro k N stage δ δ' K reciprocal bank ports signed ready ops cost ts inactive v S word initial other
  have disjoint (sign : Bool) (j : Fin 17) (ne : j ≠ 15) (b : Fin 29) :
      bank b ≠ ports sign j := host.injective.ne (apart sign j ne b)
  have run (src : Bool) := crossGroup_exec body (ports (if src then negative else !negative)) bank
    (congrArg host (shared _)) (disjoint _) G rank hr minor idem L R factor inv a src negative H J hm hw hW
    tail rest sym source dest p q empty ts inactive
  obtain ⟨u,D,t,mid,hu,ht,left,next,frame,first⟩ := run true v S word initial
  have alt := changeReciprocal host negative (!negative) H J _ _ _ _ sym source dest p q mid D next
    ((frame _ (disjoint _ 14 (by decide))).2.trans other)
  obtain ⟨z,F,n,out,hz,hn,right,done,saved,last⟩ := run false u D mid alt
  have back := changeReciprocal host (!negative) negative H J _ _ _ _ sym source dest p q out F done
    ((saved _ (disjoint _ 14 (by decide))).2.trans next.reciprocal)
  refine ⟨z,F,t+n,out,hz.trans hu,Nat.add_le_add ht hn,Exec.seq left right,back,?_,?_⟩
  · intro j hj
    exact ⟨(saved j hj).1.trans (frame j hj).1,(saved j hj).2.trans (frame j hj).2⟩
  · intro x l
    rw [List.foldl_append]
    exact (last _ l).trans (first x l)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
