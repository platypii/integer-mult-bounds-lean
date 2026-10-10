import IntegerMultBounds.Machine.BlankWordPairRecycle

/-! A fixed all-port recycler restores every original stream head, installs its
computed equal-width output, and erases every private output stream. An
arbitrary appended caller frame is retained exactly. -/
namespace IntegerMultBounds.Machine.BlankWordPairRecycleBank
noncomputable section
open RadixLinearCombinationBootstrap (empty)
variable {c u a : ℕ}

abbrev count (c u : ℕ) := c+(c+u)
def source (i : Fin c) : Fin (count c u) := Fin.castAdd (c+u) i
def dest (i : Fin c) : Fin (count c u) := Fin.natAdd c (Fin.castAdd u i)

theorem distinct (i : Fin c) : source (u:=u) i≠dest i := by
  intro h
  have hv := congrArg Fin.val h
  have := i.isLt
  dsimp [source,dest] at hv
  omega

def bank (xs ys : Fin c → List (Fin (a+4))) (done : Finset (Fin c)) (tail : Tapes u a) :
    Tapes (count c u) a :=
  (⟨fun i => if i∈done then 0 else (xs i).length,
    fun i => putWord (fun _ => blank) 0 (if i∈done then ys i else xs i)⟩ : Tapes c a).append
    ((⟨fun i => if i∈done then 0 else (ys i).length,
      fun i => if i∈done then (fun _ => blank) else putWord (fun _ => blank) 0 (ys i)⟩ : Tapes c a).append tail)

def output (ys : Fin c → List (Fin (a+4))) (tail : Tapes u a) :=
  (⟨fun _ => 0,fun i => putWord (fun _ => blank) 0 (ys i)⟩ : Tapes c a).append ((empty c).append tail)

def placement (hc : 0<c) (i : Fin c) :=
  WordBankCleanup.pairPlace (source (u:=u) i) (dest i) (distinct i) (by unfold count; omega)

def oneProgram (hc : 0<c) (i : Fin c) : Program (count c u) 17 a :=
  Placement.placed (BlankWordPairRecycle.program a) (placement hc i)

private theorem active_before (hc : 0<c) (xs ys : Fin c → List (Fin (a+4)))
    (done : Finset (Fin c)) (tail : Tapes u a) (i : Fin c) (hi : i∉done) :
    Placement.active (placement hc i) (bank xs ys done tail)=BlankWordPairRecycle.input (xs i) (ys i) := by
  rw [placement,WordBankCleanup.pair_active]
  simp only [bank,source,dest,Tapes.append,Fin.addCases_left,Fin.addCases_right,ite_eq_right_iff.mpr (fun h => (hi h).elim)]
  rfl

private theorem active_after (hc : 0<c) (xs ys : Fin c → List (Fin (a+4)))
    (done : Finset (Fin c)) (tail : Tapes u a) (i : Fin c) :
    Placement.active (placement hc i) (bank xs ys (insert i done) tail)=BlankWordPairRecycle.output (ys i) := by
  rw [placement,WordBankCleanup.pair_active]
  simp only [bank,source,dest,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    Finset.mem_insert_self,ite_true]
  rfl

private theorem bank_frame (xs ys : Fin c → List (Fin (a+4)))
    (done : Finset (Fin c)) (tail : Tapes u a) (i : Fin c) (k : Fin (count c u))
    (hs : k≠source i) (hd : k≠dest i) :
    (bank xs ys (insert i done) tail).head k=(bank xs ys done tail).head k ∧
      (bank xs ys (insert i done) tail).tape k=(bank xs ys done tail).tape k := by
  induction k using Fin.addCases with
  | left k =>
    have hk : k≠i := by intro h; subst k; exact hs rfl
    simp only [bank,Tapes.append,Fin.addCases_left,Finset.mem_insert,hk,false_or]
    exact ⟨True.intro,True.intro⟩
  | right k =>
    induction k using Fin.addCases with
    | left k =>
      have hk : k≠i := by intro h; subst k; exact hd rfl
      simp only [bank,Tapes.append,Fin.addCases_right,Fin.addCases_left,Finset.mem_insert,hk,false_or]
      exact ⟨True.intro,True.intro⟩
    | right k => simp only [bank,Tapes.append,Fin.addCases_right,and_self]

private theorem extra_eq (hc : 0<c) (xs ys : Fin c → List (Fin (a+4)))
    (done : Finset (Fin c)) (tail : Tapes u a) (i : Fin c) :
    Placement.extra (placement hc i) (bank xs ys (insert i done) tail)=
      Placement.extra (placement hc i) (bank xs ys done tail) := by
  have hslot (j : Fin 2) : placement (u:=u) hc i (Fin.castAdd (count c u-2) j)=
      WordBankCleanup.pairSlot (source i) (dest i) j :=
    InjectivePlacement.active_slot _ _ _ j
  apply Placement.Tapes.ext'
  all_goals
    intro k
    have hn (j : Fin 2) : placement (u:=u) hc i (Fin.natAdd 2 k)≠
        WordBankCleanup.pairSlot (source i) (dest i) j := by
      rw [← hslot j]
      intro h
      have hv := congrArg Fin.val ((placement hc i).injective h)
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      have := j.isLt
      omega
    have h := bank_frame xs ys done tail i (placement hc i (Fin.natAdd 2 k)) (hn 0) (hn 1)
    first | exact h.1 | exact h.2

private theorem one_runs (hc : 0<c) (xs ys : Fin c → List (Fin (a+4)))
    (done : Finset (Fin c)) (tail : Tapes u a) (i : Fin c) (hi : i∉done)
    (hlen : (xs i).length=(ys i).length)
    (hx : ∀ x∈xs i,x≠blank) (hy : ∀ y∈ys i,y≠blank) :
    HoareTime (oneProgram hc i) (fun v => v=bank xs ys done tail)
      (fun v => v=bank xs ys (insert i done) tail) (7*(ys i).length+16) := by
  have h := Placement.hoare_at (BlankWordPairRecycle.runs (xs i) (ys i) hlen hx hy)
    (placement hc i) (bank xs ys done tail) (active_before hc xs ys done tail i hi)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,← extra_eq hc xs ys done tail i,← active_after hc xs ys done tail i]
  exact Placement.view _ _

def states : List (Fin c) → ℕ
  | [] => 1
  | _::ops => 17+states ops

def compile (hc : 0<c) : (ops : List (Fin c)) → Program (count c u) (states ops) a
  | [] => skip (count c u) a (by unfold count; omega)
  | i::ops => seq (oneProgram hc i) (compile hc ops)

def cost (ops : List (Fin c)) (ys : Fin c → List (Fin (a+4))) :=
  (ops.map (fun i => 7*(ys i).length+17)).sum

private theorem list_runs (hc : 0<c) (ops : List (Fin c)) (hu : ops.Nodup)
    (xs ys : Fin c → List (Fin (a+4))) (done : Finset (Fin c))
    (hd : ∀ i∈ops,i∉done) (tail : Tapes u a)
    (hlen : ∀ i,(xs i).length=(ys i).length)
    (hx : ∀ i x,x∈xs i → x≠blank) (hy : ∀ i y,y∈ys i → y≠blank) :
    HoareTime (compile hc ops) (fun v => v=bank xs ys done tail)
      (fun v => v=bank xs ys (ops.toFinset∪done) tail) (cost ops ys) := by
  induction ops generalizing done with
  | nil => simpa only [compile,states,cost,List.map_nil,List.sum_nil,List.toFinset_nil,Finset.empty_union] using skip_hoare (by unfold count; omega : 0<count c u) (bank xs ys done tail)
  | cons i ops ih =>
    have hh := List.nodup_cons.mp hu
    have h0 := one_runs hc xs ys done tail i (hd i List.mem_cons_self) (hlen i) (hx i) (hy i)
    have h1 := ih hh.2 (insert i done) (by
      intro j hj
      simp only [Finset.mem_insert,not_or]
      exact ⟨fun he => hh.1 (he ▸ hj),hd j (List.mem_cons_of_mem _ hj)⟩)
    have he : ops.toFinset∪insert i done=(i::ops).toFinset∪done := by ext j; simp [or_comm]
    rw [he] at h1
    exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
      (by simp only [cost,List.map_cons,List.sum_cons]; omega)

def program (hc : 0<c) := compile (a:=a) (u:=u) hc (List.finRange c)

theorem runs (hc : 0<c) (xs ys : Fin c → List (Fin (a+4))) (tail : Tapes u a)
    (L : ℕ) (hxlen : ∀ i,(xs i).length=L) (hylen : ∀ i,(ys i).length=L)
    (hx : ∀ i x,x∈xs i → x≠blank) (hy : ∀ i y,y∈ys i → y≠blank) :
    HoareTime (program (a:=a) (u:=u) hc) (fun v => v=bank xs ys ∅ tail)
      (fun v => v=output ys tail) (c*(7*L+17)) := by
  have h := list_runs hc (List.finRange c) (List.nodup_finRange c) xs ys ∅
    (by simp) tail (fun i => (hxlen i).trans (hylen i).symm) hx hy
  have he : bank xs ys ((List.finRange c).toFinset∪∅) tail=output ys tail := by
    simp only [List.toFinset_finRange,Finset.union_empty,bank,Finset.mem_univ,ite_true,output]
    rfl
  have hcost : cost (List.finRange c) ys=c*(7*L+17) := by
    simp [cost,hylen]
  exact h.consequence (fun _ h => h) (fun _ h => h.trans he) hcost.le

end
end IntegerMultBounds.Machine.BlankWordPairRecycleBank
