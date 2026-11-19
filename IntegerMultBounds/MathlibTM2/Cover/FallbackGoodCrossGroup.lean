module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCrossShear

/-! Execute all mixed entries sharing a pivot and reciprocal sign. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout LabelTraversal GoodForm Matrix
open M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear
variable {P U α : Type} {T A d M W : ℕ} [NeZero M]

def crossPair (sourcePivot : Bool) (k t : Fin d) : Fin d × Fin d :=
  if sourcePivot then (t.rev,k) else (k.rev,t)

def crossGroup (sourcePivot : Bool) (k : Fin d) (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) :
    List (Fin d) → Pr P T 217 A U
  | [] => .act .done
  | t :: ts =>
    let e := crossPair sourcePivot k t
    .seq (cleanCrossShear e.1 e.2 coeff bank) (crossGroup sourcePivot k coeff bank ts)

theorem crossGroup_exec [Fintype P] (body : P → Pr P T 217 A U)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (shared : coeff 15 = bank 0)
    (apart : ∀ t : Fin 17, t ≠ 15 → ∀ b, bank b ≠ coeff t)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ t (ht : t < rank), IsUnit (lead (t+1) (lt_of_lt_of_le ht hr) G).det)
    (idem : G*G = G) (L : Matrix (Fin d) (Fin rank) (ZMod M)) (R : Matrix (Fin rank) (Fin d) (ZMod M))
    (factor : G = L*R) (inv : Fin d → ZMod M) (a : Fin rank) (sourcePivot negative : Bool)
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
    let signed := if (if sourcePivot then negative else !negative) then -reciprocal else reciprocal
    let ready := HeadColumnReady coeff bank H J (matrixWords A H N ++ tail)
      ((List.ofFn fun t => binSyms H (inv t).val).flatten ++ rest) (binSyms H signed.val)
      sym source dest p q (M := M) (d := d+d) (W := W)
    let op := fun t => let e := crossPair sourcePivot k t
                       crossEntryShear (if negative then -K else K) e.1 e.2
    let cost := fun t => let e := crossPair sourcePivot k t
                         crossShearTime body coeff bank e.1 e.2 M W H J
    ∀ ts : List (Fin d), (∀ t ∈ ts, rank ≤ t.val) → ∀ v S word, ready word S →
      ∃ y E n out, y.user = v.user ∧ n ≤ (ts.map cost).sum+1 ∧
        Exec body (crossGroup sourcePivot k coeff bank ts) (mk v S) n (mk y E) ∧ ready out E ∧
        (∀ z, (∀ b, bank b ≠ z) → E.L z = S.L z ∧ E.R z = S.R z) ∧
        ∀ x l, out (index ((ts.map op).foldl (fun z o => o.apply z) x) l) = word (index x l) := by
  intro k N stage δ δ' K reciprocal signed ready op cost ts
  induction ts with
  | nil =>
    intro _ v S word h
    exact ⟨v,S,1,word,rfl,by simp,Exec.act _ _,h,fun _ _ => ⟨rfl,rfl⟩,fun _ _ => rfl⟩
  | cons t ts ih =>
    intro outside v S word h
    have inactive := outside t List.mem_cons_self
    let e := crossPair sourcePivot k t
    have active : k.val < rank := a.isLt
    have mixed : e.1.rev.val < rank ↔ ¬ e.2.val < rank := by
      cases sourcePivot <;> simp [e,crossPair,active,not_lt_of_ge inactive]
    let selected : Fin rank := ⟨(if e.2.val < rank then e.2 else e.1.rev).val,by split <;> omega⟩
    have eq : selected = a := by
      apply Fin.ext
      cases sourcePivot <;> simp [selected,e,crossPair,not_lt_of_ge inactive,k]
    have stageEq := congrArg (fun b : Fin rank => (stageAt G rank hr minor b.val b.isLt.le).M) eq
    have portEq := congrArg (fun b : Fin rank => b.castLE hr) eq
    have signEq : (if e.2.val < rank then negative else !negative) =
        (if sourcePivot then negative else !negative) := by
      cases sourcePivot <;> simp [e,crossPair,active,not_lt_of_ge inactive]
    have step := cleanCrossShear_exec body coeff bank shared apart G rank hr minor idem L R factor inv
      e.1 e.2 mixed negative H J hm hw hW tail rest sym source dest p q empty
    dsimp only at step
    change (stageAt G rank hr minor (if e.2.val < rank then e.2 else e.1.rev).val _).M = N at stageEq
    change (if e.2.val < rank then e.2 else e.1.rev) = k at portEq
    rw [stageEq,portEq,signEq] at step
    obtain ⟨u,D,n,mid,hu,hn,run,next,frame,effect⟩ := step v S word h
    obtain ⟨y,E,m,out,hy,hm',more,done,saved,act⟩ := ih (fun j hj => outside j (List.mem_cons_of_mem _ hj)) u D mid next
    refine ⟨y,E,n+m,out,hy.trans hu,?_,Exec.seq run more,done,?_,?_⟩
    · have bound : n ≤ cost t := hn
      simpa [Nat.add_assoc] using Nat.add_le_add bound hm'
    · intro j hj
      exact ⟨(saved j hj).1.trans (frame j hj).1,(saved j hj).2.trans (frame j hj).2⟩
    · intro x l
      exact (act ((op t).apply x) l).trans (effect x l)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
