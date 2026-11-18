module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackUpdateMatrix
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotInverse

/-! Clear a complete column starting from a packed matrix and its specified unit pivot. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.ShortConv
variable {T Q A d : ℕ} {P U : Type}

def columnReadPorts : Fin 7 ↪ Fin 22 := ⟨![3,2,15,19,4,5,6],by decide⟩
def columnInversePorts : Fin 16 ↪ Fin 22 := ⟨![17,1,0,3,2,5,6,7,8,9,10,11,12,13,19,20],by decide⟩

def column (p : ℕ) (k pivot : Fin d) (r : Fin 22 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord (pivot.val*d+k.val) (columnReadPorts.trans r))
    (.seq (pivotInverse p (columnInversePorts.trans r) (r 21))
      (.seq (updateMatrix k pivot ((Fin.castLEEmb (by decide)).trans r)) (clearWords [r 17,r 19])))

def columnTime (d p w H : ℕ) :=
  let C := 48*H*H+152*H+66
  8*(d*d*H)+32*H+44+(p-2)*C+C+w*(12*H+15+p*C)+d*((d+1)*entryTime d H)

theorem column_exec (body : P → Pr P T Q A U) (r : Fin 22 ↪ Fin T) (p w H : ℕ) (hp : p.Prime)
    [NeZero (p^(w+1))] (m : Matrix (Fin d) (Fin d) (ZMod (p^(w+1)))) (k pivot : Fin d)
    (unit : IsUnit (m pivot k)) (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A)
    (tail : List (Fin (A+4))) (matrix : S.R (r 15) = matrixWords A H m ++ tail)
    (modulus : S.R (r 2) = binSyms H (p^(w+1)))
    (one : S.R (r 20) = binSyms H (1 : ZMod (p^(w+1))).val) (ticks : (S.R (r 21)).length = w)
    (free : ∀ i : Fin 22, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) → S.R (r i) = []) :
    let output := matrixWords A H (clearColumn p w k pivot m) ++ S.R (r 16)
    ∃ z n, z.user = v.user ∧ n ≤ columnTime d p w H ∧ Exec body (column p k pivot r) (mk v S) n
      (mk z {S with R := Function.update (Function.update S.R (r 21) []) (r 16) output}) := by
  have rp : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i → columnReadPorts i < 15 ∧ columnReadPorts i ≠ 2 := by decide
  obtain ⟨u,hu,read⟩ := readMatrixWord_exec body (columnReadPorts.trans r) m pivot k H v S tail matrix
    (by change (S.R (r 2)).length = H; simp [modulus,length_binSyms]) (fun i h => free _ (.inl (rp i h)))
  change Exec _ _ _ _ (mk u {S with R := Function.update S.R (r 19) (_ ++ S.R (r 19))}) at read
  rw [free 19 (by decide),List.append_nil] at read
  let D : Stacks T A := {S with R := Function.update S.R (r 19) (binSyms H (m pivot k).val)}
  have keep (i : Fin 22) (h : i ≠ 19) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) _ _
  have ip : ∀ i : Fin 16, i ≠ 4 → i < 13 → columnInversePorts i ≠ 19 ∧
      ((columnInversePorts i < 15 ∧ columnInversePorts i ≠ 2) ∨ (17 ≤ columnInversePorts i ∧ columnInversePorts i ≤ 19)) := by decide
  have outside : ∀ i, columnInversePorts i ≠ 21 := by decide
  obtain ⟨y,F,l,hy,hl,inv,empty,word,hL,hin,hout,frame⟩ := pivotInverse_exec body p w hp (m pivot k) unit
    (columnInversePorts.trans r) (r 21) (fun i => r.injective.ne (outside i)) H hm u D
    (by rw [keep 21 (by decide),ticks]) (by change D.R (r 19) = _; simp [D])
    ((keep 20 (by decide)).trans one) ((keep 2 (by decide)).trans modulus)
    (fun i h j => (keep _ (ip i h j).1).trans (free _ (ip i h j).2))
  have kept (i : Fin 22) (h : i ≠ 17) (h' : i ≠ 21) : F.R (r i) = D.R (r i) :=
    frame _ (r.injective.ne h) (r.injective.ne h')
  let bank : Fin 19 ↪ Fin 22 := Fin.castLEEmb (by decide)
  obtain ⟨z,n,hz,hn,update⟩ := updateMatrix_exec body (bank.trans r) p w m k pivot H hm y F tail
    ((kept 15 (by decide) (by decide)).trans ((keep 15 (by decide)).trans matrix))
    ((kept 2 (by decide) (by decide)).trans ((keep 2 (by decide)).trans modulus))
    (by rw [pivotReciprocal_eq hp w _ unit]; exact word) (by
      intro i h
      have hi : (bank i).val = i.val := rfl
      have a : bank i ≠ 17 ∧ bank i ≠ 21 ∧ bank i ≠ 19 := by
        refine ⟨?_,?_,?_⟩ <;> intro e <;> have q := congrArg Fin.val e <;> simp [bank] at q <;> omega
      exact (kept _ a.1 a.2.1).trans ((keep _ a.2.2).trans (free _ (by
        rcases h with ⟨lo,h2⟩ | eq
        · exact .inl ⟨lo,fun e => h2 (bank.injective e)⟩
        · subst i; decide))))
  let output := matrixWords A H (clearColumn p w k pivot m) ++ S.R (r 16)
  have outReg := (kept 16 (by decide) (by decide)).trans (keep 16 (by decide))
  change Exec _ _ _ _ (mk z {F with R := Function.update F.R (r 16) (_ ++ F.R (r 16))}) at update
  rw [outReg] at update
  let E : Stacks T A := {F with R := Function.update F.R (r 16) output}
  obtain ⟨z',hz',clear⟩ := clearWords_exec (body := body) [r 17,r 19] (by simp [r.injective.eq_iff]) z E
  have pivotWord : F.R (r 19) = binSyms H (m pivot k).val := (kept 19 (by decide) (by decide)).trans (by simp [D])
  change F.R (r 17) = _ at word
  simp [E,r.injective.eq_iff,word,pivotWord,length_binSyms] at clear
  refine ⟨z',_,hz'.trans (hz.trans (hy.trans hu)),?_,(Exec.seq read (Exec.seq inv (Exec.seq update clear))).cast rfl ?_⟩
  · have := matrixOffset_le H pivot k
    dsimp [columnTime]
    omega
  · congr 1
    refine Stacks.ext hin hout hL ?_
    funext i
    by_cases a : i = r 16
    · subst i; simp [output,r.injective.eq_iff]
    by_cases b : i = r 21
    · subst i; simp [empty,r.injective.eq_iff]
    by_cases c : i = r 17
    · subst i; simp [free 17 (by decide),r.injective.eq_iff]
    by_cases e : i = r 19
    · subst i; simp [free 19 (by decide),r.injective.eq_iff]
    simp [a,b,c,e,frame i c b,D]

open Node

/-- Borrow the width counter so the following column can use the same inputs. -/
def itineraryColumn (p : ℕ) (k pivot : Fin d) (r : Fin 23 ↪ Fin T) : Pr P T Q A U :=
  .seq (ucopy (r 22) (r 21) (r 0)) (column p k pivot ((Fin.castLEEmb (by decide)).trans r))

theorem itineraryColumn_exec (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T) (p w H : ℕ) (hp : p.Prime)
    [NeZero (p^(w+1))] (m : Matrix (Fin d) (Fin d) (ZMod (p^(w+1)))) (k pivot : Fin d)
    (unit : IsUnit (m pivot k)) (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A)
    (tail : List (Fin (A+4))) (matrix : S.R (r 15) = matrixWords A H m ++ tail)
    (modulus : S.R (r 2) = binSyms H (p^(w+1)))
    (one : S.R (r 20) = binSyms H (1 : ZMod (p^(w+1))).val) (ticks : (S.R (r 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ 4*w+4+columnTime d p w H ∧ Exec body (itineraryColumn p k pivot r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 16) (matrixWords A H (clearColumn p w k pivot m) ++ S.R (r 16))}) := by
  obtain ⟨u,hu,copy⟩ := ucopy_exec body (a := r 22) (b := r 21) (t := r 0)
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide)) v S (free 0 (by decide))
  rw [ticks,free 21 (by decide),List.append_nil] at copy
  let D : Stacks T A := {S with R := Function.update S.R (r 21) (List.replicate w tick)}
  have keep (i : Fin 23) (hi : i ≠ 21) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne hi) _ _
  let bank : Fin 22 ↪ Fin 23 := Fin.castLEEmb (by decide)
  obtain ⟨z,n,hz,hn,run⟩ := column_exec body (bank.trans r) p w H hp m k pivot unit hm u D tail
    ((keep 15 (by decide)).trans matrix) ((keep 2 (by decide)).trans modulus) ((keep 20 (by decide)).trans one)
    (by change (D.R (r 21)).length = w; simp [D]) (by
      intro i h
      apply (keep (bank i) _).trans (free _ _)
      · intro e; have q := congrArg Fin.val e; change i.val = 21 at q; omega
      · rcases h with ⟨lo,h2⟩ | h
        · exact .inl ⟨lo,fun e => h2 (bank.injective e)⟩
        · exact .inr (.inl h))
  refine ⟨z,_,hz.trans hu,Nat.add_le_add_left hn _,(Exec.seq copy run).cast rfl ?_⟩
  change mk z {D with R := Function.update (Function.update D.R (r 21) []) (r 16) (_ ++ D.R (r 16))} = _
  rw [keep 16 (by decide)]
  simp [D,Function.update_idem,← free 21 (by decide)]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
