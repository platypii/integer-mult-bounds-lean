module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairWeights

/-! Use either coefficient of an archived reciprocal pair for a physical payload shear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def pairShearPorts (inverse : Bool) (negative : Bool := false) : Fin 29 ↪ Fin 35 :=
  (Fin.castLEEmb (by decide)).trans (Equiv.swap 0 (if negative then 29 else if inverse then 30 else 31)).toEmbedding

def pairShear (b : ℕ) (i k t : Fin d) (inverse : Bool) (bank : Fin 35 ↪ Fin T) (negative : Bool := false) (useOne : Bool := false) : Pr P T 217 A U :=
  .seq (if negative then loadSignedPairWeights b i bank useOne else if useOne then loadOnePair bank else loadPairWeights b i bank) (embProg ((pairShearPorts inverse negative).trans bank) Empty.elim (weightedShear k t (Function.Embedding.refl _)))

theorem pairShear_exec (body : P → Pr P T 217 A U) (i k t : Fin d) (hk : k < t) (inverse : Bool)
    (bank : Fin 35 ↪ Fin T) (a : Fin d → ZMod M) (unit : IsUnit (a i)) (hb : b.Prime) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W) (v : HS T 217 A U) (S : Stacks T A)
    (tail : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (word : Fin (M^d*W) → α) (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (ready : ShearReady bank H J (Matrix.diagonal a) tail sym source dest p q word S) (negative : Bool := false) (useOne : Bool := false) :
    let weight := if useOne then 1 else a i
    let c := if negative then -Ring.inverse weight else if inverse then Ring.inverse weight else weight
    let C := 48*H*H+152*H+66
    ∃ z F n, z.user = v.user ∧ n ≤ (8*((i.val*d+i.val)*H)+14*H+22) +
      (6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C))) + (if negative then 8*H+8 else 0) + weightedShearTime k t M W H J ∧
      Exec body (pairShear b i k t inverse bank negative useOne) (mk v S) n (mk z F) ∧
      F.R (bank 2) = S.R (bank 2) ∧ F.R (bank 27) = S.R (bank 27) ∧ F.R (bank 28) = S.R (bank 28) ∧
      (∀ j : Fin 35, 32 ≤ j → F.R (bank j) = S.R (bank j)) ∧
      (∀ pos, readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-q) = RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∃ out : Fin (M^d*W) → α, (∀ pos, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ out)) pos)) ∧
        ∀ x j, out (index ((RowOp.shear k t hk c).apply x) j) = word (index x j) := by
  intro weight c C
  let loaded := Function.update (Function.update S.R (bank 31) (binSyms H weight.val)) (bank 30) (binSyms H (Ring.inverse weight).val)
  let D := {S with R := if negative then Function.update loaded (bank 29) (binSyms H (-Ring.inverse weight).val) else loaded}
  have loadRun : ∃ u l, u.user = v.user ∧ l ≤ (8*((i.val*d+i.val)*H)+14*H+22) +
      (6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C))) + (if negative then 8*H+8 else 0) ∧
      Exec body (if negative then loadSignedPairWeights b i bank useOne else if useOne then loadOnePair bank else loadPairWeights b i bank) (mk v S) l (mk u D) := by
    cases negative
    · cases useOne
      · simpa [D,loaded,C,weight] using loadPairWeights_exec body i bank a unit hb H J hm v S tail sym source dest p q word ready
      · obtain ⟨u,hu,run⟩ := loadOnePair_exec body bank H v S ready.padded (fun j hj => (ready.scratch j hj).2)
        exact ⟨u,2*(6*H+6),hu,by simp only [Bool.false_eq_true,ite_false,Nat.add_zero]; omega,by simpa [D,loaded,weight] using run⟩
    · exact loadSignedPairWeights_exec body i bank a unit hb H J hm v S tail sym source dest p q word ready useOne
  obtain ⟨u,l,hu,hl,load⟩ := loadRun
  let ports := (pairShearPorts inverse negative).trans bank
  have fixed : ∀ j : Fin 29, j ≠ 0 → pairShearPorts inverse negative j = j.castLE (by decide) := by cases negative <;> cases inverse <;> decide
  have keep (j : Fin 29) (hj : j ≠ 0) : D.R (ports j) = S.R (bank (j.castLE (by decide))) := by
    have off : ∀ j : Fin 29, j.castLE (by decide : 29 ≤ 35) ≠ 30 ∧ j.castLE (by decide : 29 ≤ 35) ≠ 31 := by decide
    have off29 : ∀ j : Fin 29, j.castLE (by decide : 29 ≤ 35) ≠ 29 := by decide
    cases negative <;> simp only [D,loaded,ite_true,ite_false,Bool.false_eq_true,Function.update_of_ne (bank.injective.ne (off29 j)),ports,Function.Embedding.trans_apply,fixed j hj,Function.update_of_ne (bank.injective.ne (off j).1),
      Function.update_of_ne (bank.injective.ne (off j).2)]
  have srcPort : (24 : Fin 29).castLE (by decide : 29 ≤ 35) = 24 := by decide
  have dstPort : (25 : Fin 29).castLE (by decide : 29 ≤ 35) = 25 := by decide
  have coef : D.R (ports 0) = binSyms H c.val := by
    cases negative <;> cases inverse <;> simp [D,loaded,ports,c,pairShearPorts,bank.injective.eq_iff]
  have free : ∀ j : Fin 29, 1 ≤ j → j ≤ 26 → j ≠ 2 → j ≠ 24 → j ≠ 25 → j.castLE (by decide : 29 ≤ 35) ∈ shearWork := by decide
  have left : ∀ j : Fin 12, j < 10 → shearTranslation j ≠ 0 ∧ (shearTranslation j).castLE (by decide : 29 ≤ 35) ∈ shearWork := by decide
  obtain ⟨z,F,n,hz,hn,run,post⟩ := weightedShear_exec k t hk sym c (P := Empty) Empty.elim (Function.Embedding.refl _) H J hm hw hW (embDn ports u) (embStk ports D)
    ((keep 2 (by decide)).trans ready.modulus) ((keep 28 (by decide)).trans ready.one)
    ((keep 27 (by decide)).trans ready.width) coef
    (fun j lo hi h2 h24 h25 => (keep j (by omega)).trans (ready.scratch _ (free j lo hi h2 h24 h25)).2)
    (fun j hj => by simpa only [embStk_L,Function.Embedding.refl_apply,D,ports,Function.Embedding.trans_apply,fixed _ (left j hj).1] using (ready.scratch _ (left j hj).2).1)
    source dest p q word empty
    (fun pos => by change _ = readAt blank (D.L (ports 24)) (D.R (ports 24)) _; rw [keep 24 (by decide)]; simpa only [D,ports,Function.Embedding.trans_apply,fixed 24 (by decide),srcPort] using (ready.src pos).symm)
    (fun pos => by change _ = readAt blank (D.L (ports 25)) (D.R (ports 25)) _; rw [keep 25 (by decide)]; simpa only [D,ports,Function.Embedding.trans_apply,fixed 25 (by decide),dstPort] using (ready.dst pos).symm)
  obtain ⟨y,G,embedded,_,hy,eq,frame⟩ := exec_emb (body' := body) (ι := Empty.elim)
    ports.injective (fun e => nomatch e) run u rfl D rfl
  rw [← eq] at post
  obtain ⟨modulus,headers,clean,out,result,placed⟩ := post
  have archive (j : Fin 35) (hj : 32 ≤ j) : G.R (bank j) = S.R (bank j) := by
    have off : ∀ i, pairShearPorts inverse negative i ≠ j := by
      exact (by decide : ∀ x y (j : Fin 35), 32 ≤ j → ∀ i, pairShearPorts x y i ≠ j) _ _ j hj
    have saved := (frame (bank j) (fun i => bank.injective.ne (off i))).2
    have h29 : j ≠ 29 := by omega
    have h30 : j ≠ 30 := by omega
    have h31 : j ≠ 31 := by omega
    cases negative <;> simpa [D,loaded,Function.update_of_ne (bank.injective.ne h29),
      Function.update_of_ne (bank.injective.ne h30),Function.update_of_ne (bank.injective.ne h31)] using saved
  have portEq (j : Fin 29) (hj : j ≠ 0) : ports j = bank (j.castLE (by decide)) := congrArg bank (fixed j hj)
  exact ⟨y,G,l+n,hy.trans (hz.trans hu),Nat.add_le_add hl hn,Exec.seq load embedded,
    by simpa only [embStk_R,Function.Embedding.refl_apply,portEq 2 (by decide),show (2 : Fin 29).castLE (by decide : 29 ≤ 35) = 2 by decide] using modulus.trans (keep 2 (by decide)),
    by simpa only [embStk_R,Function.Embedding.refl_apply,portEq 27 (by decide),show (27 : Fin 29).castLE (by decide : 29 ≤ 35) = 27 by decide] using (headers 27 (by decide)).trans (keep 27 (by decide)),
    by simpa only [embStk_R,Function.Embedding.refl_apply,portEq 28 (by decide),show (28 : Fin 29).castLE (by decide : 29 ≤ 35) = 28 by decide] using (headers 28 (by decide)).trans (keep 28 (by decide)),archive,
    by simpa only [embStk_L,embStk_R,Function.Embedding.refl_apply,ports,Function.Embedding.trans_apply,fixed 25 (by decide),dstPort] using clean,out,
    by simpa only [embStk_L,embStk_R,Function.Embedding.refl_apply,ports,Function.Embedding.trans_apply,fixed 24 (by decide),srcPort] using result,placed⟩

def childLoadPorts : Fin 20 ↪ Fin 36 := ⟨![30,1,3,4,2,5,6,7,8,9,10,11,29,13,31,32,33,17,34,35],by decide⟩

def childShearPorts (negative : Bool) : Fin 29 ↪ Fin 36 :=
  (Fin.castLEEmb (by decide)).trans (Equiv.swap 0 (if negative then 29 else 31)).toEmbedding

def childShear {m : ℕ} (p parentIndex index : ℕ) (k t : Fin m) (negative : Bool) (bank : Fin 36 ↪ Fin T) : Pr P T 217 A U :=
  .seq (signedChildPair p parentIndex index (childLoadPorts.trans bank))
    (embProg ((childShearPorts negative).trans bank) Empty.elim (weightedShear k t (Function.Embedding.refl _)))

theorem childShear_exec {n m : ℕ} (k t : Fin m) (hk : k < t) (negative : Bool) (body : P → Pr P T 217 A U) (bank : Fin 36 ↪ Fin T)
    (parent : Fin n → ZMod M) (j : Fin n) (inv : ZMod M) (reciprocal : parent j * inv = 1)
    (pivot : Fin d → ZMod M) (i : Fin d) (unit : IsUnit (pivot i)) (hb : b.Prime)
    (H : ℕ) (hm : M < 2^H) (v : HS T 217 A U) (S : Stacks T A) (tail rest : List (Fin (A+4)))
    (weights : S.R (bank 35) = (List.ofFn fun k => binSyms H (parent k).val).flatten ++ rest)
    (record : S.R (bank 34) = (List.ofFn fun k => binSyms H (pivot k).val).flatten ++ tail)
    (modulus : S.R (bank 2) = binSyms H M) (one : S.R (bank 32) = binSyms H (1 : ZMod M).val)
    (clock : (S.R (bank 33)).length = w)
    (J : ℕ) (hw : W < 2^J) (hW : 0 < W) (width : S.R (bank 27) = binSyms J W)
    (single : S.R (bank 28) = binSyms 1 1)
    (free : ∀ i : Fin 36, (i ≤ 26 ∧ i ≠ 2 ∧ i ≠ 24 ∧ i ≠ 25) ∨ (29 ≤ i ∧ i ≤ 31) → S.R (bank i) = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (bank ((shearTranslation i).castLE (by decide))) = [])
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^m*W) → α)
    (empty : ∀ z, q ≤ z → z < q+(M^m*W : ℕ) → dest z = blank)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ a)) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    let C := 48*H*H+152*H+66
    let c := if negative then -(inv * Ring.inverse (pivot i)) else parent j * pivot i
    ∃ z F l, z.user = v.user ∧ l ≤ (8*(j.val*H)+14*H+22) +
      ((8*(i.val*H)+48*H*H+166*H+88)+(6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C)))) +
      (2*H+2) + (8*H+8) + weightedShearTime k t M W H J ∧
      Exec body (childShear b j.val i.val k t negative bank) (mk v S) l (mk z F) ∧
      (∀ j : Fin 36, j = 2 ∨ j = 27 ∨ j = 28 ∨ 32 ≤ j → F.R (bank j) = S.R (bank j)) ∧
      (∀ z, readAt blank (F.L (bank 25)) (F.R (bank 25)) (z-q) = RadixToBinary.binaryEncoding.encode (dest z)) ∧
      ∃ out : Fin (M^m*W) → α, (∀ z, readAt blank (F.L (bank 24)) (F.R (bank 24)) (z-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ out)) z)) ∧
        ∀ x h, out (index ((RowOp.shear k t hk c).apply x) h) = a (index x h) := by
  intro C c
  have scratch : ∀ i : Fin 20, (i ≤ 14 ∧ i ≠ 4) ∨ i = 17 →
      let k := childLoadPorts i
      (k ≤ 26 ∧ k ≠ 2 ∧ k ≠ 24 ∧ k ≠ 25) ∨ (29 ≤ k ∧ k ≤ 31) := by decide
  obtain ⟨u,D,l,hu,hl,load,fw,_,neg,hL,_,_,frame⟩ := signedChildPair_exec body (childLoadPorts.trans bank)
    parent j inv reciprocal pivot i unit hb H hm v S tail rest weights record modulus one clock
    (fun i h => free _ (scratch i h))
  let ports := (childShearPorts negative).trans bank
  have fixed : ∀ h : Fin 29, h ≠ 0 → childShearPorts negative h = h.castLE (by decide) := by cases negative <;> decide
  have keep (h : Fin 29) (hn : h ≠ 0) : D.R (ports h) = S.R (bank (h.castLE (by decide))) := by
    change D.R (bank (childShearPorts negative h)) = _
    rw [fixed h hn]
    have off : ∀ h : Fin 29, let k : Fin 36 := h.castLE (by decide)
        k ≠ 30 ∧ k ≠ 31 ∧ k ≠ 29 := by decide
    exact frame _ (bank.injective.ne (off h).1) (bank.injective.ne (off h).2.1) (bank.injective.ne (off h).2.2)
  have srcPort : (24 : Fin 29).castLE (by decide : 29 ≤ 36) = 24 := by decide
  have dstPort : (25 : Fin 29).castLE (by decide : 29 ≤ 36) = 25 := by decide
  have coef : D.R (ports 0) = binSyms H c.val := by cases negative <;> first | exact fw | exact neg
  have leftPort : ∀ i : Fin 12, i < 10 → shearTranslation i ≠ 0 := by decide
  have size : 29 ≤ 36 := by decide
  obtain ⟨z,F,n,hz,hn,run,post⟩ := weightedShear_exec k t hk sym c (P := Empty) Empty.elim
    (Function.Embedding.refl _) H J hm hw hW (embDn ports u) (embStk ports D)
    ((keep 2 (by decide)).trans modulus) ((keep 28 (by decide)).trans single) ((keep 27 (by decide)).trans width) coef
    (fun i lo hi h2 h24 h25 => (keep i (by omega)).trans (free _ (.inl
      ((by decide +revert : ∀ i : Fin 29, i ≤ 26 → i ≠ 2 → i ≠ 24 → i ≠ 25 →
        let k := i.castLE size
        k ≤ 26 ∧ k ≠ 2 ∧ k ≠ 24 ∧ k ≠ 25) i hi h2 h24 h25))))
    (fun i hi => by simpa only [embStk_L,Function.Embedding.refl_apply,ports,Function.Embedding.trans_apply,fixed _ (leftPort i hi),hL] using left i hi)
    source dest p q a empty
    (fun z => by change _ = readAt blank (D.L (ports 24)) (D.R (ports 24)) _; rw [keep 24 (by decide),hL]; simpa only [ports,Function.Embedding.trans_apply,fixed 24 (by decide),srcPort] using src z)
    (fun z => by change _ = readAt blank (D.L (ports 25)) (D.R (ports 25)) _; rw [keep 25 (by decide),hL]; simpa only [ports,Function.Embedding.trans_apply,fixed 25 (by decide),dstPort] using dst z)
  obtain ⟨y,G,embedded,_,hy,eq,outside⟩ := exec_emb (body' := body) (ι := Empty.elim)
    ports.injective (fun e => nomatch e) run u rfl D rfl
  rw [← eq] at post
  obtain ⟨base,headers,clean,out,result,action⟩ := post
  have atPort (j : Fin 29) (h : j ≠ 0) : ports j = bank (j.castLE size) := congrArg bank (fixed j h)
  have saved (j : Fin 36) (hj : j = 2 ∨ j = 27 ∨ j = 28 ∨ 32 ≤ j) : G.R (bank j) = S.R (bank j) := by
    rcases hj with rfl | rfl | rfl | high
    · simpa only [embStk_R,Function.Embedding.refl_apply,atPort 2 (by decide),
        show (2 : Fin 29).castLE size = 2 by rfl] using base.trans (keep 2 (by decide))
    · simpa only [embStk_R,Function.Embedding.refl_apply,atPort 27 (by decide),
        show (27 : Fin 29).castLE size = 27 by rfl] using (headers 27 (by decide)).trans (keep 27 (by decide))
    · simpa only [embStk_R,Function.Embedding.refl_apply,atPort 28 (by decide),
        show (28 : Fin 29).castLE size = 28 by rfl] using (headers 28 (by decide)).trans (keep 28 (by decide))
    · have off : ∀ b (j : Fin 36), 32 ≤ j → ∀ k, childShearPorts b k ≠ j := by decide
      exact (outside _ (fun k => bank.injective.ne (off negative j high k))).2.trans
        (frame _ (bank.injective.ne (show j ≠ 30 by omega)) (bank.injective.ne (show j ≠ 31 by omega))
          (bank.injective.ne (show j ≠ 29 by omega)))
  exact ⟨y,G,l+n,hy.trans (hz.trans hu),Nat.add_le_add hl hn,Exec.seq load embedded,saved,
    by simpa only [embStk_R,embStk_L,Function.Embedding.refl_apply,ports,Function.Embedding.trans_apply,fixed 25 (by decide),dstPort] using clean,out,
    by simpa only [embStk_R,embStk_L,Function.Embedding.refl_apply,ports,Function.Embedding.trans_apply,fixed 24 (by decide),srcPort] using result,action⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
