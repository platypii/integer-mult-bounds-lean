module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairShear

/-! Restore the shared layout after each weighted payload shear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def cleanPairShear (b : ℕ) (i k t : Fin d) (inverse : Bool) (bank : Fin 35 ↪ Fin T) (negative : Bool := false) (useOne : Bool := false) : Pr P T 217 A U :=
  .seq (pairShear b i k t inverse bank negative useOne) (clearWorkTapes (shearWork.map bank))

private theorem cleanup_bound {l work count push limit : ℕ}
    (h : work ≤ count*4+1+count*(6*(push*l))) (hl : l ≤ limit) :
    l+work ≤ 4*count+1+(1+6*count*push)*limit := by
  calc
    _ ≤ l+(count*4+1+count*(6*(push*l))) := Nat.add_le_add_left h _
    _ = 4*count+1+(1+6*count*push)*l := by ring
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _

noncomputable def cleanPairShearTime [Fintype P] (body : P → Pr P T 217 A U) (bank : Fin 35 ↪ Fin T)
    (i k t : Fin d) (b w W H J : ℕ) (inverse negative : Bool) (useOne : Bool := false) : ℕ :=
  let C := 48*H*H+152*H+66
  let limit := (8*((i.val*d+i.val)*H)+14*H+22) +
      (6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C))) + (if negative then 8*H+8 else 0) + weightedShearTime k t (b^(w+1)) W H J
  let push := max (Fast.Main.mnPushC body) (Fast.Main.mnProgPush (pairShear (P := P) (A := A) (U := U) b i k t inverse bank negative useOne))
  4*shearWork.length+1+(1+6*shearWork.length*push)*limit

/-- Coefficient preparation costs linearly in the atom width. The shear
enumerates at most a prefix of length `d-1`, including work-tape restoration. -/
theorem cleanPairShearTime_setup_le [Fintype P] (body : P → Pr P T 217 A U)
    (bank : Fin 35 ↪ Fin T) (i k t : Fin d) (b : ℕ) (positive : 0 < b)
    (inverse negative useOne : Bool) :
    ∃ C : ℕ, ∀ w H, cleanPairShearTime body bank i k t b w 0 H 0 inverse negative useOne ≤
      C * (w+1+(b^(w+1))^(d-1)) * (H+1)^2 := by
  let push := max (Fast.Main.mnPushC body) (Fast.Main.mnProgPush
    (pairShear (P := P) (A := A) (U := U) b i k t inverse bank negative useOne))
  refine ⟨4*shearWork.length+1+(1+6*shearWork.length*push)*(8000*(b+1)*(d+1)^2), ?_⟩
  intro w H
  simp only [cleanPairShearTime]
  grw [weightedShearTime_setup_le_width k t _ H (pow_pos positive _),
    Nat.sub_le b 2, i.isLt.le]
  have sign : (if negative then 8*H+8 else 0) ≤ 8*H+8 := by split <;> omega
  grw [sign]
  dsimp [push]
  generalize (max _ _ : ℕ) = calls
  generalize (b^(w+1))^(d-1) = prefixes
  ring_nf
  omega

/-- Restoring the work tapes multiplies the volume charge by a program-dependent constant. -/
theorem cleanPairShearTime_eq_setup_add_volume [Fintype P]
    (body : P → Pr P T 217 A U) (bank : Fin 35 ↪ Fin T) (i k t : Fin d)
    (b w W H J : ℕ) (inverse negative useOne : Bool) :
    let push := max (Fast.Main.mnPushC body) (Fast.Main.mnProgPush
      (pairShear (P := P) (A := A) (U := U) b i k t inverse bank negative useOne))
    cleanPairShearTime body bank i k t b w W H J inverse negative useOne =
      cleanPairShearTime body bank i k t b w 0 H J inverse negative useOne +
        ((1 + 6 * shearWork.length * push) * 9426) * ((b^(w+1))^d * W) := by
  unfold cleanPairShearTime
  rw [weightedShearTime_eq_setup_add_volume k t (b^(w+1)) W H J]
  simp only [Nat.add_assoc, Nat.mul_add, Nat.mul_assoc]


theorem cleanPairShearTime_eq_setup_add_counter [Fintype P]
    (body : P → Pr P T 217 A U) (bank : Fin 35 ↪ Fin T) (i k t : Fin d)
    (b w W H J : ℕ) (inverse negative useOne : Bool) :
    let push := max (Fast.Main.mnPushC body) (Fast.Main.mnProgPush
      (pairShear (P := P) (A := A) (U := U) b i k t inverse bank negative useOne))
    cleanPairShearTime body bank i k t b w W H J inverse negative useOne =
      cleanPairShearTime body bank i k t b w W H 0 inverse negative useOne +
        ((1 + 6 * shearWork.length * push) * (10 + (d-1-t.val)*(12*H+18))) * J := by
  unfold cleanPairShearTime
  rw [weightedShearTime_eq_setup_add_width_volume k t (b^(w+1)) W H J,
    weightedShearTime_eq_setup_add_width_volume k t (b^(w+1)) W H 0]
  ring

theorem cleanPairShear_exec [Fintype P] (body : P → Pr P T 217 A U) (i k t : Fin d) (hk : k < t) (inverse : Bool)
    (bank : Fin 35 ↪ Fin T) (a : Fin d → ZMod M) (unit : IsUnit (a i)) (hb : b.Prime) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W) (v : HS T 217 A U) (S : Stacks T A)
    (tail : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (word : Fin (M^d*W) → α) (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (ready : ShearReady bank H J (Matrix.diagonal a) tail sym source dest p q word S) (negative : Bool := false) (useOne : Bool := false) :
    let weight := if useOne then 1 else a i
    let c := if negative then -Ring.inverse weight else if inverse then Ring.inverse weight else weight
    ∃ z F n out, z.user = v.user ∧ n ≤ cleanPairShearTime body bank i k t b w W H J inverse negative useOne ∧
      Exec body (cleanPairShear b i k t inverse bank negative useOne) (mk v S) n (mk z F) ∧
      ShearReady bank H J (Matrix.diagonal a) tail sym source dest p q out F ∧
      ∀ x j, out (index ((RowOp.shear k t hk c).apply x) j) = word (index x j) := by
  intro weight c
  let push := max (Fast.Main.mnPushC body) (Fast.Main.mnProgPush (pairShear (P := P) (A := A) (U := U) b i k t inverse bank negative useOne))
  obtain ⟨u,D,l,hu,hl,run,modulus,width,one,archive,dst,out,src,effect⟩ :=
    pairShear_exec body i k t hk inverse bank a unit hb H J hm hw hW v S tail sym source dest p q word empty ready negative useOne
  obtain ⟨z,F,hz,finish,free,frame⟩ := clearShear_exec body bank u D
  have keep (j : Fin 35) (hj : j ∉ shearWork) := frame (bank j) (by
    simpa only [List.mem_map,bank.injective.eq_iff,exists_eq_right] using hj)
  let tapes := shearWork.map bank
  have cleanup := cleanup_cost_le tapes run (le_max_right _ _ : _ ≤ push)
    (fun f => (Fast.Main.mn_progPush_le_pushC body f).trans (le_max_left ..))
  have init : (tapes.map fun j => 4*(S.L j).length+2*(S.R j).length+4) = tapes.map (fun _ => 4) := by
    apply List.map_congr_left
    intro j hj
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hj
    simp [(ready.scratch x hx).1,(ready.scratch x hx).2]
  simp only [init,List.map_const',List.sum_replicate_nat,show tapes.length = shearWork.length from List.length_map _] at cleanup
  refine ⟨z,F,_,out,hz.trans hu,?_,Exec.seq run finish,?_,effect⟩
  · exact cleanup_bound cleanup hl
  · refine ⟨(keep 2 (by decide)).2.trans (modulus.trans ready.modulus),
      (keep 27 (by decide)).2.trans (width.trans ready.width),(keep 28 (by decide)).2.trans (one.trans ready.one),
      (keep 32 (by decide)).2.trans ((archive 32 (by decide)).trans ready.padded),?_,
      (keep 34 (by decide)).2.trans ((archive 34 (by decide)).trans ready.archive),
      fun j hj => free j (by simpa [shearWork] using hj),?_,?_⟩
    · rw [(keep 33 (by decide)).2,archive 33 (by decide),ready.clock]
    · simpa only [(keep 24 (by decide)).1,(keep 24 (by decide)).2] using src
    · simpa only [(keep 25 (by decide)).1,(keep 25 (by decide)).2] using dst

def childWork : List (Fin 36) :=
  (List.finRange 36).filter fun i => decide ((i ≤ 26 ∧ i ≠ 2 ∧ i ≠ 24 ∧ i ≠ 25) ∨ (29 ≤ i ∧ i ≤ 31))

def cleanChildShear {m : ℕ} (p j i : ℕ) (k t : Fin m) (negative : Bool) (bank : Fin 36 ↪ Fin T) : Pr P T 217 A U :=
  .seq (childShear p j i k t negative bank) (clearWorkTapes (childWork.map bank))

noncomputable def cleanChildShearTime [Fintype P] {m : ℕ} (body : P → Pr P T 217 A U)
    (bank : Fin 36 ↪ Fin T) (b j i : ℕ) (k t : Fin m) (negative : Bool) (w W H J : ℕ) :=
  let C := 48*H*H+152*H+66
  let limit := (8*(j*H)+14*H+22) +
      ((8*(i*H)+48*H*H+166*H+88)+(6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C)))) +
      (2*H+2) + (8*H+8) + weightedShearTime k t (b^(w+1)) W H J
  let push := max (Fast.Main.mnPushC body) (Fast.Main.mnProgPush (childShear (P := P) (A := A) (U := U) b j i k t negative bank))
  4*childWork.length+1+(1+6*childWork.length*push)*limit

theorem cleanChildShear_exec [Fintype P] {n m : ℕ} (k t : Fin m) (hk : k < t) (negative : Bool) (body : P → Pr P T 217 A U) (bank : Fin 36 ↪ Fin T)
    (parent : Fin n → ZMod M) (j : Fin n) (inv : ZMod M) (reciprocal : parent j * inv = 1)
    (pivot : Fin d → ZMod M) (i : Fin d) (unit : IsUnit (pivot i)) (hb : b.Prime)
    (H : ℕ) (hm : M < 2^H) (v : HS T 217 A U) (S : Stacks T A) (tail rest : List (Fin (A+4)))
    (weights : S.R (bank 35) = (List.ofFn fun k => binSyms H (parent k).val).flatten ++ rest)
    (record : S.R (bank 34) = (List.ofFn fun k => binSyms H (pivot k).val).flatten ++ tail)
    (modulus : S.R (bank 2) = binSyms H M) (one : S.R (bank 32) = binSyms H (1 : ZMod M).val)
    (clock : (S.R (bank 33)).length = w)
    (J : ℕ) (hw : W < 2^J) (hW : 0 < W) (width : S.R (bank 27) = binSyms J W)
    (single : S.R (bank 28) = binSyms 1 1)
    (scratch : ∀ i ∈ childWork, S.L (bank i) = [] ∧ S.R (bank i) = [])
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^m*W) → α)
    (empty : ∀ z, q ≤ z → z < q+(M^m*W : ℕ) → dest z = blank)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ a)) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    let c := if negative then -(inv * Ring.inverse (pivot i)) else parent j * pivot i
    ∃ z F l, z.user = v.user ∧ l ≤ cleanChildShearTime body bank b j.val i.val k t negative w W H J ∧
      Exec body (cleanChildShear b j.val i.val k t negative bank) (mk v S) l (mk z F) ∧
      (∀ i ∈ childWork, F.L (bank i) = [] ∧ F.R (bank i) = []) ∧
      (∀ j : Fin 36, j = 2 ∨ j = 27 ∨ j = 28 ∨ 32 ≤ j → F.R (bank j) = S.R (bank j)) ∧
      (∀ z, readAt blank (F.L (bank 25)) (F.R (bank 25)) (z-q) = RadixToBinary.binaryEncoding.encode (dest z)) ∧
      ∃ out : Fin (M^m*W) → α, (∀ z, readAt blank (F.L (bank 24)) (F.R (bank 24)) (z-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ out)) z)) ∧
        ∀ x h, out (index ((RowOp.shear k t hk c).apply x) h) = a (index x h) := by
  intro c
  have translation : ∀ h : Fin 12, h < 10 → (shearTranslation h).castLE (by decide) ∈ childWork := by decide
  obtain ⟨u,D,l,hu,hl,run,saved,dst',out,src',effect⟩ := childShear_exec k t hk negative body bank parent j inv
    reciprocal pivot i unit hb H hm v S tail rest weights record modulus one clock J hw hW width single
    (fun h hh => (scratch h (by simpa [childWork] using hh)).2) (fun h hh => (scratch _ (translation h hh)).1) sym source dest p q a empty src dst
  let tapes := childWork.map bank
  have distinct : tapes.Nodup := ((List.nodup_finRange _).filter _).map bank.injective
  obtain ⟨z,hz,finish⟩ := clearWorkTapes_exec body tapes distinct u D
  have mem (j : Fin 36) : bank j ∈ tapes ↔ j ∈ childWork := by simp [tapes,bank.injective.eq_iff]
  have cleanup := cleanup_cost_le tapes run (le_max_right (Fast.Main.mnPushC body) _)
    (fun f => (Fast.Main.mn_progPush_le_pushC body f).trans (le_max_left ..))
  have init : (tapes.map fun h => 4*(S.L h).length+2*(S.R h).length+4) = tapes.map (fun _ => 4) := by
    apply List.map_congr_left
    intro h hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    simp [(scratch x hx).1,(scratch x hx).2]
  simp only [init,List.map_const',List.sum_replicate_nat,show tapes.length = childWork.length from List.length_map _] at cleanup
  refine ⟨z,_,_,hz.trans hu,cleanup_bound cleanup hl,Exec.seq run finish,?_,?_,?_,out,?_,effect⟩
  · intro h hh
    simp [(mem h).mpr hh]
  · intro h hh
    have off : h ∉ childWork := (by decide : ∀ h : Fin 36, h = 2 ∨ h = 27 ∨ h = 28 ∨ 32 ≤ h → h ∉ childWork) h hh
    simpa [(mem h).not.mpr off] using saved h hh
  · simpa [(mem 25).not.mpr (by decide : (25 : Fin 36) ∉ childWork)] using dst'
  · simpa [(mem 24).not.mpr (by decide : (24 : Fin 36) ∉ childWork)] using src'

end IntegerMultBounds.MathlibTM2.Cover.Fallback
