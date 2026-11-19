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

end IntegerMultBounds.MathlibTM2.Cover.Fallback
