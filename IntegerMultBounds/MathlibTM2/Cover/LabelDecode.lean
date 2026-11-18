module

public import IntegerMultBounds.MathlibTM2.Cover.LabelPadSetup
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Decode the retained canonical binary headers into the unary padding registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDecode
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open Host Node
open FlatCoordinateSchedule (bits)
variable {T Q A : ℕ} {P U : Type}

private theorem bin_value (xs : List Bool) :
    binBits xs.length (Counter.value xs) = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [List.length_cons,binBits_succ]
    cases b <;> simp [Counter.value,Nat.testBit_zero,ih]
    rwa [show (1 + 2*Counter.value xs)/2 = Counter.value xs by omega]

theorem field_exec (body : P → Pr P T Q A U) {src dst a b c : Fin T}
    (hr : [src,dst,a,b,c].Nodup) (n : ℕ) (u : HS T Q A U) (S : Stacks T A)
    (hx : S.R src = (bits n).map bitSymbol) (hf : ∀ k ∈ [dst,a,b,c], S.R k = []) :
    ∃ z t, z.user = u.user ∧ t ≤ 17*(n+1) ∧
      Exec body (toUnary src dst a b c) (mk u S) t
        (mk z {S with R := Function.update S.R dst (List.replicate n tick)}) := by
  have he := bin_value (bits n)
  rw [FlatCoordinateSchedule.bits_value] at he
  have hlt := Counter.value_lt (bits n)
  rw [FlatCoordinateSchedule.bits_value] at hlt
  obtain ⟨z,t,hu,ht,hrun⟩ := toUnary_exec_linear body hr hlt u S
    (by simpa only [binSyms_eq,he] using hx) (hf _ (by simp)) (hf _ (by simp)) (hf _ (by simp))
  have := M8.Stage2Machine.Straight.length_le n
  exact ⟨z,t,hu,by omega,by simpa only [hf dst (by simp),List.append_nil] using hrun⟩

open RecursiveInterchangeLayout (Descriptor)

def field (v : Descriptor) (w : ℕ) : Fin 7 → ℕ :=
  ![v.beforeRows,v.rows,v.beforeH,v.width,v.between,v.afterD,w]

def target (r : Fin 26 ↪ Fin T) (i : Fin 7) := r (Fin.castLE (by decide) i)
def source (r : Fin 26 ↪ Fin T) (i : Fin 7) := r (Fin.natAdd 19 i)

private theorem separate (r : Fin 26 ↪ Fin T) (i j : Fin 7) : source r i ≠ target r j := by
  intro h
  have e := congrArg Fin.val (r.injective h)
  change 19+i.val = j.val at e
  omega

private theorem target_inj (r : Fin 26 ↪ Fin T) : Function.Injective (target r) :=
  fun _ _ h => Fin.ext (congrArg (Fin.val (n := 26)) (r.injective h))

def program (r : Fin 26 ↪ Fin T) : List (Fin 7) → Pr P T Q A U
  | [] => .act .done
  | i :: is => .seq (toUnary (source r i) (target r i) (r 9) (r 10) (r 11)) (program r is)

theorem runs (body : P → Pr P T Q A U) (r : Fin 26 ↪ Fin T) (f : Fin 7 → ℕ)
    (is : List (Fin 7)) (hd : is.Nodup) (u : HS T Q A U) (S : Stacks T A)
    (hx : ∀ i ∈ is, S.R (source r i) = (bits (f i)).map bitSymbol)
    (hf : ∀ i ∈ is, S.R (target r i) = []) (ht : ∀ k ∈ [r 9,r 10,r 11], S.R k = []) :
    ∃ z R c, z.user = u.user ∧ c ≤ (is.map (fun i => 17*(f i+1))).sum+1 ∧
      (∀ i ∈ is, R (target r i) = List.replicate (f i) tick) ∧
      (∀ k, k ∉ is.map (target r) → R k = S.R k) ∧
      Exec body (program r is) (mk u S) c (mk z {S with R := R}) := by
  induction is generalizing u S with
  | nil =>
    exact ⟨u,S.R,1,rfl,by simp,by simp,by simp,Exec.act (body := body) .done (mk u S)⟩
  | cons i is ih =>
    have diff (k : Fin 26) (hk : 7 ≤ k.val) (hl : k.val < 19) :
        r k ≠ target r i ∧ source r i ≠ r k := by
      constructor <;> intro h <;> have e := congrArg Fin.val (r.injective h)
      · change k.val = i.val at e; omega
      · change 19+i.val = k.val at e; omega
    have ds : (source r i) ≠ target r i := separate r i i
    have hr : [source r i,target r i,r 9,r 10,r 11].Nodup := by
      simp [ds,(diff 9 (by decide) (by decide)).2,(diff 10 (by decide) (by decide)).2,
        (diff 11 (by decide) (by decide)).2,Ne.symm (diff 9 (by decide) (by decide)).1,
        Ne.symm (diff 10 (by decide) (by decide)).1,Ne.symm (diff 11 (by decide) (by decide)).1]
    obtain ⟨z,t,hu,hc,he⟩ := field_exec body hr (f i) u S (hx i (by simp)) (by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hf i (by simp)
      · exact ht _ hk)
    let M : Stacks T A := {S with R := Function.update S.R (target r i) (List.replicate (f i) tick)}
    obtain ⟨z',R,c,hu',hc',hin,hout,he'⟩ := ih hd.tail z M
      (fun j hj => by simpa [M,separate r j i] using hx j (by simp [hj]))
      (fun j hj => by
        have h : target r j ≠ target r i := fun e => hd.notMem (target_inj r e ▸ hj)
        simpa [M,h] using hf j (by simp [hj]))
      (by intro k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          have hne : k ≠ target r i := by
            rcases hk with rfl | rfl | rfl <;> exact (diff _ (by decide) (by decide)).1
          simpa [M,hne] using ht k (by simpa using hk))
    refine ⟨z',R,t+c,hu'.trans hu,by simp only [List.map_cons,List.sum_cons]; omega,?_,?_,Exec.seq he he'⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [hout]; exact Function.update_self ..
        intro h
        obtain ⟨j,hj,e⟩ := List.mem_map.mp h
        exact hd.notMem (target_inj r e ▸ hj)
      · exact hin j hj
    · intro k hk
      simp only [List.map_cons,List.mem_cons,not_or] at hk
      rw [hout k hk.2]
      exact Function.update_of_ne hk.1 ..

open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open LabelTraversal LabelStock LabelTransport
open RecursiveInterchangeLayout (volume)

def work (r : Fin 26 ↪ Fin T) : Fin 19 ↪ Fin T :=
  ⟨fun i => r (Fin.castLE (by decide) i),fun _ _ h => Fin.ext (congrArg (Fin.val (n := 26)) (r.injective h))⟩

private theorem field_bound (v : Descriptor) (w m B : ℕ) (hm : 0 < m) (hp : v.Positive)
    (hv : v.beforeH = B*prime^(m*(w*m))) (i : Fin 7) : field v w i ≤ volume prime v := by
  have hprime := IntegerMultBounds.Networks.Shared50ModularControl.prime_prime
  have hq := pow_pos hprime.pos v.width
  have extend (a : ℕ) {b : ℕ} (hb : 0 < b) := Nat.le_mul_of_pos_right a hb
  obtain ⟨ha,hr,hh,hb,hd⟩ := hp
  have hV := RecursiveAffinePrepare.volume_positive hprime.two_le v ⟨ha,hr,hh,hb,hd⟩
  obtain ⟨hH,hB,hD⟩ := LabelPrepare.factors v hV
  have pre := (extend _ hh).trans ((extend _ hq).trans ((extend _ hb).trans
    ((extend _ hq).trans (extend (v.beforeRows*v.rows*v.beforeH*prime^v.width*v.between*prime^v.width) hd))))
  have rad := Nat.le_mul_of_pos_left (prime^v.width) (Nat.mul_pos (Nat.mul_pos ha hr) hh)
  have hrad : prime^v.width ≤ volume prime v := rad.trans ((extend _ hb).trans ((extend _ hq).trans (extend _ hd)))
  have he := (extend w hm).trans (Nat.le_mul_of_pos_left (w*m) hm)
  have hBp : 0 < B := by by_contra! h; simp [show B = 0 by omega] at hv; omega
  have hw := (he.trans (Nat.lt_pow_self hprime.one_lt).le).trans
    ((hv ▸ Nat.le_mul_of_pos_left _ hBp).trans hH)
  fin_cases i
  exacts [(extend _ hr).trans pre,(Nat.le_mul_of_pos_left _ ha).trans pre,hH,
    (Nat.lt_pow_self hprime.one_lt).le.trans hrad,hB,hD,hw]

/-- Pad the compact stock from canonical binary words. The program creates its own unary seed. -/
theorem realizes (body : P → Pr P T Q A U) (r : Fin 26 ↪ Fin T) (m : ℕ) (hm : 0 < m)
    (rs : List (Pair T)) (hk : rs.length = m*m) (hd : (slots rs).Nodup)
    (apart : ∀ i, r i ∉ slots rs) :
    ∃ p : Pr P T Q A U, ∀ (v : Descriptor) (w B : ℕ), 0 < w → v.Positive →
      v.beforeH = B*prime^(m*(w*m)) → ∀ (bit : ℕ → Bool) (u : HS T Q A U) (S : Stacks T A),
      (∀ i, S.R (source r i) = (bits (field v w i)).map bitSymbol) →
      (∀ i : Fin 26, i.val ≤ 16 → S.R (r i) = []) → (∀ k ∈ slots rs, S.R k = []) →
      let xs := List.range (volume prime v)
      let keep := live m w (payload v)
      S.R (r 17) = ((xs.filter keep).map bit).map bitSymbol →
      ∃ z F c, z.user = u.user ∧
        F.R (r 18) = (xs.map (fun i => bitSymbol (if keep i then bit i else false))) ++ S.R (r 18) ∧
        F.R (r 17) = S.R (r 17) ∧ F.R (r 16) = (xs.map keep).map bitSymbol ∧
        c ≤ (434+10*(m*m))*volume prime v ∧
        Exec body p (mk u S) c (mk z F) := by
  obtain ⟨pad,hpad⟩ := LabelPadSetup.realizes body (work r) m hm rs hk hd (fun i => apart _)
  let seed : Act T Q A U := .push (.rt (r 14)) (fun _ => tick) .done
  refine ⟨.seq (program r (List.finRange 7)) (.seq (.act seed) pad), ?_⟩
  intro v w B hw hp hv bit u S hx hf hs
  dsimp only
  intro hsrc
  obtain ⟨u₁,R,t,hu,ht,hin,hout,he⟩ := runs body r (field v w) (List.finRange 7)
    (List.nodup_finRange _) u S (fun i _ => hx i)
    (fun i _ => hf _ (by change i.val ≤ 16; omega))
    (by intro k hk; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact hf _ (by decide))
  have outside (i : Fin 26) (hi : 7 ≤ i.val) : R (r i) = S.R (r i) := by
    apply hout
    intro h
    obtain ⟨j,_,e⟩ := List.mem_map.mp h
    have eq := congrArg Fin.val (r.injective e)
    change j.val = i.val at eq
    omega
  let M : Stacks T A := {S with R := Function.update R (r 14) [tick]}
  have seedRun : Exec body (.act seed) (mk u₁ {S with R := R}) 1 (mk u₁ M) := by
    simpa [M,seed,Action.run,update_rt,outside 14 (by decide),hf 14 (by decide)]
      using (Exec.act (body := body) seed (mk u₁ {S with R := R}))
  have word (i : Fin 7) : M.R (target r i) = List.replicate (field v w i) tick := by
    have ne : target r i ≠ r 14 := by
      intro e
      have h := congrArg Fin.val (r.injective e)
      change i.val = 14 at h
      omega
    simpa [M,ne] using hin i (List.mem_finRange i)
  have orig (i : Fin 26) (hi : 7 ≤ i.val) (hne : i ≠ 14) : M.R (r i) = S.R (r i) := by
    simp [M,hne,outside i hi]
  have dims : LabelDimensions.inputs (LabelPadSetup.dimensions (work r)) M.R v w := by
    have len (i : Fin 7) := (congrArg List.length (word i)).trans (List.length_replicate ..)
    exact ⟨len 0,len 1,len 2,len 3,len 4,len 5,len 6⟩
  obtain ⟨z,F,c,hz,ho,hx',hm',hc,run⟩ := hpad v w B hw hp hv bit u₁ M dims (word 6)
    (by change (M.R (r 14)).length = 1; simp [M])
    (fun i hi hj ne => (orig (Fin.castLE (by decide) i) hi
      (fun h => ne (Fin.ext (congrArg (Fin.val (n := 26)) h)))).trans (hf _ hj))
    (by intro k h
        have ne (i : Fin 26) : k ≠ r i := fun e => apart i (e ▸ h)
        have outside' : R k = S.R k := by
          apply hout
          intro e
          obtain ⟨j,_,ej⟩ := List.mem_map.mp e
          exact ne _ ej.symm
        simp [M,ne,outside',hs k h])
    ((orig 17 (by decide) (by decide)).trans hsrc)
  refine ⟨z,F,t+(1+c),hz.trans hu,?_,?_,hm',?_,Exec.seq he (Exec.seq seedRun run)⟩
  · exact ho.trans (congrArg (_ ++ ·) (orig 18 (by decide) (by decide)))
  · exact hx'.trans (orig 17 (by decide) (by decide))
  · let V := volume prime v
    have hV : 0 < V := RecursiveAffinePrepare.volume_positive
      IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.two_le v hp
    have bound (is : List (Fin 7)) : (is.map (fun i => 17*(field v w i+1))).sum ≤ is.length*(34*V) := by
      induction is with
      | nil => simp
      | cons i is ih =>
        have h : field v w i ≤ V := field_bound v w m B hm hp hv i
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        rw [Nat.succ_mul is.length]
        omega
    have hb := bound (List.finRange 7)
    simp only [List.length_finRange] at hb
    dsimp [V] at hb hV
    nlinarith only [hb,hV,ht,hc]

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDecode
