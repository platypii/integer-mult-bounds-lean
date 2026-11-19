module

public import IntegerMultBounds.MathlibTM2.Host.BinArithMul
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalExec

/-! Binary dimensions of a scheduled row shear, from a live modulus and suffix width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A : ℕ} {P U : Type}

/-- Accumulate n factors of the modulus on the seed, alternating two result registers. -/
def dimensionPower (r : Fin 10 ↪ Fin T) : ℕ → Pr P T Q A U
  | 0 => bcopy (r 1) (r 2) (r 4) (r 5)
  | n+1 => .seq (dimensionPower ((Equiv.swap 2 3).toEmbedding.trans r) n)
      (.seq (bmul (r 0) (r 3) (r 2) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)) (bclear (r 3)))

def dimensionTime (H W : ℕ) : ℕ → ℕ
  | 0 => 6*W+6
  | n+1 => let w := n*H+W
    dimensionTime H W n + H*(12*(H+w)+20)+16*(H+w)+2*w+26

theorem dimensionTime_eq_setup_add_width (H W n : ℕ) :
    dimensionTime H W n = dimensionTime H 0 n + (6 + n*(12*H+18))*W := by
  induction n with
  | zero => simp [dimensionTime, Nat.add_comm]
  | succ n ih =>
    simp only [dimensionTime, ih, Nat.add_zero]
    ring

theorem dimensionTime_le (H W n : ℕ) :
    dimensionTime H W n ≤ 6*W+6 + n*((12*H+18)*(n*H+W)+20*H+26) := by
  induction n with
  | zero => simp [dimensionTime]
  | succ n ih =>
    let cost (i : ℕ) := (12*H+18)*(i*H+W)+20*H+26
    have mono : cost n ≤ cost (n+1) := by
      dsimp [cost]
      gcongr; omega
    have bound := Nat.mul_le_mul_left n mono
    dsimp [cost] at bound
    rw [dimensionTime]
    nlinarith only [ih,bound]

theorem dimensionPower_exec (body : P → Pr P T Q A U) (n : ℕ) (r : Fin 10 ↪ Fin T)
    (H W M b : ℕ) (hm : M < 2^H) (hb : b < 2^W)
    (v : HS T Q A U) (S : Stacks T A) (base : S.R (r 0) = binSyms H M)
    (seed : S.R (r 1) = binSyms W b) (free : ∀ i : Fin 10, 2 ≤ i → i < 9 → S.R (r i) = []) :
    ∃ z t, z.user = v.user ∧ t ≤ dimensionTime H W n ∧
      Exec body (dimensionPower r n) (mk v S) t
        (mk z {S with R := Function.update S.R (r 2) (binSyms (n*H+W) (M^n*b))}) := by
  induction n generalizing r v S with
  | zero =>
    obtain ⟨z,hu,he⟩ := bcopy_exec body (a := r 1) (c := r 2) (t₁ := r 4) (t₂ := r 5)
      (by simp [List.nodup_cons,r.injective.eq_iff]) v S (free 4 (by decide) (by decide))
      (free 5 (by decide) (by decide))
    rw [seed,free 2 (by decide) (by decide),List.append_nil,length_binSyms] at he
    exact ⟨z,_,hu,le_rfl,by simpa [dimensionPower,dimensionTime] using he⟩
  | succ n ih =>
    let swap := (Equiv.swap (2 : Fin 10) 3).toEmbedding
    have range : ∀ i : Fin 10, 2 ≤ i → i < 9 → 2 ≤ swap i ∧ swap i < 9 := by decide
    obtain ⟨u,t,hu,ht,rec⟩ := ih (swap.trans r) v S base seed
      (fun i hi hj => free (swap i) (range i hi hj).1 (range i hi hj).2)
    let w := n*H+W
    let D : Stacks T A := {S with R := Function.update S.R (r 3) (binSyms w (M^n*b))}
    have bound : M^n*b < 2^w := by
      rw [show 2^w = (2^H)^n * 2^W by simp [w,pow_add,← pow_mul,Nat.mul_comm H n]]
      exact (Nat.mul_le_mul_right b (Nat.pow_le_pow_left hm.le n)).trans_lt
        (Nat.mul_lt_mul_of_pos_left hb (by positivity))
    have keep (i : Fin 10) (h : i ≠ 3) : D.R (r i) = S.R (r i) :=
      Function.update_of_ne (r.injective.ne h) _ _
    have blank (i : Fin 10) (h : i ≠ 3) (hi : 2 ≤ i) (hj : i < 9) := (keep i h).trans (free i hi hj)
    obtain ⟨z,m,hz,hmul,mul⟩ := bmul_exec body (a := r 0) (b := r 3) (c := r 2)
      (s := r 4) (t := r 5) (tx := r 6) (ty := r 7) (tz := r 8) (cy := r 9)
      (by simp [List.nodup_cons,r.injective.eq_iff]) (r.injective.ne (by decide)) (r.injective.ne (by decide))
      hm bound u D ((keep 0 (by decide)).trans base) (by simp [D])
      (blank 2 (by decide) (by decide) (by decide)) (blank 4 (by decide) (by decide) (by decide))
      (blank 5 (by decide) (by decide) (by decide)) (blank 6 (by decide) (by decide) (by decide))
      (blank 7 (by decide) (by decide) (by decide)) (blank 8 (by decide) (by decide) (by decide))
    let E : Stacks T A := {D with R := Function.update D.R (r 2) (binSyms (H+w) (M*(M^n*b)))}
    obtain ⟨z',h',_,clear⟩ := bclear_exec body (r 3) z E
    have len : (E.R (r 3)).length = w := by simp [E,D,r.injective.eq_iff,length_binSyms]
    have final : Function.update E.R (r 3) [] = Function.update S.R (r 2)
        (binSyms ((n+1)*H+W) (M^(n+1)*b)) := by
      funext j
      by_cases h : j = r 2 <;> by_cases h' : j = r 3 <;>
        simp_all [E,D,w,Nat.add_mul,pow_succ',Nat.mul_assoc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
    rw [len,final] at clear
    refine ⟨z',t+(m+(2*w+2)),h'.trans (hz.trans hu),?_,Exec.seq rec (Exec.seq mul clear)⟩
    unfold dimensionTime
    dsimp only [w] at *
    omega

/-- Compute the row extent of a mixed-radix shear from its three binary headers.
Registers 3 and 4 receive the partial and full products respectively. -/
def middleRowCount (r : Fin 11 ↪ Fin T) : Pr P T Q A U :=
  .seq (bmul (r 0) (r 1) (r 3) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10))
    (bmul (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10))

theorem middleRowCount_exec (body : P → Pr P T Q A U) (r : Fin 11 ↪ Fin T)
    (pre M G : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (prefixHeader : S.R (r 0) = binSyms pre.size pre) (radix : S.R (r 1) = binSyms M.size M)
    (gap : S.R (r 2) = binSyms G.size G) (free : ∀ i : Fin 11, 3 ≤ i → i < 10 → S.R (r i) = []) :
    let W := pre.size + M.size
    let D := Function.update S.R (r 3) (binSyms W (pre*M))
    ∃ z n, z.user = v.user ∧ n ≤ pre.size*(12*W+20)+16*W+24 +
      (G.size*(12*(G.size+W)+20)+16*(G.size+W)+24) ∧
      Exec body (middleRowCount r) (mk v S) n
        (mk z {S with R := Function.update D (r 4) (binSyms (G.size+W) (pre*M*G))}) := by
  intro W D
  obtain ⟨u,n,hu,hn,part⟩ := bmul_exec body (a := r 0) (b := r 1) (c := r 3)
    (s := r 5) (t := r 6) (tx := r 7) (ty := r 8) (tz := r 9) (cy := r 10)
    (by simp [List.nodup_cons,r.injective.eq_iff]) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    (Nat.lt_size_self pre) (Nat.lt_size_self M) v S prefixHeader radix
    (free 3 (by decide) (by decide)) (free 5 (by decide) (by decide)) (free 6 (by decide) (by decide))
    (free 7 (by decide) (by decide)) (free 8 (by decide) (by decide)) (free 9 (by decide) (by decide))
  have keep (i : Fin 11) (hi : i ≠ 3) : D (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne hi) _ _
  have scratch (i : Fin 11) (hi : 4 ≤ i) (hj : i < 10) : D (r i) = [] :=
    (keep i (by omega)).trans (free i (by omega) hj)
  have fits : pre*M < 2^W := by
    rw [show W = pre.size+M.size from rfl,pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self pre) (Nat.lt_size_self M).le (by positivity)
  obtain ⟨z,m,hz,hm,full⟩ := bmul_exec body (a := r 2) (b := r 3) (c := r 4)
    (s := r 5) (t := r 6) (tx := r 7) (ty := r 8) (tz := r 9) (cy := r 10)
    (by simp [List.nodup_cons,r.injective.eq_iff]) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    (Nat.lt_size_self G) fits u {S with R := D} ((keep 2 (by decide)).trans gap) (Function.update_self ..)
    (scratch 4 (by decide) (by decide)) (scratch 5 (by decide) (by decide)) (scratch 6 (by decide) (by decide))
    (scratch 7 (by decide) (by decide)) (scratch 8 (by decide) (by decide)) (scratch 9 (by decide) (by decide))
  rw [Nat.mul_comm G] at full
  exact ⟨z,n+m,hz.trans hu,Nat.add_le_add hn hm,Exec.seq part full⟩

def middleRowDescriptor (r : Fin 11 ↪ Fin T) : Pr P T Q A U :=
  .seq (middleRowCount r) (.seq (Routing.binaryCanonicalProgram (r 4) (r 5)) (bclear (r 3)))

private theorem size_square_le (x : ℕ) (hx : 0 < x) : x.size^2 ≤ 4*x := by
  have square (k : ℕ) : k^2 ≤ 2*2^k := by
    induction k with
    | zero => decide
    | succ k ih =>
      by_cases hk : k < 3
      · rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> decide
      · rw [pow_succ 2]
        nlinarith only [ih, Nat.mul_le_mul_left k (show 3 ≤ k by omega), hk]
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show x.size ≠ 0 by
    intro eq
    have h := Nat.lt_size_self x
    rw [eq] at h
    simp at h
    omega)
  have lower : 2^k ≤ x := Nat.lt_size.mp (by omega)
  have bound := square x.size
  rw [hk,pow_succ 2] at bound
  rw [hk]
  omega

/-- Computing and cleaning the row descriptor costs at most a constant per row,
even when the three header widths differ. -/
private theorem middleRowDescriptor_time_le (pre M G : ℕ) (hp : 0 < pre) (hm : 0 < M) (hg : 0 < G) :
    let W := pre.size + M.size
    let L := G.size + W
    pre.size*(12*W+20)+16*W+24+(G.size*(12*L+20)+16*L+24)+(4*L+6+(2*W+2)) ≤
      432*(pre*M*G) := by
  intro W L
  let R := pre*M*G
  have pos : 0 < R := Nat.mul_pos (Nat.mul_pos hp hm) hg
  have pm := Nat.le_mul_of_pos_right (pre*M) hg
  have monotone {x : ℕ} (h : x ≤ R) : x.size ≤ R.size :=
    Nat.size_le.mpr (h.trans_lt (Nat.lt_size_self R))
  have p := monotone ((Nat.le_mul_of_pos_right pre hm).trans pm)
  have m := monotone ((Nat.le_mul_of_pos_left M hp).trans pm)
  have g := monotone (Nat.le_mul_of_pos_left G (Nat.mul_pos hp hm))
  have lin : R.size ≤ R := Nat.size_le.mpr Nat.lt_two_pow_self
  have sq := size_square_le R pos
  calc
    _ ≤ R.size*(12*(R.size+R.size)+20)+16*(R.size+R.size)+24+
        (R.size*(12*(R.size+(R.size+R.size))+20)+16*(R.size+(R.size+R.size))+24)+
        (4*(R.size+(R.size+R.size))+6+(2*(R.size+R.size)+2)) := by
          dsimp only [L,W]
          gcongr
    _ ≤ 432*R := by nlinarith only [sq,lin,pos]

/-- Install the canonical row count in place and release the partial product.
All other stacks, including those of the three input headers, are restored. -/
theorem middleRowDescriptor_exec (body : P → Pr P T Q A U) (r : Fin 11 ↪ Fin T)
    (pre M G : ℕ) (hp : 0 < pre) (hm : 0 < M) (hg : 0 < G)
    (v : HS T Q A U) (S : Stacks T A)
    (prefixHeader : S.R (r 0) = binSyms pre.size pre) (radix : S.R (r 1) = binSyms M.size M)
    (gap : S.R (r 2) = binSyms G.size G) (free : ∀ i : Fin 11, 3 ≤ i → i < 10 → S.R (r i) = []) :
    ∃ bs z n, GrowingCounterData.Canonical bs ∧ Counter.value bs = pre*M*G ∧ z.user = v.user ∧
      n ≤ 432*(pre*M*G) ∧
      Exec body (middleRowDescriptor r) (mk v S) n
        (mk z {S with R := Function.update S.R (r 4) (bs.map bitSymbol)}) := by
  let W := pre.size + M.size
  let L := G.size + W
  obtain ⟨u,n,hu,hn,product⟩ := middleRowCount_exec body r pre M G v S prefixHeader radix gap free
  let D := Function.update S.R (r 3) (binSyms W (pre*M))
  let E := Function.update D (r 4) (binSyms L (pre*M*G))
  have fits : pre*M*G < 2^L := by
    simp only [L,W,pow_add]
    rw [Nat.mul_comm (2^G.size)]
    apply Nat.mul_lt_mul_of_lt_of_le _ (Nat.lt_size_self G).le (by positivity)
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self pre) (Nat.lt_size_self M).le (by positivity)
  obtain ⟨bs,y,cb,hb,_,hy,canon⟩ := Routing.binaryCanonical_exec body (r 4) (r 5)
    (r.injective.ne (by decide)) L (pre*M*G) fits u {S with R := E} (Function.update_self ..)
    (by simp [E,D,r.injective.eq_iff,free 5 (by decide) (by decide)])
  let F := Function.update E (r 4) (bs.map (bitSymbol (a := A)))
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 3) y {S with R := F}
  have len : (F (r 3)).length = W := by simp [F,E,D,r.injective.eq_iff,length_binSyms]
  have restored : Function.update F (r 3) [] = Function.update S.R (r 4) (bs.map bitSymbol) := by
    funext j
    by_cases h : j = r 3 <;> by_cases k : j = r 4 <;>
      simp_all [F,E,D,free 3 (by decide) (by decide)]
  change Exec body _ _ (2*(F (r 3)).length+2) (mk z {S with R := Function.update F (r 3) []}) at clear
  rw [len,restored] at clear
  exact ⟨bs,z,_,cb,hb,hz.trans (hy.trans hu),(Nat.add_le_add_right hn _).trans (middleRowDescriptor_time_le pre M G hp hm hg),
    Exec.seq product (Exec.seq canon clear)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
