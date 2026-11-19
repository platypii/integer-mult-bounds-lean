module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPreparedScan

/-! Setup bounds for the physical forward exchanges and reverse columns. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open M8 ActualAffineScaling FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net]

omit [M8.Machine.Net] in
private theorem childShearSetup_zero {P U : Type} [Fintype P] {T A m : ℕ}
    (body : P → Pr P T 217 A U) (bank : Fin 36 ↪ Fin T) (b j i : ℕ) (positive : 0 < b)
    (k t : Fin m) (neg : Bool) :
    ∃ C : ℕ, ∀ w H, cleanChildShearTime body bank b j i k t neg w 0 H 0 ≤
      C*(w+1+(b^(w+1))^(m-1))*(H+1)^2 := by
  let push := max (Fast.Main.mnPushC body)
    (Fast.Main.mnProgPush (childShear (P := P) (A := A) (U := U) b j i k t neg bank))
  refine ⟨4*childWork.length+1+(1+6*childWork.length*push)*(8000*(b+1)*(m+1)^2+8*(j+i)),?_⟩
  intro w H
  simp only [cleanChildShearTime]
  grw [weightedShearTime_setup_le_width k t _ H (pow_pos positive _),Nat.sub_le b 2]
  dsimp only [push]
  generalize (max _ _ : ℕ) = calls
  generalize (b^(w+1))^(m-1) = prefixes
  generalize childWork.length = tapes
  ring_nf
  omega

omit [M8.Machine.Net] in
private theorem childShearSetup {P U : Type} [Fintype P] {T A m : ℕ}
    (body : P → Pr P T 217 A U) (bank : Fin 36 ↪ Fin T) (b j i : ℕ) (positive : 0 < b)
    (k t : Fin m) (neg : Bool) :
    ∃ C : ℕ, ∀ w H J, cleanChildShearTime body bank b j i k t neg w 0 H J ≤
      C*(w+1+(b^(w+1))^(m-1))*(H+1)^2*(J+1) := by
  obtain ⟨c,hc⟩ := childShearSetup_zero body bank b j i positive k t neg
  let push := max (Fast.Main.mnPushC body)
    (Fast.Main.mnProgPush (childShear (P := P) (A := A) (U := U) b j i k t neg bank))
  let rate := 1+6*childWork.length*push
  refine ⟨c+rate*(10+18*m),fun w H J => ?_⟩
  have timing : cleanChildShearTime body bank b j i k t neg w 0 H J =
      cleanChildShearTime body bank b j i k t neg w 0 H 0 + rate*(10+(m-1-t.val)*(12*H+18))*J := by
    simp only [cleanChildShearTime,rate,push]
    rw [weightedShearTime_eq_setup_add_width_volume k t (b^(w+1)) 0 H J]
    simp only [Nat.mul_zero,Nat.add_zero]
    ring
  rw [timing]
  grw [hc w H,(Nat.sub_le (m-1) t.val).trans (Nat.sub_le m 1)]
  generalize (b^(w+1))^(m-1) = prefixes
  ring_nf
  omega

theorem exchangeTime_setup_le (U : Type) {m : ℕ} (j i : ℕ) (k t : Fin m) (width : ℕ) :
    ∃ C : ℕ, ∀ w H J, exchangeTime U j i k t width w 0 H J ≤
      C*(w+1+(prime^(w+1))^(m-1))*(H+1)^2*(J+1) := by
  choose c hc using childShearSetup (P := Empty) (U := U) (A := prime) Empty.elim
    (Function.Embedding.refl _) prime j i prime_prime.pos k t
  obtain ⟨s,hs⟩ := completeSwapTime_setup_le (P := Empty) (U := U) Empty.elim m k t
  have swapCounter : ∃ r : ℕ, ∀ w H J, completeSwapTime (P := Empty) (U := U) Empty.elim m k t w 0 H J =
      completeSwapTime (P := Empty) (U := U) Empty.elim m k t w 0 H 0+r*J :=
    ⟨_,fun w H J => completeSwapTime_eq_setup_add_counter _ m k t w 0 H J⟩
  obtain ⟨r,hr⟩ := swapCounter
  refine ⟨100+4*s+2*r+2*c false+c true,?_⟩
  intro w H J
  simp only [exchangeTime,Nat.mul_zero,Nat.zero_mul]
  rw [hr w H J]
  grw [hc false w H J,hc true w H J,hs w H]
  generalize (prime^(w+1))^(m-1) = prefixes
  ring_nf
  omega

/-- A fixed exchange schedule and all reverse pivot choices share a setup constant.
The largest exponential factor enumerates only a coordinate prefix. -/
theorem preparedKernel_setup_le (U : Type) {n d : ℕ} (xs : List (Fin n))
    (j i : Fin n → ℕ) (k t : Fin n → Fin (d+1)) (width : Fin n → ℕ) (total push : ℕ) :
    ∃ C : ℕ, ∀ w H J, preparedSetupTime U xs j i k t width total push w H J ≤
      C*(w+1+(prime^(w+1))^d)*(H+1)^2*(J+1) := by
  choose c hc using fun a => exchangeTime_setup_le U (j a) (i a) (k a) (t a) (width a)
  obtain ⟨b,hb⟩ := columnProgramTime_setup_le U (d+1)
  obtain ⟨r,hr⟩ := columnProgramTime_le_setup_add_linear_counter U (d+1)
  refine ⟨cleanupTime d 0 total push (xs.map c).sum (b+r),?_⟩
  intro w H J
  unfold preparedSetupTime
  extract_lets steps largest
  let size := (w+1+(prime^(w+1))^d)*(H+1)^2*(J+1)
  have cols : largest ≤ (b+r)*size := Finset.sup_le fun q _ => Finset.sup_le fun p _ => by
    apply (hr p q w 0 H J).trans
    grw [hb p q w H]
    simp only [size,Nat.add_one_sub_one]
    generalize (prime^(w+1))^d = prefixes
    ring_nf
    omega
  have exchanges (ys : List (Fin n)) :
      (ys.map fun a => exchangeTime U (j a) (i a) (k a) (t a) (width a) w 0 H J).sum ≤
        (ys.map c).sum*size := by
    induction ys with
    | nil => simp
    | cons a ys ih =>
      simp only [List.map_cons,List.sum_cons,Nat.add_mul]
      exact Nat.add_le_add (by simpa only [size,Nat.add_one_sub_one,Nat.mul_assoc] using hc a w H J) ih
  have forward : steps ≤ (xs.map c).sum*size := exchanges xs
  have field : H+1 ≤ size := by
    dsimp only [size]
    generalize (prime^(w+1))^d = prefixes
    ring_nf
    omega
  rw [Nat.mul_assoc (cleanupTime d 0 total push (xs.map c).sum (b+r)),Nat.mul_assoc (cleanupTime d 0 total push (xs.map c).sum (b+r))]
  change cleanupTime d H total push steps largest ≤ cleanupTime d 0 total push (xs.map c).sum (b+r)*size
  dsimp only [cleanupTime]
  have bits : 4*H+4 ≤ 4*size := by omega
  grw [forward,cols,bits]
  generalize (xs.map c).sum = schedule
  generalize b+r = reverse
  have positive : 1 ≤ size := by omega
  obtain ⟨extra,eq⟩ := Nat.exists_eq_add_of_le positive
  rw [eq]
  ring_nf
  omega

/-- With binary field and payload-counter widths, each record pays for its setup. -/
theorem preparedSetup_recordVolume_le (U : Type) {n d : ℕ} (xs : List (Fin n))
    (j i : Fin n → ℕ) (k t : Fin n → Fin (d+1)) (width : Fin n → ℕ) (total push : ℕ) :
    ∃ C : ℕ, ∀ w W, 0 < W →
      let q := prime^(w+1)
      preparedSetupTime U xs j i k t width total push w (Nat.size q) (Nat.size W) ≤ C*(q^(d+1)*W) := by
  obtain ⟨c,hc⟩ := preparedKernel_setup_le U xs j i k t width total push
  refine ⟨2*c*(2*(Nat.size prime+1)^2),fun w W pos => ?_⟩
  apply (hc w _ _).trans
  have field := prefixSetup_volume_le w d
  dsimp only at field
  have bits : Nat.size W ≤ W := Nat.size_le.mpr Nat.lt_two_pow_self
  have counter : Nat.size W+1 ≤ 2*W := by omega
  rw [Nat.mul_assoc c]
  grw [field,counter]
  exact le_of_eq (by ring)

/-- Summing the setup over the live records costs at most a constant times the
descriptor volume, uniformly in atom width, suffix width and spectator counts. -/
theorem preparedSetup_descriptorVolume_le (U : Type) {n d r : ℕ} (xs : List (Fin n))
    (j i : Fin n → ℕ) (k t : Fin n → Fin (d+1)) (width : Fin n → ℕ) (total push : ℕ)
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) :
    ∃ C : ℕ, ∀ (v : RecursiveInterchangeLayout.Descriptor) w suffix live, v.Positive →
      v.width = r*(w+1)+suffix → live ≤ LabelMask.records v →
      let W := prime^(2*suffix)*v.between*v.afterD
      live*preparedSetupTime U xs j i k t width total push w (Nat.size (prime^(w+1))) (Nat.size W) ≤
        C*RecursiveInterchangeLayout.volume prime v := by
  obtain ⟨c,hc⟩ := preparedSetup_recordVolume_le U xs j i k t width total push
  refine ⟨c,fun v w suffix live positive splitWidth count => ?_⟩
  intro W
  have widthPos : 0 < W := Nat.mul_pos (Nat.mul_pos (pow_pos prime_prime.pos _)
    positive.2.2.2.1) positive.2.2.2.2
  have bound := Nat.mul_le_mul count (hc w W widthPos)
  rw [← signedPassVolume_eq_descriptor v e w suffix splitWidth]
  exact bound.trans_eq (by dsimp only [W]; ring)

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
