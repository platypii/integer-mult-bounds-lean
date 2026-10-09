import IntegerMultBounds.Schoenhage.Iter
import IntegerMultBounds.Schoenhage.Level

/-! The layer-by-layer transform of `Iter` is the recursive transform of
`Transform`. Over residues modulo `2^N + 1`, with `K = 2^k` dividing `N` and
`ψ = 2^(N/K)`, a block whose exponent is `e` carries the shift
`t = (N/K)(e/2)`, so `ψ^(e/2) = 2^t`; the children exponents `e/2` and
`e/2 + K` carry the shifts `t/2` and `t/2 + N/2` (`kids`), and the root
`e = K` carries `N/2` (`rel_shiftsAt`). Proved: the iterated forward layers
cast to `ZMod (2^N + 1)` equal `fwd ψ K k K` (`fwdIter_eq_fwd`), and the
iterated inverse layers on inputs below `2^N + 1` equal `inv ψ K k K`
(`invIter_eq_inv`). Every output entry is below `2^N + 1` and lengths are
preserved. -/

namespace IntegerMultBounds.Schoenhage

/-! ### Bounds and lengths -/

theorem zipWith_mod_lt (F : ℕ) (hF : 0 < F) (g : ℕ → ℕ → ℕ) :
    ∀ (U V : List ℕ), ∀ x ∈ List.zipWith (fun u v => g u v % F) U V, x < F
  | [], _ => by simp
  | _ :: _, [] => by simp
  | u :: U, v :: V => by
    intro x hx
    simp only [List.zipWith_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ hF
    · exact zipWith_mod_lt F hF g U V x hx

theorem Fm_pos (N : ℕ) : 0 < Fm N := by unfold Fm; positivity

theorem layerF_lt (N H : ℕ) : ∀ (E D : List ℕ), ∀ x ∈ layerF N H E D, x < Fm N
  | [], _ => by simp [layerF]
  | t :: E, D => by
    intro x hx
    simp only [layerF, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact zipWith_mod_lt _ (Fm_pos N) (fun u v => u + 2 ^ t * v % Fm N) _ _ x hx
    · exact zipWith_mod_lt _ (Fm_pos N) (fun u v => u + Fm N - 2 ^ t * v % Fm N) _ _ x hx
    · exact layerF_lt N H E _ x hx

theorem layerI_lt (N H : ℕ) : ∀ (E D : List ℕ), ∀ x ∈ layerI N H E D, x < Fm N
  | [], _ => by simp [layerI]
  | t :: E, D => by
    intro x hx
    simp only [layerI, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact zipWith_mod_lt _ (Fm_pos N) (fun p q => p + q) _ _ x hx
    · exact zipWith_mod_lt _ (Fm_pos N)
        (fun p q => Fm N - 2 ^ (N - t) * ((p + Fm N - q) % Fm N) % Fm N) _ _ x hx
    · exact layerI_lt N H E _ x hx

theorem layerF_length (N H : ℕ) : ∀ (E D : List ℕ), D.length = E.length * (2 * H) →
    (layerF N H E D).length = E.length * (2 * H)
  | [], _, _ => by simp [layerF]
  | t :: E, D, hD => by
    have hD' : D.length = E.length * (2 * H) + 2 * H := by rw [hD]; simp; ring
    have ih := layerF_length N H E (D.drop (2 * H)) (by simp; omega)
    simp only [layerF, List.length_append, bfS, bfD, List.length_zipWith, List.length_take,
      List.length_drop, ih, List.length_cons]
    have h1 : min H D.length = H := by omega
    have h2 : min H (D.length - H) = H := by omega
    rw [h1, h2]; simp; ring

theorem layerI_length (N H : ℕ) : ∀ (E D : List ℕ), D.length = E.length * (2 * H) →
    (layerI N H E D).length = E.length * (2 * H)
  | [], _, _ => by simp [layerI]
  | t :: E, D, hD => by
    have hD' : D.length = E.length * (2 * H) + 2 * H := by rw [hD]; simp; ring
    have ih := layerI_length N H E (D.drop (2 * H)) (by simp; omega)
    simp only [layerI, List.length_append, ibS, ibD, List.length_zipWith, List.length_take,
      List.length_drop, ih, List.length_cons]
    have h1 : min H D.length = H := by omega
    have h2 : min H (D.length - H) = H := by omega
    rw [h1, h2]; simp; ring

theorem length_kids (N : ℕ) : ∀ E : List ℕ, (kids N E).length = 2 * E.length
  | [] => rfl
  | t :: E => by simp [kids, List.flatMap_cons] at *; have := length_kids N E; simp [kids] at this; omega

theorem length_shiftsAt (N : ℕ) : ∀ s, (shiftsAt N s).length = 2 ^ s
  | 0 => rfl
  | s + 1 => by rw [shiftsAt, length_kids, length_shiftsAt N s, pow_succ]; ring

theorem fwdIter_lt (N : ℕ) : ∀ (s H : ℕ) (E D : List ℕ), (∀ x ∈ D, x < Fm N) →
    ∀ x ∈ fwdIter N s H E D, x < Fm N
  | 0, _, _, _, hD => hD
  | s + 1, H, E, D, _ => fwdIter_lt N s _ _ _ (layerF_lt N H E D)

theorem fwdIter_length (N : ℕ) : ∀ (s H : ℕ) (E D : List ℕ), H = 2 ^ s / 2 →
    D.length = E.length * 2 ^ s → (fwdIter N s H E D).length = D.length
  | 0, _, _, _, _, _ => rfl
  | s + 1, H, E, D, hH, hD => by
    have hH' : H = 2 ^ s := by rw [hH, pow_succ]; simp
    have hl := layerF_length N H E D (by rw [hD, hH', pow_succ]; ring)
    rw [fwdIter, fwdIter_length N s _ _ _ (by rw [hH']) (by rw [hl, length_kids, hH']; ring),
      hl, hD, hH', pow_succ]; ring

theorem invIter_lt (N : ℕ) : ∀ (s k : ℕ) (D : List ℕ), (∀ x ∈ D, x < Fm N) →
    ∀ x ∈ invIter N s k D, x < Fm N
  | 0, _, _, hD => hD
  | s + 1, k, D, _ => invIter_lt N s k _ (layerI_lt N _ _ D)

theorem invIter_length (N : ℕ) : ∀ (s k : ℕ) (D : List ℕ), s ≤ k → D.length = 2 ^ k →
    (invIter N s k D).length = 2 ^ k
  | 0, _, _, _, hD => hD
  | s + 1, k, D, hs, hD => by
    rw [invIter]
    refine invIter_length N s k _ (by omega) ?_
    have : D.length = (shiftsAt N s).length * (2 * 2 ^ (k - 1 - s)) := by
      rw [hD, length_shiftsAt, ← pow_succ', ← pow_add]; congr 1; omega
    rw [layerI_length N _ _ D this, ← this, hD]

/-! ### Blocks of the recursive transform -/

section Blocks

variable {R : Type*} [CommRing R] (ψ : R) (K : ℕ)

/-- The children exponents. -/
def kidsE (es : List ℕ) : List ℕ := es.flatMap fun e => [e / 2, e / 2 + K]

/-- The exponents at depth `s`. -/
def expsAt : ℕ → List ℕ
  | 0 => [K]
  | s + 1 => kidsE K (expsAt s)

theorem length_kidsE : ∀ es : List ℕ, (kidsE K es).length = 2 * es.length
  | [] => rfl
  | e :: es => by
    have := length_kidsE es
    simp [kidsE, List.flatMap_cons] at this ⊢; omega

theorem length_expsAt : ∀ s, (expsAt K s).length = 2 ^ s
  | 0 => rfl
  | s + 1 => by rw [expsAt, length_kidsE, length_expsAt s, pow_succ]; ring

/-- The forward transform on consecutive blocks of size `2^m`. -/
def fwdB (m : ℕ) : List ℕ → List R → List R
  | [], _ => []
  | e :: es, a => fwd ψ K m e (a.take (2 ^ m)) ++ fwdB m es (a.drop (2 ^ m))

/-- The inverse transform on consecutive blocks of size `2^m`. -/
def invB (m : ℕ) : List ℕ → List R → List R
  | [], _ => []
  | e :: es, a => inv ψ K m e (a.take (2 ^ m)) ++ invB m es (a.drop (2 ^ m))

/-- One forward layer on blocks of size `2H`. -/
def layF (H : ℕ) : List ℕ → List R → List R
  | [], _ => []
  | e :: es, a => bsum (ψ ^ (e / 2)) (a.take H) ((a.drop H).take H) ++
      bdiff (ψ ^ (e / 2)) (a.take H) ((a.drop H).take H) ++ layF H es (a.drop (2 * H))

/-- One inverse combining layer on blocks of size `2H`. -/
def combI (H : ℕ) : List ℕ → List R → List R
  | [], _ => []
  | e :: es, a => List.zipWith (· + ·) (a.take H) ((a.drop H).take H) ++
      (List.zipWith (· - ·) (a.take H) ((a.drop H).take H)).map (ψ ^ (2 * K - e / 2) * ·) ++
      combI H es (a.drop (2 * H))

theorem fwdB_zero : ∀ (es : List ℕ) (a : List R), a.length = es.length → fwdB ψ K 0 es a = a
  | [], a, h => by simp at h; subst h; rfl
  | e :: es, a, h => by
    rw [fwdB, fwdB_zero es _ (by simp at h ⊢; omega)]
    simpa [fwd] using List.take_append_drop 1 a

theorem invB_zero : ∀ (es : List ℕ) (a : List R), a.length = es.length → invB ψ K 0 es a = a
  | [], a, h => by simp at h; subst h; rfl
  | e :: es, a, h => by
    rw [invB, invB_zero es _ (by simp at h ⊢; omega)]
    simpa [inv] using List.take_append_drop 1 a

theorem take_append_three {α : Type*} {S D L : List α} {n : ℕ} (hS : S.length = n) (hD : D.length = n) :
    (S ++ D ++ L).take n = S ∧ ((S ++ D ++ L).drop n).take n = D ∧ ((S ++ D ++ L).drop n).drop n = L ∧
      (S ++ D ++ L).drop (2 * n) = L := by
  rw [List.append_assoc]
  refine ⟨List.take_left' hS, ?_, ?_, ?_⟩
  · rw [List.drop_left' hS]; exact List.take_left' hD
  · rw [List.drop_left' hS]; exact List.drop_left' hD
  · rw [← List.append_assoc]; exact List.drop_left' (by simp [hS, hD]; ring)

theorem block_split {α : Type*} (a : List α) (m : ℕ) :
    (a.take (2 ^ (m + 1))).take (2 ^ m) = a.take (2 ^ m) ∧
      (a.take (2 ^ (m + 1))).drop (2 ^ m) = (a.drop (2 ^ m)).take (2 ^ m) ∧
      a.drop (2 * 2 ^ m) = a.drop (2 ^ (m + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.take_take]; congr 1; rw [pow_succ]; omega
  · rw [List.drop_take]; congr 1; rw [pow_succ]; omega
  · rw [pow_succ, mul_comm]

/-- A forward layer followed by the transforms of the children blocks is the
transform of the parent blocks. -/
theorem fwdB_layer (m : ℕ) : ∀ (es : List ℕ) (a : List R), a.length = es.length * 2 ^ (m + 1) →
    fwdB ψ K m (kidsE K es) (layF ψ (2 ^ m) es a) = fwdB ψ K (m + 1) es a
  | [], a, _ => by simp [kidsE, layF, fwdB]
  | e :: es, a, h => by
    have hl : 2 ^ (m + 1) ≤ a.length := by
      rw [h]; simp only [List.length_cons]; nlinarith [Nat.one_le_two_pow (n := m + 1)]
    have h0 : (a.take (2 ^ m)).length = 2 ^ m := by
      simp; rw [pow_succ] at hl; omega
    have h1 : ((a.drop (2 ^ m)).take (2 ^ m)).length = 2 ^ m := by
      simp; rw [pow_succ] at hl; omega
    have hS : (bsum (ψ ^ (e / 2)) (a.take (2 ^ m)) ((a.drop (2 ^ m)).take (2 ^ m))).length = 2 ^ m := by
      rw [length_bsum _ _ _ (by rw [h0, h1]), h0]
    have hD : (bdiff (ψ ^ (e / 2)) (a.take (2 ^ m)) ((a.drop (2 ^ m)).take (2 ^ m))).length = 2 ^ m := by
      rw [length_bdiff _ _ _ (by rw [h0, h1]), h0]
    obtain ⟨t1, t2, t3, -⟩ := take_append_three (L := layF ψ (2 ^ m) es (a.drop (2 * 2 ^ m))) hS hD
    obtain ⟨b1, b2, b3⟩ := block_split a m
    have hrest : (a.drop (2 * 2 ^ m)).length = es.length * 2 ^ (m + 1) := by
      rw [b3, List.length_drop, h, List.length_cons, add_mul, one_mul]; omega
    have ih := fwdB_layer m es (a.drop (2 * 2 ^ m)) hrest
    have hk : kidsE K (e :: es) = e / 2 :: (e / 2 + K) :: kidsE K es := by simp [kidsE]
    rw [hk]
    simp only [layF, fwdB]
    rw [t1, t2, t3, ih, b3]
    simp only [fwd, b1, b2, List.append_assoc]

/-- The inverses of the children blocks followed by a combining layer are the
inverse of the parent blocks. -/
theorem invB_layer (m : ℕ) : ∀ (es : List ℕ) (a : List R), a.length = es.length * 2 ^ (m + 1) →
    invB ψ K (m + 1) es a = combI ψ K (2 ^ m) es (invB ψ K m (kidsE K es) a)
  | [], a, _ => by simp [kidsE, combI, invB]
  | e :: es, a, h => by
    have hl : 2 ^ (m + 1) ≤ a.length := by
      rw [h]; simp only [List.length_cons]; nlinarith [Nat.one_le_two_pow (n := m + 1)]
    have h0 : (a.take (2 ^ m)).length = 2 ^ m := by
      simp; rw [pow_succ] at hl; omega
    have h1 : ((a.drop (2 ^ m)).take (2 ^ m)).length = 2 ^ m := by
      simp; rw [pow_succ] at hl; omega
    obtain ⟨b1, b2, b3⟩ := block_split a m
    have hP := length_inv ψ K m (e / 2) _ h0
    have hQ := length_inv ψ K m (e / 2 + K) _ h1
    obtain ⟨t1, t2, -, t3⟩ := take_append_three
      (L := invB ψ K m (kidsE K es) ((a.drop (2 ^ m)).drop (2 ^ m))) hP hQ
    have ih := invB_layer m es (a.drop (2 ^ (m + 1))) (by
      rw [List.length_drop, h, List.length_cons, add_mul, one_mul]; omega)
    have hdd : (a.drop (2 ^ m)).drop (2 ^ m) = a.drop (2 ^ (m + 1)) := by
      rw [List.drop_drop, pow_succ]; congr 1; ring
    have hk : kidsE K (e :: es) = e / 2 :: (e / 2 + K) :: kidsE K es := by simp [kidsE]
    rw [hk]
    simp only [invB]
    rw [← List.append_assoc]
    simp only [combI]
    rw [t1, t2, t3, hdd, ← ih, ← b3]
    simp only [inv, b1, b2]

end Blocks

/-! ### From residues to the ring -/

section Cast

variable {N : ℕ}

local notation "Rg" => ZMod (2 ^ N + 1)

theorem cast_Fm : ((Fm N : ℕ) : Rg) = 0 := by
  unfold Fm; exact ZMod.natCast_self _

theorem cast_mod_Fm (x : ℕ) : ((x % Fm N : ℕ) : Rg) = x := by
  unfold Fm; exact ZMod.natCast_mod _ _

theorem map_bfS (t : ℕ) : ∀ U V : List ℕ,
    (bfS N t U V).map (Nat.cast : ℕ → Rg) = bsum ((2 : Rg) ^ t) (U.map (↑)) (V.map (↑))
  | [], _ => by simp [bfS, bsum]
  | _ :: _, [] => by simp [bfS, bsum]
  | u :: U, v :: V => by
    have := map_bfS t U V
    simp only [bfS, bsum, List.zipWith_cons_cons, List.map_cons] at this ⊢
    rw [this, cast_mod_Fm]; push_cast; rw [cast_mod_Fm]; push_cast; rfl

theorem map_bfD (t : ℕ) : ∀ U V : List ℕ,
    (bfD N t U V).map (Nat.cast : ℕ → Rg) = bdiff ((2 : Rg) ^ t) (U.map (↑)) (V.map (↑))
  | [], _ => by simp [bfD, bdiff]
  | _ :: _, [] => by simp [bfD, bdiff]
  | u :: U, v :: V => by
    have := map_bfD t U V
    simp only [bfD, bdiff, List.zipWith_cons_cons, List.map_cons] at this ⊢
    rw [this, cast_mod_Fm]
    have hlt : 2 ^ t * v % Fm N ≤ u + Fm N := (Nat.mod_lt _ (Fm_pos N)).le.trans (by omega)
    rw [Nat.cast_sub hlt]; push_cast; rw [cast_Fm, cast_mod_Fm]; push_cast; ring_nf

theorem map_ibS : ∀ P Q : List ℕ,
    (ibS N P Q).map (Nat.cast : ℕ → Rg) = List.zipWith (· + ·) (P.map (↑)) (Q.map (↑))
  | [], _ => by simp [ibS]
  | _ :: _, [] => by simp [ibS]
  | p :: P, q :: Q => by
    have := map_ibS P Q
    simp only [ibS, List.zipWith_cons_cons, List.map_cons] at this ⊢
    rw [this, cast_mod_Fm]; push_cast; rfl

theorem map_ibD (t : ℕ) : ∀ P Q : List ℕ, (∀ q ∈ Q, q < Fm N) →
    (ibD N t P Q).map (Nat.cast : ℕ → Rg) =
      (List.zipWith (· - ·) (P.map (↑)) (Q.map (↑))).map (-(2 : Rg) ^ (N - t) * ·)
  | [], _, _ => by simp [ibD]
  | _ :: _, [], _ => by simp [ibD]
  | p :: P, q :: Q, hQ => by
    have := map_ibD t P Q (fun x hx => hQ x (by simp [hx]))
    simp only [ibD, List.zipWith_cons_cons, List.map_cons] at this ⊢
    rw [this, cast_mod_Fm]
    have hq : q < Fm N := hQ q (by simp)
    have h1 : 2 ^ (N - t) * ((p + Fm N - q) % Fm N) % Fm N ≤ Fm N := (Nat.mod_lt _ (Fm_pos N)).le
    rw [Nat.cast_sub h1, cast_Fm, cast_mod_Fm]; push_cast
    rw [cast_mod_Fm, Nat.cast_sub (by omega)]; push_cast; rw [cast_Fm]; ring_nf

theorem psi_pow {k e t : ℕ} (ht : t = N / 2 ^ k * (e / 2)) :
    ((2 : Rg) ^ (N / 2 ^ k)) ^ (e / 2) = 2 ^ t := by
  rw [← pow_mul, ht]

theorem psi_inv_pow {k e t : ℕ} (hK : 2 ^ k ∣ N) (he : e ≤ 2 * 2 ^ k) (ht : t = N / 2 ^ k * (e / 2)) :
    ((2 : Rg) ^ (N / 2 ^ k)) ^ (2 * 2 ^ k - e / 2) = -2 ^ (N - t) := by
  obtain ⟨q, hq⟩ := hK
  have hq' : N / 2 ^ k = q := by rw [hq]; exact Nat.mul_div_cancel_left _ (Nat.two_pow_pos k)
  rw [hq'] at ht
  have htN : t ≤ N := by
    rw [ht, hq, mul_comm (2 ^ k)]; exact Nat.mul_le_mul_left _ (by omega)
  rw [← pow_mul, hq', Nat.mul_sub, ← ht]
  have e1 : q * (2 * 2 ^ k) = N + N := by rw [hq]; ring
  rw [e1, show N + N - t = N + (N - t) by omega, pow_add, two_pow_N]; ring

theorem map_layerF (k H : ℕ) : ∀ (E es : List ℕ) (D : List ℕ),
    List.Forall₂ (fun t e => t = N / 2 ^ k * (e / 2)) E es →
    (layerF N H E D).map (Nat.cast : ℕ → Rg) = layF ((2 : Rg) ^ (N / 2 ^ k)) H es (D.map (↑))
  | [], [], _, _ => by simp [layerF, layF]
  | t :: E, e :: es, D, h => by
    rw [List.forall₂_cons] at h
    simp only [layerF, layF, List.map_append, map_bfS, map_bfD, psi_pow h.1, map_layerF k H E es _ h.2,
      List.map_take, List.map_drop]

theorem map_layerI (k H : ℕ) (hK : 2 ^ k ∣ N) : ∀ (E es : List ℕ) (D : List ℕ),
    List.Forall₂ (fun t e => e ≤ 2 * 2 ^ k ∧ t = N / 2 ^ k * (e / 2)) E es → (∀ x ∈ D, x < Fm N) →
    (layerI N H E D).map (Nat.cast : ℕ → Rg) = combI ((2 : Rg) ^ (N / 2 ^ k)) (2 ^ k) H es (D.map (↑))
  | [], [], _, _, _ => by simp [layerI, combI]
  | t :: E, e :: es, D, h, hD => by
    rw [List.forall₂_cons] at h
    have hQ : ∀ q ∈ (D.drop H).take H, q < Fm N :=
      fun q hq => hD q (List.mem_of_mem_drop (List.mem_of_mem_take hq))
    simp only [layerI, combI, List.map_append, map_ibS, map_ibD t _ _ hQ,
      psi_inv_pow hK h.1.1 h.1.2, map_layerI k H hK E es _ h.2 (fun x hx => hD x (List.mem_of_mem_drop hx)),
      List.map_take, List.map_drop]

end Cast

/-! ### Shifts and exponents -/

theorem forall₂_kids {N K : ℕ} {R R' : ℕ → ℕ → Prop}
    (hstep : ∀ t e, R t e → R' (t / 2) (e / 2) ∧ R' (t / 2 + N / 2) (e / 2 + K)) :
    ∀ {E es : List ℕ}, List.Forall₂ R E es → List.Forall₂ R' (kids N E) (kidsE K es)
  | [], [], _ => by simp [kids, kidsE]
  | t :: E, e :: es, h => by
    rw [List.forall₂_cons] at h
    have ih := forall₂_kids hstep h.2
    simp only [kids, kidsE, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    exact List.Forall₂.cons (hstep t e h.1).1 (List.Forall₂.cons (hstep t e h.1).2 ih)

/-- The tape shifts at depth `s` are `(N/K)(e/2)` for the exponents `e` at depth `s`, with
`2^(k-s) ∣ e ≤ 2K`. -/
theorem rel_shiftsAt {N k : ℕ} (hK : 2 ^ k ∣ N) : ∀ s, s < k →
    List.Forall₂ (fun t e => 2 ^ (k - s) ∣ e ∧ e ≤ 2 * 2 ^ k ∧ t = N / 2 ^ k * (e / 2))
      (shiftsAt N s) (expsAt (2 ^ k) s)
  | 0, hk => by
    obtain ⟨q, rfl⟩ := hK
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e1 : 2 ^ (j + 1) * q / 2 ^ (j + 1) = q := Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)
    have e2 : 2 ^ (j + 1) / 2 = 2 ^ j := by rw [pow_succ]; simp
    have e3 : 2 ^ (j + 1) * q / 2 = q * 2 ^ j := by
      rw [pow_succ, show 2 ^ j * 2 * q = 2 * (q * 2 ^ j) by ring]; simp
    simp only [shiftsAt, expsAt, List.forall₂_cons, List.Forall₂.nil, and_true, Nat.sub_zero]
    exact ⟨dvd_rfl, by omega, by rw [e1, e2, e3]⟩
  | s + 1, hk => by
    have ih := rel_shiftsAt hK s (by omega)
    obtain ⟨q, rfl⟩ := hK
    have hq : 2 ^ k * q / 2 ^ k = q := Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)
    obtain ⟨i, hi⟩ : ∃ i, k - s = i + 2 := ⟨k - s - 2, by omega⟩
    have hK2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    refine forall₂_kids (fun t e ⟨hd, hle, ht⟩ => ?_) ih
    rw [hi] at hd
    obtain ⟨r, rfl⟩ := hd
    set w := 2 ^ i * r
    have he : 2 ^ (i + 2) * r = 4 * w := by simp only [w]; rw [pow_add]; ring
    rw [he] at hle ht ⊢
    rw [hq] at ht ⊢
    have h1 : 4 * w / 2 = 2 * w := by omega
    have h2 : 2 * w / 2 = w := by omega
    rw [h1] at ht
    have ht2 : t / 2 = q * w := by
      rw [ht, show q * (2 * w) = 2 * (q * w) by ring]; simp
    have hN2 : 2 ^ k * q / 2 = q * 2 ^ (k - 1) := by
      rw [hK2, show 2 * 2 ^ (k - 1) * q = 2 * (q * 2 ^ (k - 1)) by ring]; simp
    have h3 : (2 * w + 2 ^ k) / 2 = w + 2 ^ (k - 1) := by rw [hK2]; omega
    have hdv : 2 ^ (k - (s + 1)) = 2 ^ (i + 1) := by congr 1; omega
    rw [hdv, h1]
    refine ⟨⟨⟨r, by simp only [w]; rw [pow_succ]; ring⟩, by omega, by rw [ht2, h2]⟩,
      ⟨?_, by omega, by rw [ht2, hN2, h3]; ring⟩⟩
    · have hk' : 2 ^ k = 2 ^ (i + 1) * 2 ^ (s + 1) := by rw [← pow_add]; congr 1; omega
      exact ⟨r + 2 ^ (s + 1), by simp only [w]; rw [hk', pow_succ]; ring⟩

/-! ### The main correspondences -/

section Main

variable {N k : ℕ}

local notation "Rg" => ZMod (2 ^ N + 1)

theorem fwdIter_eq_fwdB (hK : 2 ^ k ∣ N) : ∀ (m s : ℕ), s + m = k → ∀ D : List ℕ,
    D.length = 2 ^ s * 2 ^ m →
    (fwdIter N m (2 ^ m / 2) (shiftsAt N s) D).map (Nat.cast : ℕ → Rg) =
      fwdB ((2 : Rg) ^ (N / 2 ^ k)) (2 ^ k) m (expsAt (2 ^ k) s) (D.map (↑))
  | 0, s, _, D, hD => by
    rw [fwdIter, fwdB_zero _ _ _ _ (by simp [hD, length_expsAt])]
  | m + 1, s, hsm, D, hD => by
    have hm : 2 ^ (m + 1) / 2 = 2 ^ m := by rw [pow_succ]; simp
    have hl : (layerF N (2 ^ m) (shiftsAt N s) D).length = 2 ^ (s + 1) * 2 ^ m := by
      rw [layerF_length N _ _ D (by rw [hD, length_shiftsAt, pow_succ]; ring), length_shiftsAt, pow_succ]
      ring
    rw [fwdIter, hm, show kids N (shiftsAt N s) = shiftsAt N (s + 1) from rfl,
      fwdIter_eq_fwdB hK m (s + 1) (by omega) _ hl]
    have hrel := (rel_shiftsAt hK s (by omega)).imp (fun _ _ h => h.2.2)
    rw [map_layerF k _ _ _ D hrel]
    exact fwdB_layer _ _ m _ _ (by simp [hD, length_expsAt])

/-- The tape's forward transform is the recursive transform. -/
theorem fwdIter_eq_fwd (hK : 2 ^ k ∣ N) (D : List ℕ) (hD : D.length = 2 ^ k) :
    (fwdIter N k (2 ^ k / 2) [N / 2] D).map (Nat.cast : ℕ → Rg) =
      fwd ((2 : Rg) ^ (N / 2 ^ k)) (2 ^ k) k (2 ^ k) (D.map (↑)) := by
  have := fwdIter_eq_fwdB hK k 0 (by omega) D (by simp [hD])
  rw [show [N / 2] = shiftsAt N 0 from rfl, this, expsAt, fwdB, fwdB]
  rw [List.take_of_length_le (by simp [hD])]; simp

theorem invIter_eq_invB (hK : 2 ^ k ∣ N) (X : List Rg) (hX : X.length = 2 ^ k) :
    ∀ s, s ≤ k → ∀ D : List ℕ, D.length = 2 ^ k → (∀ x ∈ D, x < Fm N) →
      D.map (Nat.cast : ℕ → Rg) = invB ((2 : Rg) ^ (N / 2 ^ k)) (2 ^ k) (k - s) (expsAt (2 ^ k) s) X →
      (invIter N s k D).map (Nat.cast : ℕ → Rg) =
        invB ((2 : Rg) ^ (N / 2 ^ k)) (2 ^ k) k (expsAt (2 ^ k) 0) X
  | 0, _, D, _, _, h => by rw [invIter, h]; rfl
  | s + 1, hs, D, hD, hlt, h => by
    rw [invIter]
    have hDl : D.length = (shiftsAt N s).length * (2 * 2 ^ (k - 1 - s)) := by
      rw [hD, length_shiftsAt, ← pow_succ', ← pow_add]; congr 1; omega
    refine invIter_eq_invB hK X hX s (by omega) _
      (by rw [layerI_length N _ _ D hDl, ← hDl, hD]) (layerI_lt N _ _ D) ?_
    have hrel := (rel_shiftsAt hK s (by omega)).imp (fun _ _ h => h.2)
    rw [map_layerI k _ hK _ _ D hrel hlt, h]
    have hks : k - s = (k - 1 - s) + 1 := by omega
    rw [hks, invB_layer _ _ (k - 1 - s) _ X (by
      rw [hX, length_expsAt, ← pow_add]; congr 1; omega)]
    rw [show k - (s + 1) = k - 1 - s by omega]
    rfl

/-- The tape's inverse transform is the recursive inverse transform. -/
theorem invIter_eq_inv (hK : 2 ^ k ∣ N) (D : List ℕ) (hD : D.length = 2 ^ k)
    (hlt : ∀ x ∈ D, x < Fm N) :
    (invIter N k k D).map (Nat.cast : ℕ → Rg) =
      inv ((2 : Rg) ^ (N / 2 ^ k)) (2 ^ k) k (2 ^ k) (D.map (↑)) := by
  rw [invIter_eq_invB hK (D.map (↑)) (by simp [hD]) k le_rfl D hD hlt (by
    rw [Nat.sub_self, invB_zero _ _ _ _ (by simp [hD, length_expsAt])])]
  rw [expsAt, invB, invB, List.take_of_length_le (by simp [hD])]; simp

end Main

end IntegerMultBounds.Schoenhage
