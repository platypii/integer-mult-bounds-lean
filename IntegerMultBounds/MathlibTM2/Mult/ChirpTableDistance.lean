module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTables
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! # Execute the squared distance for chirp table arguments

Use unsigned arithmetic and one comparison for the signed distance. Every multiplication
and addition has an explicit no-overflow bound; the subtraction uses the existing safe
absolute-difference routine. The six input variables and emitted stream remain unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- Stable pi/precision inputs and high control variables; 40 and 41 are local scratch. -/
def ChirpTableFrame {A : ℕ} (st z : TblSt 48 A) : Prop :=
  z.val 18 = st.val 18 ∧ z.val 19 = st.val 19 ∧
    ∀ i : Fin 48, 34 ≤ i.val → i ≠ 40 → i ≠ 41 → z.val i = st.val i

theorem chirpTableFrame_refl {A : ℕ} (st : TblSt 48 A) : ChirpTableFrame st st :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem chirpTableFrame_trans {A : ℕ} {x y z : TblSt 48 A}
    (hxy : ChirpTableFrame x y) (hyz : ChirpTableFrame y z) : ChirpTableFrame x z :=
  ⟨hyz.1.trans hxy.1, hyz.2.1.trans hxy.2.1,
    fun i hi h40 h41 => (hyz.2.2 i hi h40 h41).trans (hxy.2.2 i hi h40 h41)⟩

/-- Comparison selects a subtraction without underflow. -/
def tblChirpAbsDiff : TblCode 48 :=
  .ite 25 26 (.ins (.sub 26 25 27)) (.ins (.sub 25 26 27))

theorem tblChirpAbsDiff_do {A W w : ℕ} (st : TblSt 48 A) {P N : ℕ}
    (hP : st.val 25 = P) (hN : st.val 26 = N) (hPW : P < 2 ^ W) (hNW : N < 2 ^ W) :
    TblDo A W w tblChirpAbsDiff st
      (fun z => z = ⟨Function.update st.val 27 (if P < N then N - P else P - N), st.acc⟩) 2 := by
  by_cases h : P < N
  · refine TblDo.iteT (by rw [hP, hN]; exact h) (TblDo.insX _ ?_ ?_)
    · simp only [TblIns.fits, hP, hN]; omega
    · simp [TblIns.exact, hP, hN, h]
  · refine TblDo.iteF (by rw [hP, hN]; exact h) (TblDo.insX _ ?_ ?_)
    · simp only [TblIns.fits, hP, hN]; omega
    · simp [TblIns.exact, hP, hN, h]

theorem chirp_absdiff_sq (P N : ℕ) :
    ((if P < N then N - P else P - N : ℕ) : ℤ) ^ 2 = ((P : ℤ) - N) ^ 2 := by
  split_ifs with h
  · rw [Nat.cast_sub h.le]; ring
  · rw [Nat.cast_sub (not_lt.mp h)]

/-- Unsigned square of the distance with the specified left-window offset. -/
def chirpDistanceSquare (s t offset k0 a : ℕ) : ℕ :=
  let P := t * (s * k0 / t + a)
  let N := s * k0 + t * offset
  (if P < N then N - P else P - N) ^ 2

/-- The unsigned arithmetic computes exactly the integer square used by the input table. -/
theorem chirpDistanceSquare_eq (s t m k0 a : ℕ) :
    chirpDistanceSquare s t m k0 a = chirpSquare s t m k0 a := by
  have hc : ((chirpDistanceSquare s t m k0 a : ℕ) : ℤ) = chirpDelta s t m k0 a ^ 2 := by
    unfold chirpDistanceSquare
    rw [Nat.cast_pow, chirp_absdiff_sq]
    congr 1
    simp only [chirpDelta, chirpStart, Nat.cast_add, Nat.cast_mul]
    ring
  exact Int.ofNat_inj.mp (hc.trans (Int.toNat_of_nonneg (sq_nonneg _)).symm)

/-- A shifted kernel index uses offset `2m-1` in the same unsigned routine. -/
theorem chirpDistanceSquare_kernel (s t m k0 j : ℕ) (hm : 1 ≤ m) :
    chirpDistanceSquare s t (2 * m - 1) k0 j =
      chirpSquare s t m k0 ((j : ℤ) - (m - 1 : ℕ)) := by
  rw [chirpDistanceSquare_eq]
  unfold chirpSquare chirpDelta chirpStart
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * m), Nat.cast_sub hm]
  push_cast
  ring

/-- Arguments: `s,t` in 34,35, offset in 37, block origin in 38, index in 39; result in 27. -/
def tblChirpDistancePrefix : List (TblIns 48) :=
  [.mul 34 38 40, .div 40 35 41, .add 41 39 41, .mul 35 41 25, .mul 35 37 26]

def tblChirpDistance : TblCode 48 :=
  .seq (tblBlock 48 tblChirpDistancePrefix (.add 40 26 26))
    (.seq tblChirpAbsDiff (.ins (.mul 27 27 27)))

/-- The distance routine uses nine actual table-machine atoms. -/
theorem tblChirpDistance_do {A W w : ℕ} (st : TblSt 48 A) (s t offset k0 a : ℕ)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (ho : st.val 37 = offset)
    (hk : st.val 38 = k0) (ha : st.val 39 = a)
    (hsk : s * k0 < 2 ^ W) (hadd : s * k0 / t + a < 2 ^ W)
    (hP : t * (s * k0 / t + a) < 2 ^ W) (hto : t * offset < 2 ^ W)
    (hN : s * k0 + t * offset < 2 ^ W) (hsq : chirpDistanceSquare s t offset k0 a < 2 ^ W) :
    TblDo A W w tblChirpDistance st
      (fun z => z.val 27 = chirpDistanceSquare s t offset k0 a ∧ z.acc = st.acc ∧
        ChirpTableFrame st z) 9 := by
  let P := t * (s * k0 / t + a)
  let N := s * k0 + t * offset
  let pre := tblChirpDistancePrefix ++ [.add 40 26 26]
  let st₁ := tblExactList A w pre st
  have hf : tblFitsList A W w pre st := by
    simp [pre, tblChirpDistancePrefix, tblFitsList, TblIns.fits, TblIns.exact,
      hs, ht, ho, hk, ha, hsk, hadd, hP, hto, hN]
  have hp : st₁.val 25 = P := by simp [st₁, pre, P, tblChirpDistancePrefix, tblExactList, TblIns.exact, hs, ht, ho, hk, ha]
  have hn : st₁.val 26 = N := by simp [st₁, pre, N, tblChirpDistancePrefix, tblExactList, TblIns.exact, hs, ht, ho, hk, ha]
  have hacc : st₁.acc = st.acc := by simp [st₁, pre, tblChirpDistancePrefix, tblExactList, TblIns.exact]
  have hpre := TblDo.block tblChirpDistancePrefix (.add 40 26 26) hf (P := fun z => z = st₁) rfl
  let st₂ : TblSt 48 A := ⟨Function.update st₁.val 27 (if P < N then N - P else P - N), st₁.acc⟩
  have hlast : TblDo A W w (.ins (.mul 27 27 27)) st₂
      (fun z => z.val 27 = chirpDistanceSquare s t offset k0 a ∧ z.acc = st.acc ∧
        ChirpTableFrame st z) 1 := by
    refine TblDo.insX (.mul 27 27 27) ?_ ?_
    · change (if P < N then N - P else P - N) * (if P < N then N - P else P - N) < 2 ^ W
      rw [← pow_two]
      exact hsq
    · refine ⟨?_, ?_, ?_⟩
      · change (if P < N then N - P else P - N) * (if P < N then N - P else P - N) =
          chirpDistanceSquare s t offset k0 a
        rw [← pow_two]
        rfl
      · exact hacc
      · refine ⟨?_, ?_, ?_⟩
        · simp [st₂, st₁, pre, tblChirpDistancePrefix, tblExactList, TblIns.exact]
        · simp [st₂, st₁, pre, tblChirpDistancePrefix, tblExactList, TblIns.exact]
        · intro i hi h40 h41
          have h25 : i ≠ 25 := by intro h; subst i; norm_num at hi
          have h26 : i ≠ 26 := by intro h; subst i; norm_num at hi
          have h27 : i ≠ 27 := by intro h; subst i; norm_num at hi
          simp [st₂, st₁, pre, tblChirpDistancePrefix, tblExactList, TblIns.exact,
            h25, h26, h27, h40, h41]
  have htail := (tblChirpAbsDiff_do (w := w) st₁ hp hn hP hN).seq (fun z hz => by cases hz; exact hlast)
  exact (hpre.seq (fun z hz => by cases hz; exact htail)).mono (fun z h => h)
    (by simp [tblChirpDistancePrefix])

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
