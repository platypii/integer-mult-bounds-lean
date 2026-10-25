module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightBody

/-! A structural table loop generates both weight words at every original
ambient coordinate. The interleaved stream is an intermediate setup page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

/-- Headers retained across coordinate construction and the counted loop. -/
def weightHeaderPort (k : Fin 48) : Prop :=
  k = 18 ∨ k = 19 ∨ k = 22 ∨
    (34 ≤ k.val ∧ k ≠ 37 ∧ k ≠ 40 ∧ k ≠ 41 ∧ k ≠ 45)

instance (k : Fin 48) : Decidable (weightHeaderPort k) := by
  unfold weightHeaderPort
  infer_instance

def weightPairSymbols (A w q P s t u lo i : ℕ) : List (Fin (A + 4)) :=
  let d := PhaseCellConcreteCoefficients.similarity P s t u ((lo + i) % s : ℕ)
  csyms A w (rationalWord q d) ++ csyms A w (reciprocalWeightWord q d)

def weightCoordinate : TblCode 48 := tblBlock 48 [.add 47 45 37] (.mod 37 34 37)

def weightStreamCode : TblCode 48 := tblFor 45 46 (weightCoordinate ;; weightBody)

/-- The table loop preserves the pi, geometry and scale headers and generates
one exact pair per coordinate, including ambient wraparound. -/
theorem weightStreamCode_do {A V w q P s t u lo L : ℕ} (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hdouble : st.val 38 = 2 * s) (hden : st.val 39 = similarityDenominator s t)
    (hq : st.val 42 = 2 ^ q) (hpowP : st.val 43 = 2 ^ P)
    (hqp : st.val 44 = 2 ^ (q + P)) (hL : st.val 46 = L) (hlo : st.val 47 = lo)
    (hP : 13 ≤ P) (hs0 : 0 < s) (hst : s < t)
    (hloV : lo + L < 2 ^ V) (hLV : L < 2 ^ V)
    (hsV : 2 * s < 2 ^ V) (hsq : s ^ 2 < 2 ^ V) (huV : u * s ^ 2 < 2 ^ V)
    (hV : 13 * P + 8 ≤ V) (hqV : q + P + 2 ≤ V)
    (hargs : ∀ j < s, 2 * t * j + s < 2 ^ V ∧
      similarityNumerator s t u j * 2 ^ (5 * P + 2) < 2 ^ V) :
    TblDo A V w weightStreamCode st (fun st' =>
      st'.acc = ((List.range L).flatMap (weightPairSymbols A w q P s t u lo)).reverse ++ st.acc ∧
      ∀ k, weightHeaderPort k → st'.val k = st.val k) (L * (310 * P + 124) + 3) := by
  let F := weightPairSymbols A w q P s t u lo
  let Inv := fun j (s' : TblSt 48 A) =>
    (∀ k, weightHeaderPort k → s'.val k = st.val k) ∧
    s'.acc = ((List.range j).flatMap F).reverse ++ st.acc
  have hloop : TblDo A V w weightStreamCode st (fun st' =>
      st'.acc = ((List.range L).flatMap F).reverse ++ st.acc ∧
      ∀ k, weightHeaderPort k → st'.val k = st.val k)
      (1 + (L * ((2 + (310 * P + 119)) + 1 + 2) + 2)) := by
    apply TblDo.for L (2 + (310 * P + 119)) hL hLV (by decide) Inv
    · constructor
      · intro k hk
        have hk45 : k ≠ 45 := by
          rcases hk with rfl | rfl | rfl | hk <;> simp_all
        simp [hk45]
      · simp [F]
    · intro i hi s₁ ⟨hframe, hacc⟩ hindex hcount
      let s₂ : TblSt 48 A := ⟨Function.update s₁.val 37 ((lo + i) % s), s₁.acc⟩
      have hcoordinate : TblDo A V w weightCoordinate s₁ (fun s' => s' = s₂) 2 := by
        apply TblDo.block
        · simp [tblFitsList, TblIns.fits, hframe 47 (by decide), hlo, hindex]
          omega
        · simp [tblExactList, TblIns.exact, s₂, hframe 47 (by decide),
            hframe 34 (by decide), hlo, hs, hindex]
      have hframe₂ (k : Fin 48) (hk : weightHeaderPort k) : s₂.val k = st.val k := by
        have hk37 : k ≠ 37 := by
          rcases hk with rfl | rfl | rfl | hk <;> simp_all
        simpa [s₂, hk37] using hframe k hk
      have hj : (lo + i) % s < s := Nat.mod_lt _ hs0
      have hbody := weightBody_do (A := A) (V := V) (w := w) s₂
        (by rw [hframe₂ 18 (by decide)]; exact hpi)
        (by rw [hframe₂ 19 (by decide)]; exact hP')
        (by rw [hframe₂ 22 (by decide)]; exact hneg)
        (by rw [hframe₂ 34 (by decide)]; exact hs)
        (by rw [hframe₂ 35 (by decide)]; exact ht)
        (by rw [hframe₂ 36 (by decide)]; exact hu)
        (show s₂.val 37 = (lo + i) % s by simp [s₂])
        (by rw [hframe₂ 38 (by decide)]; exact hdouble)
        (by rw [hframe₂ 39 (by decide)]; exact hden)
        (by rw [hframe₂ 42 (by decide)]; exact hq)
        (by rw [hframe₂ 43 (by decide)]; exact hpowP)
        (by rw [hframe₂ 44 (by decide)]; exact hqp)
        hP hs0 hst (hargs _ hj).1 hsV hsq huV hV (hargs _ hj).2 hqV
      refine hcoordinate.seq (fun s' he => he ▸ hbody.mono ?_ le_rfl)
      intro s₃ ⟨hout, hp, hprec, hsign, hkeep⟩
      have hhigh (k : Fin 48) (hk : 34 ≤ k.val) (hk40 : k ≠ 40) (hk41 : k ≠ 41) :=
        hkeep k hk hk40 hk41
      refine ⟨?_, ?_, ?_⟩
      · exact (hhigh 45 (by decide) (by decide) (by decide)).trans (by simp [s₂, hindex])
      · exact (hhigh 46 (by decide) (by decide) (by decide)).trans (hframe₂ 46 (by decide) |>.trans hL)
      · constructor
        · intro k hk
          have hk45 : k ≠ 45 := by
            rcases hk with rfl | rfl | rfl | hk <;> simp_all
          change Function.update s₃.val 45 (i + 1) k = st.val k
          rw [Function.update_of_ne hk45]
          rcases hk with rfl | rfl | rfl | hk
          · exact hp.trans (hframe₂ 18 (by decide))
          · exact hprec.trans (hframe₂ 19 (by decide))
          · exact hsign.trans (hframe₂ 22 (by decide))
          · exact (hhigh k hk.1 hk.2.2.1 hk.2.2.2.1).trans
              (hframe₂ k (Or.inr (Or.inr (Or.inr hk))))
        · change s₃.acc = _
          rw [hout, show s₂.acc = s₁.acc from rfl, hacc, tbl_range_flatMap_succ]
          simp [F, weightPairSymbols, List.reverse_append, List.append_assoc]
    · intro s' ⟨hf, ha⟩ _ _
      exact ⟨ha, hf⟩
  exact hloop.mono (fun _ h => h) (by ring_nf; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
