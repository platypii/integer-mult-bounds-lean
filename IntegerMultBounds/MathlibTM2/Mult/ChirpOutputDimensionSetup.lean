module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDimensions
public import IntegerMultBounds.MathlibTM2.Mult.ChirpDimensionScope

/-! # Install both shift controls and all finishing counters

The output order is l+1, w-(l+1), Γ, w-Γ, w, q-p, p+l+Γ+5,
unused high bits, and the output symbol count. The binary bank is restored.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U} {rg : TblR 14 → Fin T}

def chirpOutputDimensionSlot : Fin 9 → Fin 14 := ![10, 11, 3, 12, 4, 7, 6, 8, 9]

def chirpOutputAssignments (dst : Fin 9 → Fin T) : List (Fin 14 × Fin T) :=
  [(10, dst 0), (11, dst 1), (3, dst 2), (12, dst 3), (4, dst 4),
    (7, dst 5), (6, dst 6), (8, dst 7), (9, dst 8)]

def chirpOutputDimensionCount (p q l Γ w t : ℕ) : Fin 9 → ℕ :=
  ![l + 1, w - (l + 1), Γ, w - Γ, w, q - p, p + l + Γ + 5,
    w - (q - p) - (p + l + Γ + 5), t * (p + l + Γ + 5)]

def chirpOutputDimensionSetup (rg : TblR 14 → Fin T) (dst : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg tblChirpOutputDimensions)
    (.seq (tblUnaryCopies rg (chirpOutputAssignments dst)) (tblCompile rg tblChirpOutputDimensionsClear))

/-- Install all nine counters from p,q,l,Γ,w,t, charging generation, copies and restoration. -/
theorem chirpOutputDimensionSetup_exec (hrg : Function.Injective rg) (dst : Fin 9 → Fin T)
    (hout : ∀ i r, rg r ≠ dst i) {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 14 A) (p q l Γ w t : ℕ)
    (hp : st.val 0 = p) (hq : st.val 1 = q) (hl : st.val 2 = l)
    (hΓ : st.val 3 = Γ) (hw : st.val 4 = w) (ht : st.val 5 = t)
    (hpq : p ≤ q) (hwidth : q + l + Γ + 5 ≤ w)
    (hvolume : t * (p + l + Γ + 5) < 2 ^ W)
    (hzero : ∀ i : Fin 14, 6 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 25 * tblC W e + unaryCopiesCost W (chirpOutputDimensionValues p q l Γ w t) (chirpOutputAssignments dst) ∧
      Exec body (chirpOutputDimensionSetup rg dst) (mk v S) n
        (mk v' { S with R := (unaryCopiesR (chirpOutputDimensionValues p q l Γ w t) S.R
          (chirpOutputAssignments dst)) }) := by
  apply tblComputedUnaryCopies_exec (body := body) hrg wl nl hwl hnl heW
    tblChirpOutputDimensions tblChirpOutputDimensionsClear st (chirpOutputDimensionValues p q l Γ w t) 17 8
    (tblChirpOutputDimensions_do st p q l Γ w t hp hq hl hΓ hw ht hpq hwidth hvolume hfit)
    (fun z hz => tblChirpOutputDimensionsClear_do st z (by
      intro i hi
      rw [hz]
      fin_cases i <;> first | (simp at hi; done) |
        simp [chirpOutputDimensionValues, hp, hq, hl, hΓ, hw, ht]) hzero)
    hfit (chirpOutputAssignments dst) (by
      intro a ha
      simp only [chirpOutputAssignments, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hout _) v S hS

/-- Every installed counter has exactly its consumer's dimension. -/
theorem chirpOutputDimensions_at (dst : Fin 9 → Fin T) (hdst : Function.Injective dst)
    (p q l Γ w t : ℕ) (R : Regs T A) (i : Fin 9) :
    unaryCopiesR (chirpOutputDimensionValues p q l Γ w t) R (chirpOutputAssignments dst) (dst i) =
      List.replicate (chirpOutputDimensionCount p q l Γ w t i) tick ++ R (dst i) := by
  have hnd : ((chirpOutputAssignments dst).map Prod.snd).Nodup := by
    simp [chirpOutputAssignments, List.nodup_cons, hdst.eq_iff]
  have hmem : (chirpOutputDimensionSlot i, dst i) ∈ chirpOutputAssignments dst := by
    fin_cases i <;> simp [chirpOutputDimensionSlot, chirpOutputAssignments]
  have hval : chirpOutputDimensionValues p q l Γ w t (chirpOutputDimensionSlot i) =
      chirpOutputDimensionCount p q l Γ w t i := by
    fin_cases i <;> simp [chirpOutputDimensionValues, chirpOutputDimensionSlot, chirpOutputDimensionCount]
  simpa only [hval] using unaryCopiesR_at (chirpOutputDimensionValues p q l Γ w t) R
    (chirpOutputAssignments dst) hnd (chirpOutputDimensionSlot i, dst i) hmem

/-- Spectators of the nine counters are unchanged. -/
theorem chirpOutputDimensions_off (dst : Fin 9 → Fin T) (p q l Γ w t : ℕ)
    (R : Regs T A) (k : Fin T) (hk : ∀ i, k ≠ dst i) :
    unaryCopiesR (chirpOutputDimensionValues p q l Γ w t) R (chirpOutputAssignments dst) k = R k := by
  apply unaryCopiesR_off
  intro a ha
  simp only [chirpOutputAssignments, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact (hk _).symm

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
