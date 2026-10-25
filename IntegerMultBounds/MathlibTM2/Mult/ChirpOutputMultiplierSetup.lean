module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpMultiplierSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFactorFrame

/-! # Construct readiness of both output multipliers from one binary bank -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpOutputMultiplierR (O : ChirpOutputLayout T) (q w : ℕ) (R : Regs T A) : Regs T A :=
  unaryCopiesR (chirpMultiplierDimensionValues q w)
    (unaryCopiesR (chirpMultiplierDimensionValues q w) R (chirpMultiplierAssignments O.cr))
    (chirpMultiplierAssignments O.nr)

def chirpOutputMultiplierSetup (O : ChirpOutputLayout T) (rg : TblR 5 → Fin T) : Pr P T Q A U :=
  .seq (chirpMultiplierSetup rg O.cr) (chirpMultiplierSetup rg O.nr)

/-- The shared binary bank is reused and restored; only six readiness counters change. -/
theorem chirpOutputMultiplierSetup_exec (O : ChirpOutputLayout T)
    (rg : TblR 5 → Fin T) (hrg : Function.Injective rg)
    (hoff : ∀ r ∈ [CR.wn, .pn, .nn], ∀ i, rg i ≠ O.cr r ∧ rg i ≠ O.nr r)
    {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 5 A) (q w : ℕ) (hq : st.val 0 = q) (hw : st.val 1 = w) (hw1 : 1 ≤ w)
    (hroom : 4 * w + 2 < 2 ^ W)
    (hzero : ∀ i : Fin 5, 2 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 2 * chirpMultiplierSetupCost W e q w ∧
      Exec body (chirpOutputMultiplierSetup O rg) (mk v S) n
        (mk v' { S with R := chirpOutputMultiplierR O q w S.R }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpMultiplierSetup_exec (body := body) hrg O.cr
    (fun r hr i => (hoff r hr i).1) wl nl hwl hnl heW st q w hq hw hw1 hroom hzero hfit v S hS
  let S₁ : Stacks T A := { S with R :=
    (unaryCopiesR (chirpMultiplierDimensionValues q w) S.R (chirpMultiplierAssignments O.cr)) }
  have hbank : tblHolds rg S₁ (tblRho W wl nl st) := by
    intro i
    exact (chirpMultiplierSetup_off O.cr S.R q w (rg i)
      (hoff .wn (by simp) i).1 (hoff .pn (by simp) i).1 (hoff .nn (by simp) i).1).trans (hS i)
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpMultiplierSetup_exec (body := body) hrg O.nr
    (fun r hr i => (hoff r hr i).2) wl nl hwl hnl heW st q w hq hw hw1 hroom hzero hfit v₁ S₁ hbank
  exact ⟨v₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

/-- Fresh data banks plus the executed counters imply both complete multiplier interfaces. -/
theorem chirpOutputMultiplierSetup_base (O : ChirpOutputLayout T) (hc : O.Cross)
    (S : Stacks T A) (q w : ℕ) (blocks : List (List GaussianInt))
    (hinput : S.R (O.cr .xs) = cstream A w blocks.flatten)
    (hcr : ∀ r, r ≠ .xs → S.R (O.cr r) = []) (hnr : ∀ r, S.R (O.nr r) = [])
    (hmul : CClean O.mul S) :
    ChirpOutputBase O { S with R := chirpOutputMultiplierR O q w S.R } q w blocks := by
  let R₁ := unaryCopiesR (chirpMultiplierDimensionValues q w) S.R (chirpMultiplierAssignments O.cr)
  have hnc (r s : CR) (hs : s ∈ [CR.wn, .pn, .nn]) : O.cr r ≠ O.nr s := by
    exact (hc s r (by intro h; subst s; simp at hs)).symm
  have hcn (r s : CR) (hs : s ∈ [CR.wn, .pn, .nn]) : O.nr r ≠ O.cr s := by
    by_cases hr : r = .xs
    · subst r
      rw [O.link]
      exact O.cr_inj.ne (by intro h; subst s; simp at hs)
    · exact hc r s hr
  have cr_frame (r : CR) : chirpOutputMultiplierR O q w S.R (O.cr r) = R₁ (O.cr r) :=
    chirpMultiplierSetup_off O.nr R₁ q w _
      (hnc r .wn (by simp)) (hnc r .pn (by simp)) (hnc r .nn (by simp))
  have nr_frame (r : CR) : R₁ (O.nr r) = S.R (O.nr r) :=
    chirpMultiplierSetup_off O.cr S.R q w _
      (hcn r .wn (by simp)) (hcn r .pn (by simp)) (hcn r .nn (by simp))
  have nr_blank (r : CR) : R₁ (O.nr r) = [] := (nr_frame r).trans (hnr r)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hf : (fun r => chirpOutputMultiplierR O q w S.R (O.cr r)) = (fun r => R₁ (O.cr r)) := funext cr_frame
    change Ready (fun r => chirpOutputMultiplierR O q w S.R (O.cr r)) w q
    rw [hf]
    exact chirpMultiplierSetup_ready O.cr O.cr_inj S.R q w hcr
  · exact chirpMultiplierSetup_ready O.nr O.nr_inj R₁ q w (fun r _ => nr_blank r)
  · intro j
    refine ⟨(hmul j).1, ?_⟩
    exact (chirpMultiplierSetup_off O.nr R₁ q w _ (O.nr_mul .wn j).symm
      (O.nr_mul .pn j).symm (O.nr_mul .nn j).symm).trans
      ((chirpMultiplierSetup_off O.cr S.R q w _ (O.cr_mul .wn j).symm
        (O.cr_mul .pn j).symm (O.cr_mul .nn j).symm).trans (hmul j).2)
  · exact (cr_frame .xs).trans
      ((chirpMultiplierSetup_off O.cr S.R q w _ (O.cr_inj.ne (by decide))
        (O.cr_inj.ne (by decide)) (O.cr_inj.ne (by decide))).trans hinput)
  · intro r hr
    change chirpOutputMultiplierR O q w S.R (O.cr r) = []
    rw [cr_frame]
    exact (chirpMultiplierSetup_off O.cr S.R q w _
      (O.cr_inj.ne (by intro h; subst r; simp at hr))
      (O.cr_inj.ne (by intro h; subst r; simp at hr))
      (O.cr_inj.ne (by intro h; subst r; simp at hr))).trans (hcr r (by intro h; subst r; simp at hr))
  · intro r hr
    exact (chirpMultiplierSetup_off O.nr R₁ q w _
      (O.nr_inj.ne (by intro h; subst r; simp at hr))
      (O.nr_inj.ne (by intro h; subst r; simp at hr))
      (O.nr_inj.ne (by intro h; subst r; simp at hr))).trans (nr_blank r)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
