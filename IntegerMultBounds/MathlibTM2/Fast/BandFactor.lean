module

public import IntegerMultBounds.MathlibTM2.Fast.BandLine
public import IntegerMultBounds.MathlibTM2.Mult.BandTranspose
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The banded factorization: Newton reciprocals of the pivots

The window factorization of `Mult.BandFactor` needs, for each pivot `c`, the
Newton reciprocal `newtonZ P c K`. One Newton step keeps `c` on `hv` and the
current reciprocal `r` on `xa`; it forms `t = c r` and `q = r t` by truncated
record products and replaces `r` by `r - (q - r) = 2r - q` with two record
subtractions, so no constant record is needed.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node


variable {T Q A : ℕ} {U : Type} {P : Type}

section Programs

variable (rg : RsbR → Fin T) {ι : Fin 64 → Fin T} (hι : Function.Injective ι) (hT : 64 ≤ T)
  (hQ : SS.states ≤ Q)

/-- One Newton step on the reciprocal `xa` of the pivot `hv`. -/
noncomputable def bandNewtonStepP : Pr P T Q A U :=
  .seq (cmulStream (rsbCr rg .hv .xa .hc) (rmulOne ι hι hT hQ (rsbCr rg .hv .xa .hc)))
  (.seq (rsbCopyTo rg .xa .ya)
  (.seq (moveR (rg .hc) (rg .ac2) id)
  (.seq (moveR (rg .ac2) (rg .xs) id)
  (.seq (cmulStream (rsbCr rg .ya .xs .pr) (rmulOne ι hι hT hQ (rsbCr rg .ya .xs .pr)))
  (.seq (emptyR (rg .ya)) (.seq (emptyR (rg .xs))
  (.seq (rsbCopyTo rg .xa .ac)
  (.seq (rsbSubWord (rg .pr) (rg .ac) (rg .ac2) (rg (.cm .wn)) (rg .tA))
  (.seq (moveR (rg .ac2) (rg .nv) id)
  (.seq (rsbSubWord (rg .xa) (rg .nv) (rg .ac2) (rg (.cm .wn)) (rg .tA))
  (moveR (rg .ac2) (rg .xa) id)))))))))))

/-- The Newton reciprocal of the pivot `hv` onto `xa`: start from the constant
record on `bx`, then one step per symbol of `kn`. -/
noncomputable def bandNewtonP : Pr P T Q A U :=
  .seq (rsbCopyTo rg .bx .xa) (rsbRep (rg .kn) (rg .tK) (bandNewtonStepP rg hι hT hQ))

/-- One non-pivot row of a window step: multiplier by the stored reciprocal,
row update against the pivot-row copy on `ef`, then the updated row moves to
the new window `sr` (reversed) followed by the zero record of `msk`. -/
noncomputable def bandFacRowP : Pr P T Q A U :=
  .seq (bandBwdStepP rg hι hT hQ) (.seq (rsbMv (rg .mwn) (rg .tC) (rg .vk) (rg .sr))
    (copyR (rg .msk) (rg .sr) (rg .tC) id))

/-- The `B` non-pivot rows of a window step, one per symbol of `ms`. -/
noncomputable def bandFacRowsP : Pr P T Q A U := rsbRep (rg .ms) (rg .tL) (bandFacRowP rg hι hT hQ)

/-- One window step: pivot row out to `hf`, its Newton reciprocal out to `df`,
the `B` non-pivot rows updated into the new window, the next input row of `src`
appended. -/
noncomputable def bandFacStepP : Pr P T Q A U :=
  .seq (bandPopP rg)
  (.seq (rsbMv (rg .mwn) (rg .tC) (rg .vk) (rg .ac2))
  (.seq (moveR (rg .ac2) (rg .bo) id)
  (.seq (bandNewtonP rg hι hT hQ)
  (.seq (rsbCopyTo rg .bo .hf) (.seq (rsbCopyTo rg .hv .hf)
  (.seq (rsbCopyTo rg .xa .df)
  (.seq (rsbRep (rg .ms) (rg .tL) (rsbCopyTo rg .bo .ef))
  (.seq (rsbRep (rg .ms) (rg .tL) (rsbCopyTo rg .xa .tb))
  (.seq (emptyR (rg .hv)) (.seq (emptyR (rg .xa)) (.seq (emptyR (rg .bo))
  (.seq (bandFacRowsP rg hι hT hQ)
  (.seq (rsbMv (rg .smwn) (rg .tC) (rg .src) (rg .sr))
  (moveR (rg .sr) (rg .vk) id))))))))))))))

/-- The window factorization: one window step per symbol of `sn`. -/
noncomputable def bandFacLoopP : Pr P T Q A U := rsbRep (rg .sn) (rg .sel) (bandFacStepP rg hι hT hQ)

/-- One block of a transpose step: head to `ya`, rest to `nv` followed by a zero. -/
def bandTBlkP : Pr P T Q A U :=
  .seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg .vk) (rg .ya))
  (.seq (rsbMv (rg .m2wn) (rg .tC) (rg .vk) (rg .nv)) (copyR (rg .msk) (rg .nv) (rg .tC) id))

/-- One transpose step: the next pivot row of `src` gives the new first block;
the block heads become the column pushed onto `ef`. -/
def bandTStepP : Pr P T Q A U :=
  .seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg .src) (rg .pr)) (.seq (emptyR (rg .pr))
  (.seq (rsbMv (rg .mwn) (rg .tC) (rg .src) (rg .xs))
  (.seq (rsbMv (rg .mwn) (rg .tC) (rg .src) (rg .pr)) (.seq (emptyR (rg .pr))
  (.seq (rsbRep (rg .ms) (rg .tL) (bandTBlkP rg))
  (.seq (rsbMv (rg (.cm .wn)) (rg .tC) (rg .vk) (rg .ya))
  (.seq (rsbMv (rg .m2wn) (rg .tC) (rg .vk) (rg .pr)) (.seq (emptyR (rg .pr))
  (.seq (moveR (rg .ya) (rg .ef) id)
  (.seq (moveR (rg .nv) (rg .vk) id) (moveR (rg .xs) (rg .vk) id)))))))))))

/-- The transpose: one transpose step per symbol of `sn`. -/
def bandTLoopP : Pr P T Q A U := rsbRep (rg .sn) (rg .sel) (bandTStepP rg)

/-- Reverse the order of the blocks of `x` onto `y`: each block (`|c|` symbols) moves
through `ac2`, one block per symbol of `n`. -/
def bandRevP (x y c n tn : RsbR) : Pr P T Q A U :=
  rsbRep (rg n) (rg tn) (.seq (rsbMv (rg c) (rg .tC) (rg x) (rg .ac2)) (moveR (rg .ac2) (rg y) id))

/-- Reorganize the factor outputs: `m2n := ms`, the multipliers in order onto `bo`, the
pivot rows in order onto `src`, the zero window onto `vk`, then the transpose counters. -/
def bandAxisOrgP : Pr P T Q A U :=
  .seq (emptyR (rg .m2n)) (.seq (rsbCopyTo rg .ms .m2n)
  (.seq (emptyR (rg .kn)) (.seq (rsbRep (rg .sn) (rg .sel) (rsbCopyTo rg .ms .kn))
  (.seq (bandRevP rg .dout .bo (.cm .wn) .kn .tK)
  (.seq (bandRevP rg .hf .src .smwn .sn .sel)
  (.seq (rsbRep (rg .ms) (rg .tL) (rsbCopyTo rg .msk .xs))
  (.seq (rsbRep (rg .ms) (rg .tL) (rsbCopyTo rg .xs .vk)) (.seq (emptyR (rg .xs))
  (.seq (emptyR (rg .ms)) (.seq (rsbCopyTo rg .dst .ms)
  (.seq (emptyR (rg .mwn)) (.seq (rsbCopyTo rg .m2wn .mwn) (rsbCopyTo rg (.cm .wn) .mwn)))))))))))))

/-- Split off the initial window, factor, drop the final window. -/
noncomputable def bandAxisFacP : Pr P T Q A U :=
  .seq (rsbMv (rg .tswn) (rg .tC) (rg .src) (rg .ac2)) (.seq (moveR (rg .ac2) (rg .vk) id)
    (.seq (bandFacLoopP rg hι hT hQ) (emptyR (rg .vk))))

/-- Transpose, drop the final window, store the backward columns on `hf`. -/
def bandAxisTrP : Pr P T Q A U :=
  .seq (bandTLoopP rg) (.seq (emptyR (rg .vk)) (.seq (moveR (rg .ef) (rg .ac2) id)
    (moveR (rg .ac2) (rg .hf) id)))

/-- The per-axis preparation of the banded line solve. -/
noncomputable def bandAxisPrepP : Pr P T Q A U :=
  .seq (bandAxisFacP rg hι hT hQ) (.seq (bandAxisOrgP rg) (bandAxisTrP rg))

end Programs

/-- A Newton step on real records. -/
def newtonStepZ (P : ℕ) (c r : ℤ) : ℤ := 2*r-(r*(c*r).tdiv (2^P)).tdiv (2^P)

lemma tdivN_real (P : ℕ) (a b : ℤ) :
    tdivN P ((⟨a, 0⟩ : GaussianInt)*⟨b, 0⟩)=⟨(a*b).tdiv (2^P), 0⟩ := by
  ext <;> simp [tdivN]

lemma newtonZ_succ (P : ℕ) (c : ℤ) (n : ℕ) :
    Mult.BandFactor.newtonZ P c (n+1)=newtonStepZ P c (Mult.BandFactor.newtonZ P c n) := rfl

lemma machine_row (P : ℕ) (x : ℤ) : ∀ (n : ℕ) (u v : List ℤ), u.length=n → v.length=n →
    List.zipWith (· - ·) (colC v) (List.zipWith (fun a b => tdivN P (a * b))
      (List.replicate n (⟨x, 0⟩ : GaussianInt)) (colC u))=colC (Mult.BandFactor.subRowZ P x u v)
  | 0, [], [], _, _ => rfl
  | n+1, a::u, b::v, hu, hv => by
    have ih := machine_row P x n u v (by simpa using hu) (by simpa using hv)
    simp only [colC, List.map_cons, List.replicate_succ, List.zipWith_cons_cons,
      Mult.BandFactor.subRowZ] at ih ⊢
    rw [ih, tdivN_real]
    congr 1
  | 0, _::_, _, hu, _ => by simp at hu
  | 0, [], _::_, _, hv => by simp at hv
  | _+1, [], _, hu, _ => by simp at hu
  | _+1, _::_, [], _, hv => by simp at hv

section Contracts

variable {body : P → Pr P T Q A U} {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

/-- The cost of one Newton step. -/
def bandNewtonStepCost (w : ℕ) : ℕ := 2 * rmulCost w + 80 * w + 120

/-- One Newton step: `xa` goes from `r` to `2r - r(cr)`, truncated, everything else kept. -/
theorem band_newtonStep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (c r : ℤ)
    (hfc : Fits w (⟨c, 0⟩ : GaussianInt)) (hfr : Fits w (⟨r, 0⟩ : GaussianInt))
    (hft : Fits w (⟨(c*r).tdiv (2^P), 0⟩ : GaussianInt))
    (hhv : σ .hv = csyms A w ⟨c, 0⟩) (hxa : σ .xa = csyms A w ⟨r, 0⟩)
    (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = []) (hpr : σ .pr = []) (hac : σ .ac = [])
    (hac2 : σ .ac2 = []) (hnv : σ .nv = []) (hb1 : σ .b1 = []) (htC : σ .tC = [])
    (htA : σ .tA = []) :
    RsbRuns body rg ι (bandNewtonStepP rg hι hT hQ) σ
      (Function.update σ .xa (csyms A w ⟨newtonStepZ P c r, 0⟩))
      (bandNewtonStepCost w) := by
  have hwn := hready.wn
  set t : ℤ := (c*r).tdiv (2^P) with ht
  set q : ℤ := (r*t).tdiv (2^P) with hq
  -- t = c r
  have h₁ := rsb_rmulStream_runs (body := body) hrg hdisj hι hT hQ hA bandFree_hv (ρ := σ)
    hready hw hp [⟨c, 0⟩] [⟨r, 0⟩] rfl (by simpa using hfc) (by simpa using hfr)
    (by simp [hhv, cstream]) (by simp [hxa, cstream])
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, tdivN_real, hhc, List.append_nil,
    cstream, List.flatMap_cons, List.flatMap_nil] at h₁
  set σ₁ := Function.update σ .hc (csyms A w ⟨t, 0⟩)
  -- ya = r
  have h₂ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .ya)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₁ (by simp [σ₁, hb1])
    (by simp [σ₁, htC])
  set σ₂ := Function.update σ₁ .ya (σ₁ .xa ++ σ₁ .ya)
  -- xs = t
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .hc) (b := .ac2) (by decide) σ₂
  set σ₃ := Function.update (Function.update σ₂ .hc []) .ac2 ((σ₂ .hc).reverse ++ σ₂ .ac2)
  have h₄ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .xs) (by decide) σ₃
  set σ₄ := Function.update (Function.update σ₃ .ac2 []) .xs ((σ₃ .ac2).reverse ++ σ₃ .xs)
  have hready₄ : RsbReady σ₄ w P := by
    simp only [σ₄, σ₃, σ₂, σ₁]
    exact (((((hready.update .hc (fun c => by simp) _).update .ya (fun c => by simp) _).update
      .hc (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2 (fun c => by simp)
      _).update .xs (fun c => by simp) _
  -- q = r t
  have h₅ := rsb_rmulStream_runs (body := body) hrg hdisj hι hT hQ hA bandFree_ya (ρ := σ₄)
    hready₄ hw hp [⟨r, 0⟩] [⟨t, 0⟩] rfl (by simpa using hfr) (by simpa using hft)
    (by simp [σ₄, σ₃, σ₂, σ₁, hya, hxa, cstream]) (by simp [σ₄, σ₃, σ₂, σ₁, hac2, hxs, cstream])
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, tdivN_real, cstream,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at h₅
  set σ₅ := Function.update σ₄ .pr (csyms A w ⟨q, 0⟩ ++ σ₄ .pr)
  have h₆ := rsb_emptyR_runs (body := body) (ι := ι) hrg .ya σ₅
  have h₇ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xs (Function.update σ₅ .ya [])
  set σ₇ := Function.update (Function.update σ₅ .ya []) .xs []
  -- ac = r
  have h₈ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .ac)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₇
    (by simp [σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hb1]) (by simp [σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₈ := Function.update σ₇ .ac (σ₇ .xa ++ σ₇ .ac)
  -- ac2 = rev (q - r)
  have h₉ := rsb_subWord_runs (body := body) (ι := ι) hrg hA (a := .pr) (b := .ac) (o := .ac2)
    (ctr := .cm .wn) (tmp := .tA) (w := w) (by decide) σ₈ ⟨q, 0⟩ ⟨r, 0⟩ [] []
    (by simp [σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hpr])
    (by simp [σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hxa, hac])
    (by simp [σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hwn]) (by simp [σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
  set σ₉ := Function.update (Function.update (Function.update σ₈ .pr []) .ac []) .ac2
    ((csyms A w (⟨q, 0⟩-⟨r, 0⟩)).reverse ++ σ₈ .ac2)
  have h₁₀ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .nv) (by decide) σ₉
  set σ₁₀ := Function.update (Function.update σ₉ .ac2 []) .nv ((σ₉ .ac2).reverse ++ σ₉ .nv)
  -- ac2 = rev (r - (q - r))
  have h₁₁ := rsb_subWord_runs (body := body) (ι := ι) hrg hA (a := .xa) (b := .nv) (o := .ac2)
    (ctr := .cm .wn) (tmp := .tA) (w := w) (by decide) σ₁₀ ⟨r, 0⟩ (⟨q, 0⟩-⟨r, 0⟩) [] []
    (by simp [σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hxa])
    (by simp [σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hac2, hnv])
    (by simp [σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hwn])
    (by simp [σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
  set σ₁₁ := Function.update (Function.update (Function.update σ₁₀ .xa []) .nv []) .ac2
    ((csyms A w (⟨r, 0⟩-(⟨q, 0⟩-⟨r, 0⟩))).reverse ++ σ₁₀ .ac2)
  have h₁₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .xa) (by decide) σ₁₁
  have hval : (⟨r, 0⟩ : GaussianInt)-(⟨q, 0⟩-⟨r, 0⟩)=⟨newtonStepZ P c r, 0⟩ := by
    ext <;> simp [newtonStepZ, hq, ht]; ring
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj h₆ (RsbRuns.seq hdisj h₇
    (RsbRuns.seq hdisj h₈ (RsbRuns.seq hdisj h₉ (RsbRuns.seq hdisj h₁₀
    (RsbRuns.seq hdisj h₁₁ h₁₂))))))))))).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₁₁, σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hhc, hya, hxs, hpr,
      hac, hac2, hnv, hval]
  · simp [σ₁₁, σ₁₀, σ₉, σ₈, σ₇, σ₅, σ₄, σ₃, σ₂, σ₁, hya, hxs, hpr, hac, hac2, hnv, hxa,
      bandNewtonStepCost]
    omega

/-- The Newton loop: `xa` ends with `newtonZ P c K`. -/
theorem band_newton_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P K : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (c : ℤ) (hfc : Fits w (⟨c, 0⟩ : GaussianInt))
    (hfit : ∀ n < K, Fits w (⟨Mult.BandFactor.newtonZ P c n, 0⟩ : GaussianInt) ∧
      Fits w (⟨(c*Mult.BandFactor.newtonZ P c n).tdiv (2^P), 0⟩ : GaussianInt))
    (hbx : σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P c 0, 0⟩)
    (hhv : σ .hv = csyms A w ⟨c, 0⟩) (hxa : σ .xa = [])
    (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = []) (hpr : σ .pr = []) (hac : σ .ac = [])
    (hac2 : σ .ac2 = []) (hnv : σ .nv = []) (hb1 : σ .b1 = []) (htC : σ .tC = [])
    (htA : σ .tA = []) (htK : σ .tK = []) (hkn : (σ .kn).length = K) :
    RsbRuns body rg ι (bandNewtonP rg hι hT hQ) σ
      (Function.update σ .xa (csyms A w ⟨Mult.BandFactor.newtonZ P c K, 0⟩))
      (6 * w + 6 + (K * (bandNewtonStepCost w + 6) + 4)) := by
  have hcsl : (csyms A w (⟨Mult.BandFactor.newtonZ P c 0, 0⟩ : GaussianInt)).length = w := by
    simp [csyms]
  have h₁ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .bx) (b := .xa)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ hb1 htC
  rw [hbx, hxa, List.append_nil, hcsl] at h₁
  set σ₁ := Function.update σ .xa (csyms A w ⟨Mult.BandFactor.newtonZ P c 0, 0⟩)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update σ .xa (csyms A w ⟨Mult.BandFactor.newtonZ P c j, 0⟩) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ₁ .kn).length, ∀ X Y, RsbRuns body rg ι (bandNewtonStepP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .kn X .tK Y) (rsbUpd2 (Ψ (j + 1)) .kn X .tK Y) (bandNewtonStepCost w) := by
    intro j hj X Y
    have hj' : j < K := by simpa [σ₁, hkn] using hj
    have hready' : RsbReady (rsbUpd2 (Ψ j) .kn X .tK Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact ((hready.update .xa (fun c => by simp) _).update .kn (fun c => by simp) _).update .tK
        (fun c => by simp) _
    have hstep := band_newtonStep_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA
      (rsbUpd2 (Ψ j) .kn X .tK Y) hready' hw hp c (Mult.BandFactor.newtonZ P c j) hfc
      (hfit j hj').1 (hfit j hj').2 (by simp [rsbUpd2, hΨ, hhv]) (by simp [rsbUpd2, hΨ])
      (by simp [rsbUpd2, hΨ, hhc]) (by simp [rsbUpd2, hΨ, hya]) (by simp [rsbUpd2, hΨ, hxs])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hac]) (by simp [rsbUpd2, hΨ, hac2])
      (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, hb1]) (by simp [rsbUpd2, hΨ, htC])
      (by simp [rsbUpd2, hΨ, htA])
    refine hstep.congr ?_
    funext r; cases r <;> simp [rsbUpd2, hΨ, newtonZ_succ]
  have h₂ := rsb_rep_runs hrg hdisj (ra := .kn) (rt := .tK) (by decide)
    (bandNewtonStepP rg hι hT hQ) (σ₁ .kn) Ψ _ hbody
  refine ((RsbRuns.seq hdisj h₁ ((h₂.congr_pre ?_).congr ?_)).mono ?_)
  · funext r; cases r <;> simp [rsbUpd2, hΨ, σ₁, htK]
  · funext r; cases r <;> simp [rsbUpd2, hΨ, σ₁, htK, hkn]
  · simp [σ₁, hkn]

/-- The cost of one non-pivot row (rows of `2B` tail records). -/
def bandFacRowCost (w B : ℕ) : ℕ :=
  rmulCost w + 30 * w + 40 + bandFwdStepCost w (2 * B) + 4 * (2 * B * w) + 4 * w + 8

/-- One non-pivot row: `vk` loses the row, `dout` gains its multiplier `x`, and `sr`
gains the updated tail followed by a zero record, reversed. -/
theorem band_facRow_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (q : GaussianInt) (r : ℤ) (rs more col cols : List GaussianInt)
    (hrs : rs.length = 2 * B) (hcol : col.length = 2 * B) (hfq : Fits w q)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt)) (hfx : Fits w (tdivN P (q * ⟨r, 0⟩)))
    (hfc : ∀ a ∈ col, Fits w a ∧ a.im = 0) (D TB SR : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (q :: (rs ++ more))) (htb : σ .tb = csyms A w ⟨r, 0⟩ ++ TB)
    (hef : σ .ef = cstream A w (col ++ cols)) (hsr : σ .sr = SR)
    (hmsk : σ .msk = csyms A w 0)
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hxa : σ .xa = []) (hhc : σ .hc = [])
    (hm2n : (σ .m2n).length = 2 * B) (hmwn : (σ .mwn).length = 2 * B * w) :
    RsbRuns body rg ι (bandFacRowP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w more)) .tb TB) .ef (cstream A w cols)) .dout
        (csyms A w (tdivN P (q * ⟨r, 0⟩)) ++ D)) .sr
        ((cstream A w (List.zipWith (· - ·) rs
          (List.zipWith (fun a b => tdivN P (a * b))
            (List.replicate (2 * B) (tdivN P (q * ⟨r, 0⟩))) col) ++ [0])).reverse ++ SR))
      (bandFacRowCost w B) := by
  set rs' := List.zipWith (· - ·) rs (List.zipWith (fun a b => tdivN P (a * b))
    (List.replicate (2 * B) (tdivN P (q * ⟨r, 0⟩))) col) with hrs'
  have hrs'l : rs'.length = 2 * B := by simp [hrs', hrs, hcol]
  have h₁ := band_bwdStep_runs (body := body) (ι := ι) (w := w) (B := 2 * B) hrg hdisj hι
    hT hQ hA σ hready hw hp q r rs more col cols hrs hcol hfq hfr hfx hfc D TB hvk htb hef hdout
    hhv hya hxs hpr hnv hac hac2 htC htA htJ hb1 hxa hhc hm2n hmwn
  rw [← hrs'] at h₁
  set σ₁ := Function.update (Function.update (Function.update (Function.update σ .vk
    (cstream A w (rs' ++ more))) .tb TB) .ef (cstream A w cols)) .dout
    (csyms A w (tdivN P (q * ⟨r, 0⟩)) ++ D)
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .vk) (y := .sr)
    (by decide) σ₁ (by simp [σ₁, htC]) (by simp [σ₁, hmwn, hrs'l])
  have hmw : (σ₁ .mwn).length = rs'.length * w := by simp [σ₁, hmwn, hrs'l]
  rw [hmw] at h₂
  simp only [σ₁, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.dout),
    Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.ef),
    Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.tb), Function.update_self,
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.dout),
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.ef),
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.tb),
    Function.update_of_ne (by decide : RsbR.sr ≠ RsbR.vk), hsr, cstream_append,
    take_cstream rs' rs'.length le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append] at h₂
  set σ₂ := Function.update (Function.update σ₁ .vk (cstream A w more)) .sr
    ((cstream A w rs').reverse ++ SR)
  have h₃ := rsb_copyR_runs (body := body) (ι := ι) hrg (a := .msk) (b := .sr) (t := .tC)
    (by decide) (by decide) (by decide) σ₂ (by simp [σ₂, σ₁, htC])
  have h₂' := h₂.congr_pre (ρ₀ := σ₁) (by simp only [σ₁, cstream_append])
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj (h₂'.congr ?_) h₃)).congr ?_).mono ?_
  · simp only [σ₂, σ₁, cstream_append]
  · funext x; cases x <;> simp [σ₂, σ₁, hmsk, cstream_append, List.reverse_append]
  · simp [σ₂, σ₁, hmsk, bandFacRowCost, hrs'l, csyms]
    nlinarith

/-- The multiplier of a row with head `h` and pivot reciprocal `r`. -/
def facMul (P : ℕ) (r : ℤ) (row : List ℤ) : ℤ := (row.headD 0*r).tdiv (2^P)

/-- The updated, shifted row. -/
def facRow (P : ℕ) (r : ℤ) (tail0 row : List ℤ) : List ℤ :=
  Mult.BandFactor.subRowZ P (facMul P r row) tail0 row.tail++[0]

/-- The window after `m` steps of the numerator factorization. -/
def facState (P K : ℕ) (rows inputs : List (List ℤ)) : ℕ → List (List ℤ)
  | 0 => rows
  | m+1 => Mult.BandFactor.stepRowsZ P K (facState P K rows inputs m) (inputs.getD m [])

lemma facMul_eq (P K : ℕ) (c : ℤ) (row : List ℤ) :
    facMul P (Mult.BandFactor.newtonZ P c K) row=Mult.BandFactor.mulZ P K (row.headD 0) c := rfl

lemma stepRowsZ_cons (P K : ℕ) (c : ℤ) (tail0 next : List ℤ) (rest : List (List ℤ)) :
    Mult.BandFactor.stepRowsZ P K ((c :: tail0) :: rest) next=
      rest.map (fun row => facRow P (Mult.BandFactor.newtonZ P c K) tail0 row)++[next] := by
  simp [Mult.BandFactor.stepRowsZ, facRow, facMul_eq]

lemma lcolZ_cons (P K : ℕ) (c : ℤ) (tail0 : List ℤ) (rest : List (List ℤ)) :
    Mult.BandFactor.lcolZ P K ((c :: tail0) :: rest)=
      rest.map (fun row => facMul P (Mult.BandFactor.newtonZ P c K) row) := by
  simp [Mult.BandFactor.lcolZ, facMul_eq]

/-- The window keeps its shape: `B+1` rows of `2B+1` entries. -/
lemma facState_shape (P K B : ℕ) (rows inputs : List (List ℤ)) (hrows : rows.length=B+1)
    (hrl : ∀ row ∈ rows, row.length=2*B+1) (hin : ∀ row ∈ inputs, row.length=2*B+1) (m : ℕ)
    (hm : m ≤ inputs.length) :
    (facState P K rows inputs m).length=B+1 ∧
      ∀ row ∈ facState P K rows inputs m, row.length=2*B+1 := by
  induction m with
  | zero => exact ⟨hrows, hrl⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    simp only [facState]
    obtain ⟨row0, rest, hr⟩ : ∃ row0 rest, facState P K rows inputs m=row0 :: rest := by
      cases h : facState P K rows inputs m with
      | nil => rw [h] at h1; simp at h1
      | cons a l => exact ⟨a, l, rfl⟩
    have hr0 := h2 row0 (by rw [hr]; simp)
    obtain ⟨c, tail0, hc⟩ : ∃ c tail0, row0=c :: tail0 := by
      cases row0 with
      | nil => simp at hr0
      | cons a l => exact ⟨a, l, rfl⟩
    rw [hr, hc, stepRowsZ_cons]
    have hnx : (inputs.getD m []).length=2*B+1 := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hin _ (List.getElem_mem _)
    have htl : tail0.length=2*B := by rw [hc] at hr0; simp at hr0; omega
    refine ⟨by rw [hr] at h1; simp at h1 ⊢; omega, fun row hrow => ?_⟩
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hrow
    rcases hrow with ⟨row', hrow', rfl⟩ | rfl
    · have := h2 row' (by rw [hr]; exact List.mem_cons_of_mem _ hrow')
      simp [facRow, Mult.BandFactor.subRowZ, htl, this]
    · exact hnx

/-- The window states of the factorization of a banded numerator matrix are the
windows of its integer stage matrices. -/
theorem facState_window (P K B : ℕ) (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ)
    (hA : NLogN.SchurDominance.BandFrom B (Mult.BandFactor.gvM P AZ) 0) (n : ℕ) :
    ∀ m ≤ n, facState P K (Mult.BandFactor.windowZ B AZ) (Mult.BandFactor.inputsZ B AZ n) m=
      (List.range' m (B+1)).map (Mult.BandFactor.winRowZ B (Mult.BandFactor.stgZ P K AZ m) m) := by
  have hinj : Function.Injective (List.map (List.map (Mult.BandFactor.gv P))) :=
    List.map_injective_iff.mpr (List.map_injective_iff.mpr (Mult.BandFactor.gv_injective P))
  have hRHS : ∀ m, ((List.range' m (B+1)).map
      (Mult.BandFactor.winRowZ B (Mult.BandFactor.stgZ P K AZ m) m)).map (List.map (Mult.BandFactor.gv P))=
      NLogN.SchurDominance.window B (NLogN.SchurDominance.stg (Mult.Sizes.rdP P) (Mult.BandFactor.mRule P K)
        (Mult.BandFactor.gvM P AZ) 0 m) m := by
    intro m
    simp only [NLogN.SchurDominance.window, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, Mult.BandFactor.winRowZ_map, Mult.BandFactor.stgZ_map P K hP]
  intro m
  induction m with
  | zero =>
    intro _
    rfl
  | succ m ih =>
    intro hm
    apply hinj
    rw [hRHS]
    simp only [facState]
    rw [Mult.BandFactor.stepRowsZ_map P K hP, ih (by omega), hRHS]
    have hin : (Mult.BandFactor.inputsZ B AZ n).getD m []=
        Mult.BandFactor.winRowZ B AZ (m+1) (m+B+1) := by
      rw [List.getD_eq_getElem _ _ (by simp [Mult.BandFactor.inputsZ]; omega)]
      simp [Mult.BandFactor.inputsZ]
    rw [hin, Mult.BandFactor.winRowZ_map]
    have hfar : NLogN.SchurDominance.winRow B (Mult.BandFactor.gvM P AZ) (m+1) (m+B+1)=
        NLogN.SchurDominance.winRow B (NLogN.SchurDominance.stg (Mult.Sizes.rdP P) (Mult.BandFactor.mRule P K)
          (Mult.BandFactor.gvM P AZ) 0 m) (m+1) (m+B+1) :=
      List.map_congr_left fun j _ => (NLogN.SchurDominance.stg_far (Mult.Sizes.rdP P) _ B (Mult.Sizes.rdP_zero P)
        (Mult.BandFactor.machMul_zero P K) _ hA m _ j (by omega)).symm
    rw [hfar, NLogN.SchurDominance.stepRows_window (Mult.Sizes.rdP P) _ B (Mult.Sizes.rdP_zero P) (Mult.BandFactor.machMul_zero P K)
      _ m (NLogN.SchurDominance.bandFrom_stg (Mult.Sizes.rdP P) _ B (Mult.Sizes.rdP_zero P) (Mult.BandFactor.machMul_zero P K) _ hA m)]
    simp [NLogN.SchurDominance.stg]

/-- The numerator factorization run is read off the window states. -/
theorem factorRowsZ_facState (P K : ℕ) : ∀ (inputs rows : List (List ℤ)),
    Mult.BandFactor.factorRowsZ P K rows inputs =
      (List.range inputs.length).map fun j =>
        (Mult.BandFactor.lcolZ P K (facState P K rows inputs j), (facState P K rows inputs j).headD [])
  | [], _ => rfl
  | next :: inputs, rows => by
    rw [Mult.BandFactor.factorRowsZ, factorRowsZ_facState P K inputs, List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    have h : ∀ m, facState P K (Mult.BandFactor.stepRowsZ P K rows next) inputs m =
        facState P K rows (next :: inputs) (m + 1) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => simp only [facState, ih, List.getD_cons_succ]
    simp [Function.comp, h]

/-- The `B` non-pivot rows of a window step. -/
theorem band_facRows_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (r : ℤ) (tail0 : List ℤ) (rest : List (List ℤ)) (htl : tail0.length = 2 * B)
    (hrest : rest.length = B) (hrow : ∀ row ∈ rest, row.length = 2 * B + 1)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt)) (hft : ∀ a ∈ tail0, Fits w (⟨a, 0⟩ : GaussianInt))
    (hfh : ∀ row ∈ rest, Fits w (⟨row.headD 0, 0⟩ : GaussianInt) ∧
      Fits w (⟨facMul P r row, 0⟩ : GaussianInt))
    (D TB SR : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (rest.map colC).flatten)
    (htb : σ .tb = cstream A w (List.replicate B ⟨r, 0⟩) ++ TB)
    (hef : σ .ef = cstream A w (List.replicate B (colC tail0)).flatten) (hsr : σ .sr = SR)
    (hmsk : σ .msk = csyms A w 0)
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hxa : σ .xa = []) (hhc : σ .hc = []) (htL : σ .tL = []) (hms : (σ .ms).length = B)
    (hm2n : (σ .m2n).length = 2 * B) (hmwn : (σ .mwn).length = 2 * B * w) :
    RsbRuns body rg ι (bandFacRowsP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        []) .tb TB) .ef []) .dout
        (cstream A w ((rest.map fun row => (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D)) .sr
        ((cstream A w (rest.map fun row => colC (facRow P r tail0 row)).flatten).reverse ++ SR))
      (B * (bandFacRowCost w B + 6) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((rest.drop j).map colC).flatten)) .tb
        (cstream A w (List.replicate (B-j) ⟨r, 0⟩) ++ TB)) .ef
        (cstream A w (List.replicate (B-j) (colC tail0)).flatten)) .dout
        (cstream A w (((rest.take j).map fun row => (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D))
        .sr ((cstream A w ((rest.take j).map fun row => colC (facRow P r tail0 row)).flatten).reverse ++
          SR) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .ms).length, ∀ X Y, RsbRuns body rg ι (bandFacRowP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .ms X .tL Y) (rsbUpd2 (Ψ (j + 1)) .ms X .tL Y) (bandFacRowCost w B) := by
    intro j hj X Y
    rw [hms] at hj
    have hjr : j < rest.length := by omega
    set row := rest[j]'hjr with hrowdef
    have hrl := hrow row (List.getElem_mem hjr)
    obtain ⟨h, tl, hht⟩ : ∃ h tl, row = h :: tl := by
      cases hr : row with
      | nil => rw [hr] at hrl; simp at hrl
      | cons h tl => exact ⟨h, tl, rfl⟩
    have htll : tl.length = 2 * B := by rw [hht] at hrl; simp at hrl; omega
    have hfhj := hfh row (List.getElem_mem hjr)
    rw [hht] at hfhj
    have hready' : RsbReady (rsbUpd2 (Ψ j) .ms X .tL Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact ((((((hready.update .vk (fun c => by simp) _).update .tb (fun c => by simp) _).update
        .ef (fun c => by simp) _).update .dout (fun c => by simp) _).update .sr (fun c => by simp)
        _).update .ms (fun c => by simp) _).update .tL (fun c => by simp) _
    have hBj : B-j=(B-(j+1))+1 := by omega
    have hstep := band_facRow_runs (body := body) (ι := ι) (w := w) (B := B) hrg hdisj hι hT hQ hA
      (rsbUpd2 (Ψ j) .ms X .tL Y) hready' hw hp ⟨h, 0⟩ r (colC tl)
      ((rest.drop (j+1)).map colC).flatten (colC tail0)
      (List.replicate (B-(j+1)) (colC tail0)).flatten (by simp [colC, htll])
      (by simp [colC, htl]) hfhj.1 hfr (by rw [tdivN_real]; simpa [facMul, hht] using hfhj.2)
      (by intro a ha; simp only [colC, List.mem_map] at ha; obtain ⟨x, hx, rfl⟩ := ha
          exact ⟨hft x hx, rfl⟩)
      (cstream A w (((rest.take j).map fun row => (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D)
      (cstream A w (List.replicate (B-(j+1)) ⟨r, 0⟩) ++ TB)
      ((cstream A w ((rest.take j).map fun row => colC (facRow P r tail0 row)).flatten).reverse ++ SR)
      (by
        simp only [rsbUpd2, hΨ, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.tL),
          Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.ms)]
        rw [List.drop_eq_getElem_cons hjr, ← hrowdef, hht]
        simp [colC])
      (by simp [rsbUpd2, hΨ, hBj, List.replicate_succ])
      (by simp [rsbUpd2, hΨ, hBj, List.replicate_succ])
      (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ, hmsk]) (by simp [rsbUpd2, hΨ])
      (by simp [rsbUpd2, hΨ, hhv]) (by simp [rsbUpd2, hΨ, hya]) (by simp [rsbUpd2, hΨ, hxs])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, hac])
      (by simp [rsbUpd2, hΨ, hac2]) (by simp [rsbUpd2, hΨ, htC]) (by simp [rsbUpd2, hΨ, htA])
      (by simp [rsbUpd2, hΨ, htJ]) (by simp [rsbUpd2, hΨ, hb1]) (by simp [rsbUpd2, hΨ, hxa])
      (by simp [rsbUpd2, hΨ, hhc]) (by simp [rsbUpd2, hΨ, hm2n]) (by simp [rsbUpd2, hΨ, hmwn])
    refine hstep.congr ?_
    have htake : ∀ {β : Type} (F : List ℤ → β), (rest.map F).take (j+1)=(rest.map F).take j++[F row] := by
      intro β F
      rw [List.take_succ_eq_append_getElem (by simpa using hjr), List.getElem_map]
    have hmr := machine_row P (facMul P r row) (2 * B) tail0 tl htl htll
    rw [tdivN_real]
    have hfm : facMul P r row=(h*r).tdiv (2^P) := by simp [facMul, hht]
    rw [← hfm, hmr]
    have h0 : (0 : GaussianInt)=⟨0, 0⟩ := rfl
    funext x; cases x <;> simp [rsbUpd2, hΨ, htake, facRow, hht, colC, List.reverse_append, h0]
  have h := rsb_rep_runs hrg hdisj (ra := .ms) (rt := .tL) (by decide) (bandFacRowP rg hι hT hQ)
    (σ .ms) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext x; cases x <;> simp [rsbUpd2, hΨ, hvk, htb, hef, hdout, hsr, htL]
  · rw [hms]
    have hd : (rest.map colC).drop B=[] := List.drop_of_length_le (by simp [hrest])
    funext x; cases x <;> simp [rsbUpd2, hΨ, htL, hrest, List.take_of_length_le, hd]
  · rw [hms]

/-- `B` copies of register `a` onto `b`, one per symbol of `ms`. -/
theorem band_copyRep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {a b : RsbR}
    (ha : a ≠ .b1 ∧ a ≠ .tC ∧ a ≠ .ms ∧ a ≠ .tL) (hb : b ≠ .b1 ∧ b ≠ .tC ∧ b ≠ .ms ∧ b ≠ .tL)
    (hab : a ≠ b) {B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hb1 : σ .b1 = []) (htC : σ .tC = [])
    (htL : σ .tL = []) (hms : (σ .ms).length = B) :
    RsbRuns body rg ι (rsbRep (rg .ms) (rg .tL) (rsbCopyTo rg a b)) σ
      (Function.update σ b ((List.replicate B (σ a)).flatten ++ σ b))
      (B * (6 * (σ a).length + 6 + 6) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update σ b ((List.replicate j (σ a)).flatten ++ σ b) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .ms).length, ∀ X Y, RsbRuns body rg ι (rsbCopyTo rg a b)
      (rsbUpd2 (Ψ j) .ms X .tL Y) (rsbUpd2 (Ψ (j + 1)) .ms X .tL Y) (6 * (σ a).length + 6) := by
    intro j _ X Y
    have h := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj ⟨ha.1, ha.2.1⟩ ⟨hb.1, hb.2.1⟩ hab
      (rsbUpd2 (Ψ j) .ms X .tL Y)
      (by simp [rsbUpd2, hΨ, Function.update_of_ne hb.1.symm, hb1])
      (by simp [rsbUpd2, hΨ, Function.update_of_ne hb.2.1.symm, htC])
    have hA : rsbUpd2 (Ψ j) .ms X .tL Y a=σ a := by
      simp [rsbUpd2, hΨ, Function.update_of_ne hab, Function.update_of_ne ha.2.2.1,
        Function.update_of_ne ha.2.2.2]
    rw [hA] at h
    refine h.congr ?_
    funext x
    simp only [rsbUpd2, hΨ, Function.update_apply, List.replicate_succ, List.flatten_cons,
      List.append_assoc]
    split_ifs <;> simp_all
  have h := rsb_rep_runs hrg hdisj (ra := .ms) (rt := .tL) (by decide) (rsbCopyTo rg a b)
    (σ .ms) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext x
    simp only [rsbUpd2, hΨ, Function.update_apply, List.replicate_zero, List.flatten_nil,
      List.nil_append]
    split_ifs <;> simp_all
  · funext x
    simp only [rsbUpd2, hΨ, Function.update_apply, hms]
    split_ifs <;> simp_all
  · rw [hms]

lemma flatten_replicate_cstream {w : ℕ} (B : ℕ) (X : List GaussianInt) :
    (List.replicate B (cstream A w X)).flatten=cstream A w (List.replicate B X).flatten := by
  induction B with
  | zero => simp
  | succ B ih => simp [List.replicate_succ, ih]

lemma flatten_replicate_csyms {w : ℕ} (B : ℕ) (x : GaussianInt) :
    (List.replicate B (csyms A w x)).flatten=cstream A w (List.replicate B x) := by
  induction B with
  | zero => simp
  | succ B ih => simp [List.replicate_succ, ih]

/-- The cost of one window step. -/
def bandFacStepCost (w B K : ℕ) : ℕ :=
  100 * (B + 1) * (B + 1) * w + 200 + (K * (bandNewtonStepCost w + 6) + 4) +
    (B * (bandFacRowCost w B + 6) + 4)

/-- **One window step.** The pivot row `c :: tail0` goes to `hf`, its reciprocal
`r = newtonZ P c K` to `df`, the multipliers of the `B` rows (last on top) to
`dout`, and `vk` becomes the updated rows followed by the next input row of `src`. -/
theorem band_facStep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B K : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (c : ℤ) (tail0 next : List ℤ) (rest : List (List ℤ))
    (htl : tail0.length = 2 * B) (hnext : next.length = 2 * B + 1)
    (hrest : rest.length = B) (hrow : ∀ row ∈ rest, row.length = 2 * B + 1)
    (hfc : Fits w (⟨c, 0⟩ : GaussianInt))
    (hfit : ∀ n < K, Fits w (⟨Mult.BandFactor.newtonZ P c n, 0⟩ : GaussianInt) ∧
      Fits w (⟨(c*Mult.BandFactor.newtonZ P c n).tdiv (2^P), 0⟩ : GaussianInt))
    (hfr : Fits w (⟨Mult.BandFactor.newtonZ P c K, 0⟩ : GaussianInt))
    (hft : ∀ a ∈ tail0, Fits w (⟨a, 0⟩ : GaussianInt))
    (hfh : ∀ row ∈ rest, Fits w (⟨row.headD 0, 0⟩ : GaussianInt) ∧
      Fits w (⟨facMul P (Mult.BandFactor.newtonZ P c K) row, 0⟩ : GaussianInt))
    (SRC HF DF D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (colC (c :: tail0) ++ (rest.map colC).flatten))
    (hsrc : σ .src = cstream A w (colC next) ++ SRC)
    (hhf : σ .hf = HF) (hdf : σ .df = DF) (hdout : σ .dout = D)
    (hbx : σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P c 0, 0⟩) (hmsk : σ .msk = csyms A w 0)
    (hef : σ .ef = []) (htb : σ .tb = []) (hsr : σ .sr = []) (hbo : σ .bo = [])
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hac : σ .ac = []) (hac2 : σ .ac2 = []) (hnv : σ .nv = [])
    (hb1 : σ .b1 = []) (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = [])
    (htK : σ .tK = []) (htL : σ .tL = [])
    (hkn : (σ .kn).length = K) (hms : (σ .ms).length = B) (hm2n : (σ .m2n).length = 2 * B)
    (hmwn : (σ .mwn).length = 2 * B * w) (hsmwn : (σ .smwn).length = (2 * B + 1) * w) :
    RsbRuns body rg ι (bandFacStepP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((rest.map fun row =>
          colC (facRow P (Mult.BandFactor.newtonZ P c K) tail0 row)).flatten ++ colC next)))
        .src SRC) .hf (cstream A w (colC (c :: tail0)) ++ HF))
        .df (csyms A w ⟨Mult.BandFactor.newtonZ P c K, 0⟩ ++ DF))
        .dout (cstream A w ((rest.map fun row =>
          (⟨facMul P (Mult.BandFactor.newtonZ P c K) row, 0⟩ : GaussianInt)).reverse) ++ D))
      (bandFacStepCost w B K) := by
  have hwn := hready.wn
  set r := Mult.BandFactor.newtonZ P c K with hr
  set RS := cstream A w (rest.map colC).flatten with hRS
  have htl' : (colC tail0).length = 2 * B := by simp [colC, htl]
  -- pop the pivot
  have h₁ := band_pop_runs (body := body) (ι := ι) hrg hdisj σ ⟨c, 0⟩
    (cstream A w (colC tail0) ++ RS) (by rw [hvk]; simp [colC, hRS]) hhv hac2 htC hwn
  set σ₁ := Function.update (Function.update σ .vk (cstream A w (colC tail0) ++ RS)) .hv
    (csyms A w ⟨c, 0⟩)
  -- the pivot tail to `bo`
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .vk) (y := .ac2)
    (by decide) σ₁ (by simp [σ₁, htC]) (by simp [σ₁, hmwn, htl'])
  have hmw : (σ₁ .mwn).length=(colC tail0).length * w := by simp [σ₁, hmwn, htl']
  rw [hmw] at h₂
  simp only [σ₁, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.hv), Function.update_self,
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.hv),
    Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.vk), take_cstream _ _ le_rfl,
    drop_cstream, List.take_length, List.drop_length, Nat.sub_self, zero_mul, List.drop_zero,
    cstream_nil, List.nil_append, hac2, List.append_nil] at h₂
  have h₂' := h₂.congr_pre (ρ₀ := σ₁) rfl
  set σ₂ := Function.update (Function.update σ₁ .vk RS) .ac2 (cstream A w (colC tail0)).reverse
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .bo) (by decide) σ₂
  set σ₃ := Function.update (Function.update σ₂ .ac2 []) .bo ((σ₂ .ac2).reverse ++ σ₂ .bo)
  have hready₃ : RsbReady σ₃ w P := by
    simp only [σ₃, σ₂, σ₁]
    exact (((((hready.update .vk (fun c => by simp) _).update .hv (fun c => by simp) _).update
      .vk (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2 (fun c => by simp)
      _).update .bo (fun c => by simp) _
  -- Newton
  have h₄ := band_newton_runs (body := body) (ι := ι) (K := K) hrg hdisj hι hT hQ hA σ₃ hready₃ hw hp
    c hfc hfit (by simp [σ₃, σ₂, σ₁, hbx]) (by simp [σ₃, σ₂, σ₁]) (by simp [σ₃, σ₂, σ₁, hxa])
    (by simp [σ₃, σ₂, σ₁, hhc]) (by simp [σ₃, σ₂, σ₁, hya]) (by simp [σ₃, σ₂, σ₁, hxs])
    (by simp [σ₃, σ₂, σ₁, hpr]) (by simp [σ₃, σ₂, σ₁, hac]) (by simp [σ₃, σ₂, σ₁])
    (by simp [σ₃, σ₂, σ₁, hnv]) (by simp [σ₃, σ₂, σ₁, hb1]) (by simp [σ₃, σ₂, σ₁, htC])
    (by simp [σ₃, σ₂, σ₁, htA]) (by simp [σ₃, σ₂, σ₁, htK]) (by simp [σ₃, σ₂, σ₁, hkn])
  rw [← hr] at h₄
  set σ₄ := Function.update σ₃ .xa (csyms A w ⟨r, 0⟩)
  -- outputs
  have h₅ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .bo) (b := .hf)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₄ (by simp [σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₄, σ₃, σ₂, σ₁, htC])
  set σ₅ := Function.update σ₄ .hf (σ₄ .bo ++ σ₄ .hf)
  have h₆ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .hv) (b := .hf)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₅ (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₆ := Function.update σ₅ .hf (σ₅ .hv ++ σ₅ .hf)
  have h₇ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .df)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₆
    (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1]) (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₇ := Function.update σ₆ .df (σ₆ .xa ++ σ₆ .df)
  -- copies for the rows
  have h₈ := band_copyRep_runs (body := body) (ι := ι) hrg hdisj (a := .bo) (b := .ef)
    ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩
    (by decide) (B := B) σ₇ (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
  set σ₈ := Function.update σ₇ .ef ((List.replicate B (σ₇ .bo)).flatten ++ σ₇ .ef)
  have h₉ := band_copyRep_runs (body := body) (ι := ι) hrg hdisj (a := .xa) (b := .tb)
    ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩
    (by decide) (B := B) σ₈ (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
  set σ₉ := Function.update σ₈ .tb ((List.replicate B (σ₈ .xa)).flatten ++ σ₈ .tb)
  have h₁₀ := rsb_emptyR_runs (body := body) (ι := ι) hrg .hv σ₉
  have h₁₁ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xa (Function.update σ₉ .hv [])
  have h₁₂ := rsb_emptyR_runs (body := body) (ι := ι) hrg .bo
    (Function.update (Function.update σ₉ .hv []) .xa [])
  set σ₁₂ := Function.update (Function.update (Function.update σ₉ .hv []) .xa []) .bo []
  have hready₁₂ : RsbReady σ₁₂ w P := by
    simp only [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄]
    exact ((((((((hready₃.update .xa (fun c => by simp) _).update .hf (fun c => by simp) _).update
      .hf (fun c => by simp) _).update .df (fun c => by simp) _).update .ef (fun c => by simp)
      _).update .tb (fun c => by simp) _).update .hv (fun c => by simp) _).update .xa
      (fun c => by simp) _).update .bo (fun c => by simp) _
  -- the rows
  have h₁₃ := band_facRows_runs (body := body) (ι := ι) (w := w) (B := B) hrg hdisj hι hT hQ hA
    σ₁₂ hready₁₂ hw hp r tail0 rest htl hrest hrow hfr hft hfh D [] []
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hRS])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htb, flatten_replicate_csyms])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, hbo, flatten_replicate_cstream])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsr])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hmsk])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hdout])
    (by simp [σ₁₂]) (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hya])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hxs])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hpr])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hnv])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hac])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htA])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htJ])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1]) (by simp [σ₁₂])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hhc])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hm2n])
    (by simp [σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hmwn])
  set NR := cstream A w (rest.map fun row => colC (facRow P r tail0 row)).flatten
  set σ₁₃ := Function.update (Function.update (Function.update (Function.update (Function.update
    σ₁₂ .vk []) .tb []) .ef []) .dout (cstream A w ((rest.map fun row =>
      (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D)) .sr (NR.reverse ++ [])
  -- the next input row
  have hnl : (colC next).length = 2 * B + 1 := by simp [colC, hnext]
  have h₁₄ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .smwn) (t := .tC) (x := .src) (y := .sr)
    (by decide) σ₁₃ (by simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
    (by simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsmwn, hsrc, hnl])
  have hsw : (σ₁₃ .smwn).length=(colC next).length * w := by
    simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsmwn, hnl]
  have hsrc₁₃ : σ₁₃ .src=cstream A w (colC next) ++ SRC := by
    simp [σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsrc]
  rw [hsw, hsrc₁₃, take_cstream _ _ le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append] at h₁₄
  set σ₁₄ := Function.update (Function.update σ₁₃ .src SRC) .sr
    ((cstream A w (colC next)).reverse ++ σ₁₃ .sr)
  have h₁₅ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .sr) (b := .vk) (by decide) σ₁₄
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂' (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj h₆ (RsbRuns.seq hdisj h₇
    (RsbRuns.seq hdisj h₈ (RsbRuns.seq hdisj h₉ (RsbRuns.seq hdisj h₁₀ (RsbRuns.seq hdisj h₁₁
    (RsbRuns.seq hdisj h₁₂ (RsbRuns.seq hdisj h₁₃ (RsbRuns.seq hdisj h₁₄
    h₁₅)))))))))))))).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₁₄, σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, htb, hsr,
      hbo, hhv, hxa, hac2, hhf, hdf, NR, colC, List.reverse_append]
  · simp [σ₁₄, σ₁₃, σ₁₂, σ₉, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hef, htb, hbo, 
      hhf, hdf, bandFacStepCost, csyms, colC, htl, NR, hRS]
    have hsum : (List.map (List.length ∘ fun row => List.map (fun x => (⟨x, 0⟩ : GaussianInt))
        (facRow P r tail0 row)) rest).sum=B*(2*B+1) := by
      rw [List.map_congr_left (g := fun _ => 2*B+1) (fun row hr => by
        simp [facRow, Mult.BandFactor.subRowZ, htl, hrow row hr]), List.map_const',
        List.sum_replicate, hrest, smul_eq_mul]
    rw [hsum, hnext]
    nlinarith

/-- The record-width conditions of one window step. -/
def FacFits (w P K : ℕ) : List (List ℤ) → Prop
  | (c :: tail0) :: rest => Fits w (⟨c, 0⟩ : GaussianInt) ∧
      (∀ n < K, Fits w (⟨Mult.BandFactor.newtonZ P c n, 0⟩ : GaussianInt) ∧
        Fits w (⟨(c*Mult.BandFactor.newtonZ P c n).tdiv (2^P), 0⟩ : GaussianInt)) ∧
      Fits w (⟨Mult.BandFactor.newtonZ P c K, 0⟩ : GaussianInt) ∧
      (∀ a ∈ tail0, Fits w (⟨a, 0⟩ : GaussianInt)) ∧
      ∀ row ∈ rest, Fits w (⟨row.headD 0, 0⟩ : GaussianInt) ∧
        Fits w (⟨facMul P (Mult.BandFactor.newtonZ P c K) row, 0⟩ : GaussianInt)
  | _ => False

/-- The pivot of a window. -/
def facPiv (rows : List (List ℤ)) : ℤ := (rows.headD []).headD 0

/-- **The window factorization.** After `s` steps: `vk` holds the final window,
`hf` the pivot rows (last on top), `df` the Newton reciprocals of the pivots
(last on top), and `dout` all multipliers in reverse order. -/
theorem band_facLoop_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B K s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (rows inputs : List (List ℤ)) (hrows : rows.length = B + 1)
    (hrl : ∀ row ∈ rows, row.length = 2 * B + 1) (hin : ∀ row ∈ inputs, row.length = 2 * B + 1)
    (hs : inputs.length = s) (hfit : ∀ m < s, FacFits w P K (facState P K rows inputs m))
    (hr0 : ∀ m < s, σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs m)) 0, 0⟩)
    (SRC HF DF D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (rows.map colC).flatten)
    (hsrc : σ .src = cstream A w (inputs.map colC).flatten ++ SRC)
    (hhf : σ .hf = HF) (hdf : σ .df = DF) (hdout : σ .dout = D) (hmsk : σ .msk = csyms A w 0)
    (hef : σ .ef = []) (htb : σ .tb = []) (hsr : σ .sr = []) (hbo : σ .bo = [])
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hac : σ .ac = []) (hac2 : σ .ac2 = []) (hnv : σ .nv = [])
    (hb1 : σ .b1 = []) (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = [])
    (htK : σ .tK = []) (htL : σ .tL = []) (hsel : σ .sel = []) (hsn : (σ .sn).length = s)
    (hkn : (σ .kn).length = K) (hms : (σ .ms).length = B) (hm2n : (σ .m2n).length = 2 * B)
    (hmwn : (σ .mwn).length = 2 * B * w) (hsmwn : (σ .smwn).length = (2 * B + 1) * w) :
    RsbRuns body rg ι (bandFacLoopP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((facState P K rows inputs s).map colC).flatten)) .src SRC)
        .hf (cstream A w ((List.range s).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten ++ HF))
        .df (cstream A w ((List.range s).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ++ DF))
        .dout (cstream A w (((List.range s).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse) ++ D))
      (s * (bandFacStepCost w B K + 6) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun m =>
      Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((facState P K rows inputs m).map colC).flatten))
        .src (cstream A w ((inputs.drop m).map colC).flatten ++ SRC))
        .hf (cstream A w ((List.range m).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten ++ HF))
        .df (cstream A w ((List.range m).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ++ DF))
        .dout (cstream A w (((List.range m).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse) ++ D) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .sn).length, ∀ X Y, RsbRuns body rg ι (bandFacStepP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .sn X .sel Y) (rsbUpd2 (Ψ (j + 1)) .sn X .sel Y) (bandFacStepCost w B K) := by
    intro j hj X Y
    rw [hsn] at hj
    obtain ⟨hlen, hrlen⟩ := facState_shape P K B rows inputs hrows hrl hin j (by omega)
    obtain ⟨row0, rest, hr⟩ : ∃ row0 rest, facState P K rows inputs j=row0 :: rest := by
      cases h : facState P K rows inputs j with
      | nil => rw [h] at hlen; simp at hlen
      | cons a l => exact ⟨a, l, rfl⟩
    have hr0l := hrlen row0 (by rw [hr]; simp)
    obtain ⟨c, tail0, hc⟩ : ∃ c tail0, row0=c :: tail0 := by
      cases row0 with
      | nil => simp at hr0l
      | cons a l => exact ⟨a, l, rfl⟩
    subst hc
    have hfj := hfit j hj
    rw [hr] at hfj
    obtain ⟨hfc, hfn, hfr, hft, hfh⟩ := hfj
    have htl : tail0.length=2*B := by simp at hr0l; omega
    have hrest : rest.length=B := by rw [hr] at hlen; simp at hlen; omega
    have hjin : j < inputs.length := by omega
    set next := inputs[j]'hjin with hnextdef
    have hnl : next.length=2*B+1 := hin next (List.getElem_mem _)
    have hready' : RsbReady (rsbUpd2 (Ψ j) .sn X .sel Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact ((((((hready.update .vk (fun c => by simp) _).update .src (fun c => by simp) _).update
        .hf (fun c => by simp) _).update .df (fun c => by simp) _).update .dout (fun c => by simp)
        _).update .sn (fun c => by simp) _).update .sel (fun c => by simp) _
    have hpiv : facPiv (facState P K rows inputs j)=c := by simp [facPiv, hr]
    have hstep := band_facStep_runs (body := body) (ι := ι) (w := w) (B := B) (K := K) hrg hdisj hι
      hT hQ hA (rsbUpd2 (Ψ j) .sn X .sel Y) hready' hw hp c tail0 next rest htl hnl hrest
      (fun row hrow => hrlen row (by rw [hr]; exact List.mem_cons_of_mem _ hrow))
      hfc hfn hfr hft hfh (cstream A w ((inputs.drop (j+1)).map colC).flatten ++ SRC)
      (cstream A w ((List.range j).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten ++ HF)
      (cstream A w ((List.range j).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ++ DF)
      (cstream A w (((List.range j).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse) ++ D)
      (by simp [rsbUpd2, hΨ, hr, colC])
      (by
        have hdj : (inputs.map colC).drop j=colC next :: (inputs.map colC).drop (j+1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hjin), List.getElem_map]
        simp [rsbUpd2, hΨ, hdj])
      (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ])
      (by have := hr0 j hj; rw [hpiv] at this; simp [rsbUpd2, hΨ, this]) (by simp [rsbUpd2, hΨ, hmsk])
      (by simp [rsbUpd2, hΨ, hef]) (by simp [rsbUpd2, hΨ, htb]) (by simp [rsbUpd2, hΨ, hsr])
      (by simp [rsbUpd2, hΨ, hbo]) (by simp [rsbUpd2, hΨ, hhv]) (by simp [rsbUpd2, hΨ, hxa])
      (by simp [rsbUpd2, hΨ, hhc]) (by simp [rsbUpd2, hΨ, hya]) (by simp [rsbUpd2, hΨ, hxs])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hac]) (by simp [rsbUpd2, hΨ, hac2])
      (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, hb1]) (by simp [rsbUpd2, hΨ, htC])
      (by simp [rsbUpd2, hΨ, htA]) (by simp [rsbUpd2, hΨ, htJ]) (by simp [rsbUpd2, hΨ, htK])
      (by simp [rsbUpd2, hΨ, htL]) (by simp [rsbUpd2, hΨ, hkn]) (by simp [rsbUpd2, hΨ, hms])
      (by simp [rsbUpd2, hΨ, hm2n]) (by simp [rsbUpd2, hΨ, hmwn]) (by simp [rsbUpd2, hΨ, hsmwn])
    refine hstep.congr ?_
    have hnext' : inputs.getD j []=next := by rw [List.getD_eq_getElem _ _ hjin]
    have hst : facState P K rows inputs (j+1)=
        rest.map (fun row => facRow P (Mult.BandFactor.newtonZ P c K) tail0 row)++[next] := by
      simp only [facState, hr, hnext', stepRowsZ_cons]
    have hlc : Mult.BandFactor.lcolZ P K (facState P K rows inputs j)=
        rest.map (fun row => facMul P (Mult.BandFactor.newtonZ P c K) row) := by
      rw [hr, lcolZ_cons]
    funext x; cases x <;> simp [rsbUpd2, hΨ, hst, List.range_succ, hr, colC,
      List.reverse_append, facPiv, lcolZ_cons, Function.comp_def]
  have h := rsb_rep_runs hrg hdisj (ra := .sn) (rt := .sel) (by decide) (bandFacStepP rg hι hT hQ)
    (σ .sn) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext x; cases x <;> simp [rsbUpd2, hΨ, hvk, hsrc, hhf, hdf, hdout, hsel, facState]
  · rw [hsn]
    have hd : (inputs.map colC).drop s=[] := List.drop_of_length_le (by simp; omega)
    funext x; cases x <;> simp [rsbUpd2, hΨ, hsel, hd]
  · rw [hsn]

/-- One block of a transpose step. -/
theorem band_tBlk_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w B : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (blk : List GaussianInt) (hblk : blk.length = B + 1)
    (VK YA NV : List (Fin (A + 4))) (hvk : σ .vk = cstream A w blk ++ VK) (hya : σ .ya = YA)
    (hnv : σ .nv = NV) (hmsk : σ .msk = csyms A w 0) (htC : σ .tC = [])
    (hwn : (σ (.cm .wn)).length = w) (hm2wn : (σ .m2wn).length = B * w) :
    RsbRuns body rg ι (bandTBlkP rg) σ
      (Function.update (Function.update (Function.update σ .vk VK) .ya
        ((csyms A w (blk.headD 0)).reverse ++ YA)) .nv
        ((cstream A w (blk.tail ++ [0])).reverse ++ NV))
      (4 * w + 4 + (4 * (B * w) + 4) + (4 * w + 4)) := by
  obtain ⟨b, bs, rfl⟩ : ∃ b bs, blk = b :: bs := by
    cases blk with
    | nil => simp at hblk
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hbs : bs.length = B := by simpa using hblk
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := .vk) (y := .ya)
    (by decide) σ htC (by rw [hwn, hvk]; simp [csyms])
  rw [hwn, hvk, cstream_cons, List.append_assoc, take_csyms_append, drop_csyms_append, hya] at h₁
  set σ₁ := Function.update (Function.update σ .vk (cstream A w bs ++ VK)) .ya
    ((csyms A w b).reverse ++ YA)
  have h₂ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .m2wn) (t := .tC) (x := .vk) (y := .nv)
    (by decide) σ₁ (by simp [σ₁, htC]) (by simp [σ₁, hm2wn, hbs])
  have hl : (σ₁ .m2wn).length = bs.length * w := by simp [σ₁, hm2wn, hbs]
  rw [hl] at h₂
  simp only [σ₁, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.ya), Function.update_self,
    Function.update_of_ne (by decide : RsbR.nv ≠ RsbR.ya),
    Function.update_of_ne (by decide : RsbR.nv ≠ RsbR.vk), take_cstream _ _ le_rfl, drop_cstream,
    List.take_length, List.drop_length, Nat.sub_self, zero_mul, List.drop_zero, hnv] at h₂
  have h₂' := h₂.congr_pre (ρ₀ := σ₁) rfl
  set σ₂ := Function.update (Function.update σ₁ .vk VK) .nv ((cstream A w bs).reverse ++ NV)
  have h₃ := rsb_copyR_runs (body := body) (ι := ι) hrg (a := .msk) (b := .nv) (t := .tC)
    (by decide) (by decide) (by decide) σ₂ (by simp [σ₂, σ₁, htC])
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂' h₃)).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₂, σ₁, hmsk, List.reverse_append]
  · simp [σ₂, σ₁, hmsk, csyms, hbs]; omega

/-- The cost of one transpose step with `k+1` blocks. -/
def bandTStepCost (w k : ℕ) : ℕ := 40 * (k + 2) * (k + 2) * w + 40 * k + 100

/-- **One transpose step.** With the window `W` of `k+1` blocks of `k+1` entries on
`vk` and the next pivot row on `src`, `ef` gains the column `(tStep W u).1` and
`vk` becomes `(tStep W u).2`, for `u` the entries `1, …, k+1` of the row. -/
theorem band_tStep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w k : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (row : List ℤ) (hrow : row.length = 2 * (k + 1) + 1)
    (W : List (List ℤ)) (hW : W.length = k + 1) (hWl : ∀ blk ∈ W, blk.length = k + 1)
    (SRC EF : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w (colC row) ++ SRC) (hvk : σ .vk = cstream A w (W.map colC).flatten)
    (hef : σ .ef = EF) (hmsk : σ .msk = csyms A w 0) (hpr : σ .pr = []) (hxs : σ .xs = [])
    (hya : σ .ya = []) (hnv : σ .nv = []) (htC : σ .tC = []) (htL : σ .tL = [])
    (hwn : (σ (.cm .wn)).length = w) (hmwn : (σ .mwn).length = (k + 1) * w)
    (hm2wn : (σ .m2wn).length = k * w) (hms : (σ .ms).length = k) :
    RsbRuns body rg ι (bandTStepP rg) σ
      (Function.update (Function.update (Function.update σ .src SRC) .vk
        (cstream A w ((Mult.BandFactor.tStep W ((row.drop 1).take (k + 1))).2.map colC).flatten))
        .ef (cstream A w (colC (Mult.BandFactor.tStep W ((row.drop 1).take (k + 1))).1) ++ EF))
      (bandTStepCost w k) := by
  obtain ⟨c, rr, rfl⟩ : ∃ c rr, row = c :: rr := by
    cases row with
    | nil => simp at hrow
    | cons c rr => exact ⟨c, rr, rfl⟩
  have hrr : rr.length = 2 * (k + 1) := by simpa using hrow
  set u := rr.take (k + 1) with hu
  set v := rr.drop (k + 1) with hv
  have hul : u.length = k + 1 := by simp [hu, hrr]
  have hvl : v.length = k + 1 := by simp [hv, hrr]; omega
  have hsplit : colC (c :: rr) = ⟨c, 0⟩ :: (colC u ++ colC v) := by
    simp only [colC, List.map_cons, ← List.map_append, hu, hv, List.take_append_drop]
  have hdrop : (c :: rr).drop 1 = rr := rfl
  rw [hdrop]
  -- drop the pivot
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := .src) (y := .pr)
    (by decide) σ htC (by rw [hwn, hsrc, hsplit]; simp [csyms])
  rw [hwn, hsrc, hsplit, cstream_cons, List.append_assoc, take_csyms_append, drop_csyms_append,
    hpr, List.append_nil] at h₁
  set σ₁ := Function.update (Function.update σ .src (cstream A w (colC u ++ colC v) ++ SRC)) .pr
    (csyms A w ⟨c, 0⟩).reverse
  have h₂ := rsb_emptyR_runs (body := body) (ι := ι) hrg .pr σ₁
  set σ₂ := Function.update σ₁ .pr []
  -- the new first block
  have h₃ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .src) (y := .xs)
    (by decide) σ₂ (by simp [σ₂, σ₁, htC]) (by
      simp only [σ₂, σ₁, Function.update_of_ne (by decide : RsbR.mwn ≠ RsbR.pr),
        Function.update_of_ne (by decide : RsbR.mwn ≠ RsbR.src), Function.update_of_ne
        (by decide : RsbR.src ≠ RsbR.pr), Function.update_self, hmwn, cstream_append,
        List.length_append, length_cstream, colC, List.length_map, hul, hvl]
      omega)
  have hl₃ : (σ₂ .mwn).length = (colC u).length * w := by simp [σ₂, σ₁, hmwn, colC, hul]
  have hs₂ : σ₂ .src = cstream A w (colC u) ++ (cstream A w (colC v) ++ SRC) := by
    simp [σ₂, σ₁]
  rw [hl₃, hs₂, take_cstream _ _ le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append] at h₃
  set σ₃ := Function.update (Function.update σ₂ .src (cstream A w (colC v) ++ SRC)) .xs
    ((cstream A w (colC u)).reverse ++ σ₂ .xs)
  -- drop the far half
  have hs₃' : σ₃ .src = cstream A w (colC v) ++ SRC := by simp [σ₃]
  have h₄ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .mwn) (t := .tC) (x := .src) (y := .pr)
    (by decide) σ₃ (by simp [σ₃, σ₂, σ₁, htC]) (by
      rw [hs₃']; simp only [σ₃, σ₂, σ₁, Function.update_of_ne (by decide : RsbR.mwn ≠ RsbR.xs),
        Function.update_of_ne (by decide : RsbR.mwn ≠ RsbR.pr),
        Function.update_of_ne (by decide : RsbR.mwn ≠ RsbR.src), hmwn, List.length_append,
        length_cstream, colC, List.length_map, hvl]
      omega)
  have hl₄ : (σ₃ .mwn).length = (colC v).length * w := by simp [σ₃, σ₂, σ₁, hmwn, colC, hvl]
  have hs₃ : σ₃ .src = cstream A w (colC v) ++ SRC := by simp [σ₃]
  rw [hl₄, hs₃, take_cstream _ _ le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append] at h₄
  set σ₄ := Function.update (Function.update σ₃ .src SRC) .pr
    ((cstream A w (colC v)).reverse ++ σ₃ .pr)
  have h₅ := rsb_emptyR_runs (body := body) (ι := ι) hrg .pr σ₄
  set σ₅ := Function.update σ₄ .pr []
  -- the first `k` blocks
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update σ₅ .vk
        (cstream A w ((W.drop j).map colC).flatten)) .ya
        (cstream A w ((W.take j).map fun blk => (⟨blk.headD 0, 0⟩ : GaussianInt))).reverse) .nv
        (cstream A w ((W.take j).map fun blk => colC (blk.tail ++ [0])).flatten).reverse := ⟨_, rfl⟩
  have hbody : ∀ j < (σ₅ .ms).length, ∀ X Y, RsbRuns body rg ι (bandTBlkP rg)
      (rsbUpd2 (Ψ j) .ms X .tL Y) (rsbUpd2 (Ψ (j + 1)) .ms X .tL Y)
      (4 * w + 4 + (4 * (k * w) + 4) + (4 * w + 4)) := by
    intro j hj X Y
    have hj' : j < k := by simpa [σ₅, σ₄, σ₃, σ₂, σ₁, hms] using hj
    have hjW : j < W.length := by omega
    have hbl := hWl (W[j]'hjW) (List.getElem_mem _)
    have h := band_tBlk_runs (body := body) (ι := ι) (w := w) (B := k) hrg hdisj
      (rsbUpd2 (Ψ j) .ms X .tL Y) (colC (W[j]'hjW)) (by simp [colC, hbl])
      (cstream A w ((W.drop (j+1)).map colC).flatten)
      (cstream A w ((W.take j).map fun blk => (⟨blk.headD 0, 0⟩ : GaussianInt))).reverse
      (cstream A w ((W.take j).map fun blk => colC (blk.tail ++ [0])).flatten).reverse
      (by
        have hdj : (W.map colC).drop j=colC (W[j]'hjW) :: (W.map colC).drop (j+1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hjW), List.getElem_map]
        simp [rsbUpd2, hΨ, hdj])
      (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ])
      (by simp [rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hmsk])
      (by simp [rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
      (by simp [rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hwn])
      (by simp [rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hm2wn])
    refine h.congr ?_
    have htake : ∀ {β : Type} (F : List ℤ → β), (W.map F).take (j+1) = (W.map F).take j ++ [F (W[j]'hjW)] := by
      intro β F
      rw [List.take_succ_eq_append_getElem (by simpa using hjW), List.getElem_map]
    have hh : (colC (W[j]'hjW)).headD 0 = ⟨(W[j]'hjW).headD 0, 0⟩ := by
      cases W[j]'hjW <;> rfl
    have ht : (colC (W[j]'hjW)).tail ++ [0] = colC ((W[j]'hjW).tail ++ [0]) := by
      cases W[j]'hjW <;> simp [colC] <;> rfl
    rw [hh, ht]
    funext x; cases x <;> simp [rsbUpd2, hΨ, htake, List.reverse_append]
  have h₆ := rsb_rep_runs hrg hdisj (ra := .ms) (rt := .tL) (by decide) (bandTBlkP rg) (σ₅ .ms) Ψ _ hbody
  have h₆' := h₆.congr_pre (ρ₀ := σ₅) (by
    funext x; cases x <;> simp [rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hvk, hya, hnv, htL])
  have hk5 : (σ₅ .ms).length = k := by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hms]
  rw [hk5] at h₆'
  set σ₆ := rsbUpd2 (Ψ k) .ms (σ₅ .ms) .tL []
  -- the last block
  have hkW : k < W.length := by omega
  set last := W[k]'hkW with hlast
  have hll : last.length = k + 1 := hWl last (List.getElem_mem _)
  obtain ⟨lh, lt, hlht⟩ : ∃ lh lt, last = lh :: lt := by
    cases hc : last with
    | nil => rw [hc] at hll; simp at hll
    | cons a l => exact ⟨a, l, rfl⟩
  have hltl : lt.length = k := by rw [hlht] at hll; simpa using hll
  have hWd : (W.map colC).drop k = [colC last] := by
    rw [List.drop_eq_getElem_cons (by simpa using hkW), List.getElem_map,
      List.drop_of_length_le (by simp; omega)]
  have hvk6 : σ₆ .vk = csyms A w ⟨lh, 0⟩ ++ cstream A w (colC lt) := by
    simp [σ₆, rsbUpd2, hΨ, hWd, hlht, colC]
  have h₇ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .cm .wn) (t := .tC) (x := .vk) (y := .ya)
    (by decide) σ₆ (by simp [σ₆, rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
    (by rw [hvk6]; simp [σ₆, rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hwn, csyms])
  have hw6 : (σ₆ (.cm .wn)).length = w := by simp [σ₆, rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hwn]
  rw [hw6, hvk6, take_csyms_append, drop_csyms_append] at h₇
  set σ₇ := Function.update (Function.update σ₆ .vk (cstream A w (colC lt))) .ya
    ((csyms A w ⟨lh, 0⟩).reverse ++ σ₆ .ya)
  have h₈ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .m2wn) (t := .tC) (x := .vk) (y := .pr)
    (by decide) σ₇ (by simp [σ₇, σ₆, rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
    (by simp [σ₇, σ₆, rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hm2wn, colC, hltl])
  have hl8 : (σ₇ .m2wn).length = (colC lt).length * w := by
    simp [σ₇, σ₆, rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hm2wn, colC, hltl]
  have hv7 : σ₇ .vk = cstream A w (colC lt) ++ [] := by simp [σ₇]
  rw [hl8, hv7, take_cstream _ _ le_rfl, drop_cstream, List.take_length, List.drop_length,
    Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append] at h₈
  set σ₈ := Function.update (Function.update σ₇ .vk []) .pr ((cstream A w (colC lt)).reverse ++ σ₇ .pr)
  have h₉ := rsb_emptyR_runs (body := body) (ι := ι) hrg .pr σ₈
  set σ₉ := Function.update σ₈ .pr []
  have h₁₀ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ya) (b := .ef) (by decide) σ₉
  set σ₁₀ := Function.update (Function.update σ₉ .ya []) .ef ((σ₉ .ya).reverse ++ σ₉ .ef)
  have h₁₁ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .nv) (b := .vk) (by decide) σ₁₀
  set σ₁₁ := Function.update (Function.update σ₁₀ .nv []) .vk ((σ₁₀ .nv).reverse ++ σ₁₀ .vk)
  have h₁₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .xs) (b := .vk) (by decide) σ₁₁
  have hWsplit : W = W.take k ++ [last] := by
    conv_lhs => rw [← List.take_append_drop k W]
    congr 1
    rw [List.drop_eq_getElem_cons hkW, List.drop_of_length_le (by omega)]
  have hdl : W.dropLast = W.take k := by
    rw [List.dropLast_eq_take, hW]; rfl
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj h₆' (RsbRuns.seq hdisj h₇
    (RsbRuns.seq hdisj h₈ (RsbRuns.seq hdisj h₉ (RsbRuns.seq hdisj h₁₀ (RsbRuns.seq hdisj h₁₁
    h₁₂))))))))))).congr ?_).mono ?_
  · have hheads : W.map (fun blk => (⟨blk.headD 0, 0⟩ : GaussianInt)) =
        (W.take k).map (fun blk => (⟨blk.headD 0, 0⟩ : GaussianInt)) ++ [⟨lh, 0⟩] := by
      conv_lhs => rw [hWsplit]
      simp [hlht]
    have hct : ∀ blk : List ℤ, (blk.map (fun x => (⟨x, 0⟩ : GaussianInt))).tail ++ [⟨0, 0⟩] =
        (blk.tail ++ [0]).map (fun x => (⟨x, 0⟩ : GaussianInt)) := by
      intro blk; cases blk <;> simp
    have hmapk : ∀ {β : Type} (g : List ℤ → β), (W.map g).take k ++ [g last] = W.map g := by
      intro β g
      conv_rhs => rw [hWsplit]
      simp
    funext x; cases x <;> simp [σ₁₁, σ₁₀, σ₉, σ₈, σ₇, σ₆, rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hef,
      hxs, hpr, hya, hnv, Mult.BandFactor.tStep, hdl, colC, List.reverse_append, htL, hu,
      Function.comp_def]
    all_goals
      conv_rhs => rw [← hmapk (fun blk : List ℤ => (⟨blk.head?.getD 0, 0⟩ : GaussianInt))]
      simp [hlht]
  · simp [σ₁₁, σ₁₀, σ₉, σ₈, σ₇, σ₆, rsbUpd2, hΨ, σ₅, σ₄, σ₃, σ₂, σ₁, hef, hxs, 
      colC, hul, hvl, hltl, bandTStepCost, csyms, hW]
    have hsum : (List.take k (List.map (List.length ∘ fun blk =>
        (List.map (fun x => (⟨x, 0⟩ : GaussianInt)) blk).tail ++ [(⟨0, 0⟩ : GaussianInt)]) W)).sum =
        k * (k + 1) := by
      rw [List.map_congr_left (g := fun _ => k+1) (fun blk hb => by simp [hWl blk hb]),
        List.map_const', List.take_replicate, List.sum_replicate, hW, smul_eq_mul,
        Nat.min_eq_left (by omega)]
    rw [hsum]
    ring_nf; omega

/-- **The transpose.** With the pivot rows `Ur` (row `0` on top) on `src` and the
zero window on `vk`, `ef` gains the backward-pass columns `ucolZ`, the last on top. -/
theorem band_tLoop_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w k s : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (Ur : List (List ℤ)) (hUr : Ur.length = s)
    (hrow : ∀ row ∈ Ur, row.length = 2 * (k + 1) + 1) (SRC EF : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w (Ur.map colC).flatten ++ SRC)
    (hvk : σ .vk = cstream A w ((Mult.BandFactor.tWin (k + 1) Ur 0).map colC).flatten)
    (hef : σ .ef = EF) (hmsk : σ .msk = csyms A w 0) (hpr : σ .pr = []) (hxs : σ .xs = [])
    (hya : σ .ya = []) (hnv : σ .nv = []) (htC : σ .tC = []) (htL : σ .tL = [])
    (hsel : σ .sel = []) (hsn : (σ .sn).length = s)
    (hwn : (σ (.cm .wn)).length = w) (hmwn : (σ .mwn).length = (k + 1) * w)
    (hm2wn : (σ .m2wn).length = k * w) (hms : (σ .ms).length = k) :
    RsbRuns body rg ι (bandTLoopP rg) σ
      (Function.update (Function.update (Function.update σ .src SRC) .vk
        (cstream A w ((Mult.BandFactor.tWin (k + 1) Ur s).map colC).flatten))
        .ef (cstream A w ((List.range s).reverse.map fun m =>
          colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten ++ EF))
      (s * (bandTStepCost w k + 6) + 4) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun m =>
      Function.update (Function.update (Function.update σ .src
        (cstream A w ((Ur.drop m).map colC).flatten ++ SRC)) .vk
        (cstream A w ((Mult.BandFactor.tWin (k + 1) Ur m).map colC).flatten))
        .ef (cstream A w ((List.range m).reverse.map fun m =>
          colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten ++ EF) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .sn).length, ∀ X Y, RsbRuns body rg ι (bandTStepP rg)
      (rsbUpd2 (Ψ j) .sn X .sel Y) (rsbUpd2 (Ψ (j + 1)) .sn X .sel Y) (bandTStepCost w k) := by
    intro j hj X Y
    rw [hsn] at hj
    have hjU : j < Ur.length := by omega
    set row := Ur[j]'hjU with hrowdef
    have hrl : row.length = 2 * (k + 1) + 1 := hrow row (List.getElem_mem _)
    have hWl : ∀ blk ∈ Mult.BandFactor.tWin (k + 1) Ur j, blk.length = k + 1 := by
      intro blk hb
      simp only [Mult.BandFactor.tWin, List.mem_map] at hb
      obtain ⟨d, -, rfl⟩ := hb
      simp
    have h := band_tStep_runs (body := body) (ι := ι) (w := w) (k := k) hrg hdisj
      (rsbUpd2 (Ψ j) .sn X .sel Y) row hrl (Mult.BandFactor.tWin (k + 1) Ur j)
      (by simp [Mult.BandFactor.tWin]) hWl (cstream A w ((Ur.drop (j+1)).map colC).flatten ++ SRC)
      (cstream A w ((List.range j).reverse.map fun m =>
          colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten ++ EF)
      (by
        have hdj : (Ur.map colC).drop j=colC row :: (Ur.map colC).drop (j+1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hjU), List.getElem_map]
        simp [rsbUpd2, hΨ, hdj])
      (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ, hmsk])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hxs]) (by simp [rsbUpd2, hΨ, hya])
      (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, htC]) (by simp [rsbUpd2, hΨ, htL])
      (by simp [rsbUpd2, hΨ, hwn]) (by simp [rsbUpd2, hΨ, hmwn]) (by simp [rsbUpd2, hΨ, hm2wn])
      (by simp [rsbUpd2, hΨ, hms])
    refine h.congr ?_
    have hgd : Ur.getD j [] = row := by rw [List.getD_eq_getElem _ _ hjU]
    have hstep := Mult.BandFactor.tWin_step (k + 1) Ur (by omega) j (by rw [hgd, hrl]; omega)
    rw [hgd] at hstep
    have hcol : (Mult.BandFactor.tStep (Mult.BandFactor.tWin (k + 1) Ur j)
        ((row.drop 1).take (k + 1))).1 = Mult.BandFactor.ucolZ (k + 1) Ur j := by
      simp only [Mult.BandFactor.tStep, Mult.BandFactor.tWin_heads]
    rw [hstep, hcol]
    funext x; cases x <;> simp [rsbUpd2, hΨ, List.range_succ]
  have h := rsb_rep_runs hrg hdisj (ra := .sn) (rt := .sel) (by decide) (bandTStepP rg)
    (σ .sn) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext x; cases x <;> simp [rsbUpd2, hΨ, hsrc, hvk, hef, hsel]
  · rw [hsn]
    have hd : (Ur.map colC).drop s=[] := List.drop_of_length_le (by simp; omega)
    funext x; cases x <;> simp [rsbUpd2, hΨ, hsel, hd]
  · rw [hsn]

/-- **Block reversal.** The blocks of `x` (each `L` records) land on `y` in reverse order. -/
theorem band_rev_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {x y c n tn : RsbR} (hd : [x, y, c, n, tn, .tC, .ac2].Nodup) {w L : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (blocks : List (List GaussianInt))
    (hbl : ∀ b ∈ blocks, b.length = L) (XR YR : List (Fin (A + 4)))
    (hx : σ x = cstream A w blocks.flatten ++ XR) (hy : σ y = YR) (hc : (σ c).length = L * w)
    (hn : (σ n).length = blocks.length) (htn : σ tn = []) (htC : σ .tC = []) (hac2 : σ .ac2 = []) :
    RsbRuns body rg ι (bandRevP rg x y c n tn) σ
      (Function.update (Function.update σ x XR) y (cstream A w blocks.reverse.flatten ++ YR))
      (blocks.length * (6 * (L * w) + 6 + 6) + 4) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hxy, hxc, hxn, hxt, hxC, hxa⟩, ⟨hyc, hyn, hyt, hyC, hya⟩, ⟨hcn, hct, hcC, hca⟩,
    ⟨hnt, hnC, hna⟩, ⟨htC', hta⟩, hCa, -⟩ := hd
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update σ x (cstream A w (blocks.drop j).flatten ++ XR)) y
        (cstream A w (blocks.take j).reverse.flatten ++ YR) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ n).length, ∀ X Y, RsbRuns body rg ι
      (.seq (rsbMv (rg c) (rg .tC) (rg x) (rg .ac2)) (moveR (rg .ac2) (rg y) id))
      (rsbUpd2 (Ψ j) n X tn Y) (rsbUpd2 (Ψ (j + 1)) n X tn Y) (6 * (L * w) + 6) := by
    intro j hj X Y
    rw [hn] at hj
    set b := blocks[j]'hj
    have hbL : b.length = L := hbl b (List.getElem_mem _)
    have hdj : blocks.drop j = b :: blocks.drop (j+1) := List.drop_eq_getElem_cons hj
    set ρ := rsbUpd2 (Ψ j) n X tn Y
    have hρx : ρ x = cstream A w b ++ (cstream A w (blocks.drop (j+1)).flatten ++ XR) := by
      simp only [ρ, rsbUpd2, hΨ, Function.update_apply]
      split_ifs; simp_all
    have hρc : (ρ c).length = b.length * w := by
      simp only [ρ, rsbUpd2, hΨ, Function.update_apply]
      split_ifs <;> simp_all
    have hρt : ρ .tC = [] := by
      simp only [ρ, rsbUpd2, hΨ, Function.update_apply]
      split_ifs <;> simp_all
    have hρa : ρ .ac2 = [] := by
      simp only [ρ, rsbUpd2, hΨ, Function.update_apply]
      split_ifs <;> simp_all
    have hd4 : [c, RsbR.tC, x, RsbR.ac2].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true]
      exact ⟨⟨hcC, Ne.symm hxc, hca⟩, ⟨Ne.symm hxC, hCa⟩, hxa, not_false⟩
    have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := c) (t := .tC) (x := x) (y := .ac2)
      hd4 ρ hρt (by rw [hρc, hρx]; simp)
    rw [hρc, hρx, take_cstream _ _ le_rfl, drop_cstream, List.take_length, List.drop_length,
      Nat.sub_self, zero_mul, List.drop_zero, cstream_nil, List.nil_append, hρa, List.append_nil] at h₁
    set ρ₁ := Function.update (Function.update ρ x (cstream A w (blocks.drop (j+1)).flatten ++ XR))
      .ac2 (cstream A w b).reverse
    have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := y) (Ne.symm hya) ρ₁
    refine ((RsbRuns.seq hdisj h₁ h₂).congr ?_).mono ?_
    · have htk : (blocks.take (j+1)).reverse.flatten = b ++ (blocks.take j).reverse.flatten := by
        rw [List.take_succ_eq_append_getElem hj, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.flatten_cons]
      funext z
      simp only [ρ₁, ρ, rsbUpd2, hΨ, Function.update_apply]
      split_ifs <;> simp_all
    · simp [ρ₁, hbL]; omega
  have h := rsb_rep_runs hrg hdisj (ra := n) (rt := tn) hnt _ (σ n) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_
  · funext z; simp only [rsbUpd2, hΨ, Function.update_apply]
    split_ifs <;> simp_all
  · funext z; simp only [rsbUpd2, hΨ, Function.update_apply, hn]
    split_ifs <;> simp_all [List.drop_of_length_le, List.take_of_length_le]
  · rw [hn]

/-- `|n|` copies of register `a` onto `b`, one per symbol of the counter `n`. -/
theorem band_copyRepG_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {a b n tn : RsbR} (hd : [a, b, n, tn, .b1, .tC].Nodup)
    (σ : RsbR → List (Fin (A + 4))) (hb1 : σ .b1 = []) (htC : σ .tC = []) (htn : σ tn = []) :
    RsbRuns body rg ι (rsbRep (rg n) (rg tn) (rsbCopyTo rg a b)) σ
      (Function.update σ b ((List.replicate (σ n).length (σ a)).flatten ++ σ b))
      ((σ n).length * (6 * (σ a).length + 6 + 6) + 4) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hab, han, hat, ha1, haC⟩, ⟨hbn, hbt, hb1', hbC⟩, ⟨hnt, hn1, hnC⟩, ⟨ht1, htC'⟩, h1C, -⟩ := hd
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update σ b ((List.replicate j (σ a)).flatten ++ σ b) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ n).length, ∀ X Y, RsbRuns body rg ι (rsbCopyTo rg a b)
      (rsbUpd2 (Ψ j) n X tn Y) (rsbUpd2 (Ψ (j + 1)) n X tn Y) (6 * (σ a).length + 6) := by
    intro j _ X Y
    have h := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj ⟨ha1, haC⟩ ⟨hb1', hbC⟩ hab
      (rsbUpd2 (Ψ j) n X tn Y)
      (by simp only [rsbUpd2, hΨ, Function.update_apply]; split_ifs <;> simp_all)
      (by simp only [rsbUpd2, hΨ, Function.update_apply]; split_ifs <;> simp_all)
    have hA : rsbUpd2 (Ψ j) n X tn Y a=σ a := by
      simp only [rsbUpd2, hΨ, Function.update_apply]; split_ifs; simp_all
    rw [hA] at h
    refine h.congr ?_
    funext x
    simp only [rsbUpd2, hΨ, Function.update_apply, List.replicate_succ, List.flatten_cons,
      List.append_assoc]
    split_ifs <;> simp_all
  have h := rsb_rep_runs hrg hdisj (ra := n) (rt := tn) hnt (rsbCopyTo rg a b) (σ n) Ψ _ hbody
  refine (h.congr_pre ?_ |>.congr ?_)
  · funext x
    simp only [rsbUpd2, hΨ, Function.update_apply, List.replicate_zero, List.flatten_nil,
      List.nil_append]
    split_ifs <;> simp_all
  · funext x
    simp only [rsbUpd2, hΨ, Function.update_apply]
    split_ifs <;> simp_all

/-- The cost of the reorganization. -/
def bandAxisOrgCost (s k w K : ℕ) : ℕ := 200 * (s + k + 2) * (k + 2) * w + 2 * K + 200

lemma bandAxisOrg_arith (s k w K : ℕ) (hw : 1 ≤ w) :
    2 * (2 * (k + 1)) + 2 + (6 * (k + 1) + 6 + (2 * K + 2 + (s * (6 * (k + 1) + 6 + 6) + 4 +
      (s * (k + 1) * (6 * w + 6 + 6) + 4 + (s * (6 * ((2 * (k + 1) + 1) * w) + 6 + 6) + 4 +
      ((k + 1) * (6 * w + 6 + 6) + 4 + ((k + 1) * (6 * ((k + 1) * w) + 6 + 6) + 4 +
      (2 * ((k + 1) * w) + 2 + (2 * (k + 1) + 2 + (6 * k + 6 + (2 * (2 * (k + 1) * w) + 2 +
      (6 * (k * w) + 6 + (6 * w + 6))))))))))))) ≤ bandAxisOrgCost s k w K := by
  unfold bandAxisOrgCost
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  ring_nf
  nlinarith [Nat.zero_le (s * k * v), Nat.zero_le (k * k * v), Nat.zero_le (s * v), Nat.zero_le (k * v),
    Nat.zero_le (s * k), Nat.zero_le (k * k), Nat.zero_le v]

/-- **The reorganization of the factor outputs.** -/
theorem band_axisOrg_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w k s : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (Lf : List ℤ) (hLf : Lf.length = s * (k + 1))
    (Ur : List (List ℤ)) (hUr : Ur.length = s) (hrow : ∀ row ∈ Ur, row.length = 2 * (k + 1) + 1)
    (SRC : List (Fin (A + 4)))
    (hdout : σ .dout = cstream A w ((Lf.map fun x => (⟨x, 0⟩ : GaussianInt)).reverse))
    (hhf : σ .hf = cstream A w (Ur.map colC).reverse.flatten) (hsrc : σ .src = SRC)
    (hbo : σ .bo = []) (hvk : σ .vk = []) (hxs : σ .xs = []) (hmsk : σ .msk = csyms A w 0)
    (hms : (σ .ms).length = k + 1) (hsn : (σ .sn).length = s)
    (hsmwn : (σ .smwn).length = (2 * (k + 1) + 1) * w) (hwn : (σ (.cm .wn)).length = w)
    (htK : σ .tK = []) (htL : σ .tL = []) (hsel : σ .sel = []) (htC : σ .tC = []) (hb1 : σ .b1 = [])
    (hac2 : σ .ac2 = []) {K : ℕ} (hm2n : (σ .m2n).length = 2 * (k + 1)) (hkn : (σ .kn).length = K)
    (hmwn : (σ .mwn).length = 2 * (k + 1) * w) (hm2wn : (σ .m2wn).length = k * w)
    (hdst : (σ .dst).length = k) (hw : 1 ≤ w) :
    RsbRuns body rg ι (bandAxisOrgP rg) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update σ
        .m2n (σ .ms)) .kn ((List.replicate s (σ .ms)).flatten)) .dout [])
        .bo (cstream A w (Lf.map fun x => (⟨x, 0⟩ : GaussianInt)))) .hf [])
        .src (cstream A w (Ur.map colC).flatten ++ SRC))
        .vk ((List.replicate (k + 1) ((List.replicate (k + 1) (csyms A w 0)).flatten)).flatten))
        .ms (σ .dst)) .mwn (σ (.cm .wn) ++ σ .m2wn)) (bandAxisOrgCost s k w K) := by
  set C : ℤ → GaussianInt := fun x => ⟨x, 0⟩ with hC
  have hsing : ∀ l : List ℤ, (l.map fun x => [C x]).flatten = l.map C := by
    intro l; induction l <;> simp_all
  have hsing' : ∀ l : List ℤ, (l.map (List.reverse ∘ fun x => [C x])).flatten = l.map C := by
    intro l; induction l <;> simp_all
  have h₁ := rsb_emptyR_runs (body := body) (ι := ι) hrg .m2n σ
  set σ₁ := Function.update σ .m2n []
  have h₂ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .ms) (b := .m2n)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₁ (by simp [σ₁, hb1])
    (by simp [σ₁, htC])
  set σ₂ := Function.update σ₁ .m2n (σ₁ .ms ++ σ₁ .m2n)
  have h₃ := rsb_emptyR_runs (body := body) (ι := ι) hrg .kn σ₂
  set σ₃ := Function.update σ₂ .kn []
  have h₄ := band_copyRepG_runs (body := body) (ι := ι) hrg hdisj (a := .ms) (b := .kn) (n := .sn)
    (tn := .sel) (by decide) σ₃ (by simp [σ₃, σ₂, σ₁, hb1]) (by simp [σ₃, σ₂, σ₁, htC])
    (by simp [σ₃, σ₂, σ₁, hsel])
  set σ₄ := Function.update σ₃ .kn ((List.replicate (σ₃ .sn).length (σ₃ .ms)).flatten ++ σ₃ .kn)
  have hkn4 : (σ₄ .kn).length = (Lf.map fun x => [C x]).reverse.length := by
    simp [σ₄, σ₃, σ₂, σ₁, hsn, hms, hLf, List.length_flatten, List.sum_replicate]
  have h₅ := band_rev_runs (body := body) (ι := ι) hrg hdisj (x := .dout) (y := .bo) (c := .cm .wn)
    (n := .kn) (tn := .tK) (by decide) (w := w) (L := 1) σ₄ (Lf.map fun x => [C x]).reverse
    (by intro b hb; simp at hb; obtain ⟨x, -, rfl⟩ := hb; rfl) [] []
    (by simp [σ₄, σ₃, σ₂, σ₁, hdout, List.flatten_reverse, hsing'])
    (by simp [σ₄, σ₃, σ₂, σ₁, hbo]) (by simp [σ₄, σ₃, σ₂, σ₁, hwn]) hkn4
    (by simp [σ₄, σ₃, σ₂, σ₁, htK]) (by simp [σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₄, σ₃, σ₂, σ₁, hac2])
  set σ₅ := Function.update (Function.update σ₄ .dout []) .bo
    (cstream A w (Lf.map fun x => [C x]).reverse.reverse.flatten ++ [])
  have h₆ := band_rev_runs (body := body) (ι := ι) hrg hdisj (x := .hf) (y := .src) (c := .smwn)
    (n := .sn) (tn := .sel) (by decide) (w := w) (L := 2 * (k + 1) + 1) σ₅ (Ur.map colC).reverse
    (by intro b hb; simp [colC] at hb; obtain ⟨r, hr, rfl⟩ := hb; simp [hrow r hr]) [] SRC
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hhf]) (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hsrc])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hsmwn]) (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hsn, hUr])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hsel]) (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, htC])
    (by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hac2])
  set σ₆ := Function.update (Function.update σ₅ .hf []) .src
    (cstream A w (Ur.map colC).reverse.reverse.flatten ++ SRC)
  have h₇ := band_copyRep_runs (body := body) (ι := ι) hrg hdisj (a := .msk) (b := .xs)
    ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩
    (by decide) (B := k + 1) σ₆ (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
  set σ₇ := Function.update σ₆ .xs ((List.replicate (k + 1) (σ₆ .msk)).flatten ++ σ₆ .xs)
  have h₈ := band_copyRep_runs (body := body) (ι := ι) hrg hdisj (a := .xs) (b := .vk)
    ⟨by decide, by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide, by decide⟩
    (by decide) (B := k + 1) σ₇ (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC]) (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htL])
    (by simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hms])
  set σ₈ := Function.update σ₇ .vk ((List.replicate (k + 1) (σ₇ .xs)).flatten ++ σ₇ .vk)
  have h₉ := rsb_emptyR_runs (body := body) (ι := ι) hrg .xs σ₈
  have h₁₀ := rsb_emptyR_runs (body := body) (ι := ι) hrg .ms (Function.update σ₈ .xs [])
  set σ₁₀ := Function.update (Function.update σ₈ .xs []) .ms []
  have h₁₁ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .dst) (b := .ms)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₁₀
    (by simp [σ₁₀, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₁₀, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₁₁ := Function.update σ₁₀ .ms (σ₁₀ .dst ++ σ₁₀ .ms)
  have h₁₂ := rsb_emptyR_runs (body := body) (ι := ι) hrg .mwn σ₁₁
  set σ₁₂ := Function.update σ₁₁ .mwn []
  have h₁₃ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .m2wn) (b := .mwn)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₁₂
    (by simp [σ₁₂, σ₁₁, σ₁₀, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₁₂, σ₁₁, σ₁₀, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  set σ₁₃ := Function.update σ₁₂ .mwn (σ₁₂ .m2wn ++ σ₁₂ .mwn)
  have h₁₄ := rsb_copyTo_runs (body := body) (ι := ι) hrg hdisj (a := .cm .wn) (b := .mwn)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) σ₁₃
    (by simp [σ₁₃, σ₁₂, σ₁₁, σ₁₀, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hb1])
    (by simp [σ₁₃, σ₁₂, σ₁₁, σ₁₀, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htC])
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃
    (RsbRuns.seq hdisj h₄ (RsbRuns.seq hdisj h₅ (RsbRuns.seq hdisj h₆ (RsbRuns.seq hdisj h₇
    (RsbRuns.seq hdisj h₈ (RsbRuns.seq hdisj h₉ (RsbRuns.seq hdisj h₁₀ (RsbRuns.seq hdisj h₁₁
    (RsbRuns.seq hdisj h₁₂ (RsbRuns.seq hdisj h₁₃ h₁₄))))))))))))).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₁₃, σ₁₂, σ₁₁, σ₁₀, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hvk, hxs,
      hmsk, hsn, hsing]
  · simp [σ₁₃, σ₁₂, σ₁₁, σ₁₀, σ₈, σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hvk, hxs, hmsk, hsn, hms, hm2n, hkn,
      hmwn, hm2wn, hdst, hwn, hLf, hUr, bandAxisOrgCost, csyms, List.length_flatten,
      List.sum_replicate]
    exact bandAxisOrg_arith s k w K hw

/-- **Split and factor.** -/
theorem band_axisFac_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B K s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (rows inputs : List (List ℤ)) (hrows : rows.length = B + 1)
    (hrl : ∀ row ∈ rows, row.length = 2 * B + 1) (hin : ∀ row ∈ inputs, row.length = 2 * B + 1)
    (hs : inputs.length = s) (hfit : ∀ m < s, FacFits w P K (facState P K rows inputs m))
    (hr0 : ∀ m < s, σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs m)) 0, 0⟩)
    (SRC : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w ((rows.map colC).flatten ++ (inputs.map colC).flatten) ++ SRC)
    (htswn : (σ .tswn).length = (B + 1) * (2 * B + 1) * w)
    (hhf : σ .hf = []) (hdf : σ .df = []) (hdout : σ .dout = []) (hmsk : σ .msk = csyms A w 0)
    (hvk : σ .vk = []) (hef : σ .ef = []) (htb : σ .tb = []) (hsr : σ .sr = []) (hbo : σ .bo = [])
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hac : σ .ac = []) (hac2 : σ .ac2 = []) (hnv : σ .nv = [])
    (hb1 : σ .b1 = []) (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = [])
    (htK : σ .tK = []) (htL : σ .tL = []) (hsel : σ .sel = []) (hsn : (σ .sn).length = s)
    (hkn : (σ .kn).length = K) (hms : (σ .ms).length = B) (hm2n : (σ .m2n).length = 2 * B)
    (hmwn : (σ .mwn).length = 2 * B * w) (hsmwn : (σ .smwn).length = (2 * B + 1) * w) :
    RsbRuns body rg ι (bandAxisFacP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update σ
        .src SRC)
        .hf (cstream A w ((List.range s).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten))
        .df (cstream A w ((List.range s).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt))))
        .dout (cstream A w (((List.range s).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse)))
      (4 * ((B + 1) * (2 * B + 1) * w) + 4 + (2 * ((B + 1) * (2 * B + 1) * w) + 2) +
        (s * (bandFacStepCost w B K + 6) + 4) + (2 * ((B + 1) * (2 * B + 1) * w) + 2)) := by
  have hwl : ((rows.map colC).flatten).length = (B + 1) * (2 * B + 1) := by
    rw [List.length_flatten, List.map_map]
    rw [List.map_congr_left (g := fun _ => 2 * B + 1) (fun r hr => by simp [colC, hrl r hr]),
      List.map_const', List.sum_replicate, hrows, smul_eq_mul]
  have h₁ := rsb_mv_runs (body := body) (ι := ι) hrg (c := .tswn) (t := .tC) (x := .src) (y := .ac2)
    (by decide) σ htC (by rw [htswn, hsrc]; simp [hwl])
  have hl1 : (σ .tswn).length = ((rows.map colC).flatten).length * w := by rw [htswn, hwl]
  rw [hl1, hsrc, cstream_append, List.append_assoc, take_cstream _ _ le_rfl, drop_cstream,
    List.take_length, List.drop_length, Nat.sub_self, zero_mul, List.drop_zero, cstream_nil,
    List.nil_append, hac2, List.append_nil] at h₁
  set σ₁ := Function.update (Function.update σ .src (cstream A w (inputs.map colC).flatten ++ SRC))
    .ac2 (cstream A w (rows.map colC).flatten).reverse
  have h₂ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .vk) (by decide) σ₁
  set σ₂ := Function.update (Function.update σ₁ .ac2 []) .vk ((σ₁ .ac2).reverse ++ σ₁ .vk)
  have hready₂ : RsbReady σ₂ w P := by
    simp only [σ₂, σ₁]
    exact (((hready.update .src (fun c => by simp) _).update .ac2 (fun c => by simp) _).update .ac2
      (fun c => by simp) _).update .vk (fun c => by simp) _
  have h₃ := band_facLoop_runs (body := body) (ι := ι) (w := w) (B := B) (K := K) (s := s) hrg hdisj hι
    hT hQ hA σ₂ hready₂ hw hp rows inputs hrows hrl hin hs hfit
    (fun m hm => by simp [σ₂, σ₁, hr0 m hm]) SRC [] [] []
    (by simp [σ₂, σ₁, hvk]) (by simp [σ₂, σ₁]) (by simp [σ₂, σ₁, hhf]) (by simp [σ₂, σ₁, hdf])
    (by simp [σ₂, σ₁, hdout]) (by simp [σ₂, σ₁, hmsk]) (by simp [σ₂, σ₁, hef]) (by simp [σ₂, σ₁, htb])
    (by simp [σ₂, σ₁, hsr]) (by simp [σ₂, σ₁, hbo]) (by simp [σ₂, σ₁, hhv]) (by simp [σ₂, σ₁, hxa])
    (by simp [σ₂, σ₁, hhc]) (by simp [σ₂, σ₁, hya]) (by simp [σ₂, σ₁, hxs]) (by simp [σ₂, σ₁, hpr])
    (by simp [σ₂, σ₁, hac]) (by simp [σ₂, σ₁]) (by simp [σ₂, σ₁, hnv]) (by simp [σ₂, σ₁, hb1])
    (by simp [σ₂, σ₁, htC]) (by simp [σ₂, σ₁, htA]) (by simp [σ₂, σ₁, htJ]) (by simp [σ₂, σ₁, htK])
    (by simp [σ₂, σ₁, htL]) (by simp [σ₂, σ₁, hsel]) (by simp [σ₂, σ₁, hsn]) (by simp [σ₂, σ₁, hkn])
    (by simp [σ₂, σ₁, hms]) (by simp [σ₂, σ₁, hm2n]) (by simp [σ₂, σ₁, hmwn]) (by simp [σ₂, σ₁, hsmwn])
  set σ₃ := Function.update (Function.update (Function.update (Function.update (Function.update σ₂ .vk
    (cstream A w ((facState P K rows inputs s).map colC).flatten)) .src SRC)
    .hf (cstream A w ((List.range s).reverse.map fun j =>
      colC ((facState P K rows inputs j).headD [])).flatten ++ []))
    .df (cstream A w ((List.range s).reverse.map fun j =>
      (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ++ []))
    .dout (cstream A w (((List.range s).map fun j =>
      colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse) ++ [])
  have h₄ := rsb_emptyR_runs (body := body) (ι := ι) hrg .vk σ₃
  have hfl : (cstream A w ((facState P K rows inputs s).map colC).flatten).length =
      (B + 1) * (2 * B + 1) * w := by
    obtain ⟨hl, hrl'⟩ := facState_shape P K B rows inputs hrows hrl hin s (by omega)
    rw [length_cstream, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => 2 * B + 1) (fun r hr => by simp [colC, hrl' r hr]),
      List.map_const', List.sum_replicate, hl, smul_eq_mul]
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃ h₄))).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₃, σ₂, σ₁, hvk, hac2]
  · simp only [σ₃, Function.update_self, σ₁, σ₂, length_cstream, List.length_reverse, hwl]
    simp [hvk]
    have hsum : (List.map (List.length ∘ colC) (facState P K rows inputs s)).sum = (B + 1) * (2 * B + 1) := by
      obtain ⟨hl, hrl'⟩ := facState_shape P K B rows inputs hrows hrl hin s (by omega)
      rw [List.map_congr_left (g := fun _ => 2 * B + 1) (fun r hr => by simp [colC, hrl' r hr]),
        List.map_const', List.sum_replicate, hl, smul_eq_mul]
    rw [hsum]; omega

/-- **Transpose and store.** -/
theorem band_axisTr_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w k s : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (Ur : List (List ℤ)) (hUr : Ur.length = s)
    (hrow : ∀ row ∈ Ur, row.length = 2 * (k + 1) + 1) (SRC : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w (Ur.map colC).flatten ++ SRC)
    (hvk : σ .vk = cstream A w ((Mult.BandFactor.tWin (k + 1) Ur 0).map colC).flatten)
    (hef : σ .ef = []) (hhf : σ .hf = []) (hmsk : σ .msk = csyms A w 0) (hpr : σ .pr = [])
    (hxs : σ .xs = []) (hya : σ .ya = []) (hnv : σ .nv = []) (htC : σ .tC = []) (htL : σ .tL = [])
    (hsel : σ .sel = []) (hac2 : σ .ac2 = []) (hsn : (σ .sn).length = s)
    (hwn : (σ (.cm .wn)).length = w) (hmwn : (σ .mwn).length = (k + 1) * w)
    (hm2wn : (σ .m2wn).length = k * w) (hms : (σ .ms).length = k) :
    RsbRuns body rg ι (bandAxisTrP rg) σ
      (Function.update (Function.update (Function.update σ .src SRC) .vk []) .hf
        (cstream A w ((List.range s).reverse.map fun m =>
          colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten))
      (s * (bandTStepCost w k + 6) + 4 + (2 * ((k + 1) * (k + 1) * w) + 2) +
        (2 * (s * (k + 1) * w) + 2) + (2 * (s * (k + 1) * w) + 2)) := by
  have h₁ := band_tLoop_runs (body := body) (ι := ι) hrg hdisj σ Ur hUr hrow SRC [] hsrc hvk hef hmsk
    hpr hxs hya hnv htC htL hsel hsn hwn hmwn hm2wn hms
  set σ₁ := Function.update (Function.update (Function.update σ .src SRC) .vk
    (cstream A w ((Mult.BandFactor.tWin (k + 1) Ur s).map colC).flatten))
    .ef (cstream A w ((List.range s).reverse.map fun m =>
      colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten ++ [])
  have h₂ := rsb_emptyR_runs (body := body) (ι := ι) hrg .vk σ₁
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ef) (b := .ac2) (by decide)
    (Function.update σ₁ .vk [])
  have h₄ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .hf) (by decide)
    (Function.update (Function.update (Function.update σ₁ .vk []) .ef [])
      .ac2 (((Function.update σ₁ .vk []) .ef).reverse ++ (Function.update σ₁ .vk []) .ac2))
  have hwin : ∀ m, (cstream A w ((Mult.BandFactor.tWin (k + 1) Ur m).map colC).flatten).length =
      (k + 1) * (k + 1) * w := by
    intro m
    rw [length_cstream, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => k + 1) (fun r hr => by
        simp only [Mult.BandFactor.tWin, List.mem_map] at hr
        obtain ⟨d, -, rfl⟩ := hr
        simp [colC]),
      List.map_const', List.sum_replicate, smul_eq_mul]
    simp [Mult.BandFactor.tWin]
  have hcols : (cstream A w ((List.range s).reverse.map fun m =>
      colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten).length = s * (k + 1) * w := by
    rw [length_cstream, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => k + 1) (fun m _ => by simp [colC, Mult.BandFactor.ucolZ]),
      List.map_const', List.sum_replicate, smul_eq_mul]
    simp
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ (RsbRuns.seq hdisj h₃ h₄))).congr ?_).mono ?_
  · funext x; cases x <;> simp [σ₁, hef, hhf, hac2]
  · simp only [σ₁, Function.update_self, Function.update_of_ne (by decide : RsbR.ef ≠ RsbR.vk),
      Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.ef),
      Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.vk), Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.src),
      List.append_nil, hcols, List.length_reverse, hac2]
    rw [Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.ef), Function.update_self, hwin]
    omega

/-- The forward table: all multipliers in pivot order. -/
def facLf (P K : ℕ) (rows inputs : List (List ℤ)) (s : ℕ) : List ℤ :=
  ((List.range s).map fun j => Mult.BandFactor.lcolZ P K (facState P K rows inputs j)).flatten

/-- The forward factor table has one fixed-width column per pivot. -/
theorem length_facLf (P K B n : ℕ) (rows inputs : List (List ℤ))
    (hrows : rows.length = B+1) (hrl : ∀ row ∈ rows, row.length = 2*B+1)
    (hin : ∀ row ∈ inputs, row.length = 2*B+1) (hn : n ≤ inputs.length) :
    (facLf P K rows inputs n).length = n*B := by
  rw [facLf,List.length_flatten,List.map_map]
  rw [List.map_congr_left (g := fun _ => B) (fun j hj => by
    have hj' := List.mem_range.mp hj
    obtain ⟨hl,_⟩ := facState_shape P K B rows inputs hrows hrl hin j (by omega)
    obtain ⟨r,rest,hr⟩ : ∃ r rest, facState P K rows inputs j = r::rest := by
      cases h : facState P K rows inputs j with
      | nil => rw [h] at hl; simp at hl
      | cons r rest => exact ⟨r,rest,rfl⟩
    simp only [Function.comp,hr,Mult.BandFactor.lcolZ,List.length_map]
    rw [hr] at hl
    simpa using hl)]
  simp

/-- The pivot rows in pivot order. -/
def facUr (P K : ℕ) (rows inputs : List (List ℤ)) (s : ℕ) : List (List ℤ) :=
  (List.range s).map fun j => (facState P K rows inputs j).headD []

/-- The cost of the per-axis preparation. -/
def bandAxisPrepCost (w k K s : ℕ) : ℕ :=
  (4 * ((k + 1 + 1) * (2 * (k + 1) + 1) * w) + 4 + (2 * ((k + 1 + 1) * (2 * (k + 1) + 1) * w) + 2) +
    (s * (bandFacStepCost w (k + 1) K + 6) + 4) + (2 * ((k + 1 + 1) * (2 * (k + 1) + 1) * w) + 2)) +
  (bandAxisOrgCost s k w K + (s * (bandTStepCost w k + 6) + 4 + (2 * ((k + 1) * (k + 1) * w) + 2) +
    (2 * (s * (k + 1) * w) + 2) + (2 * (s * (k + 1) * w) + 2)))

/-- **The per-axis preparation.** `bo` holds the forward table, `hf` the backward columns
(last pivot on top), `df` the pivot reciprocals (last on top); `m2n`, `mwn` hold `B` and
`B w` symbols for the line passes. -/
theorem band_axisPrep_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P k K s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (rows inputs : List (List ℤ)) (hrows : rows.length = k + 1 + 1)
    (hrl : ∀ row ∈ rows, row.length = 2 * (k + 1) + 1)
    (hin : ∀ row ∈ inputs, row.length = 2 * (k + 1) + 1)
    (hs : inputs.length = s) (hfit : ∀ m < s, FacFits w P K (facState P K rows inputs m))
    (hr0 : ∀ m < s, σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs m)) 0, 0⟩)
    (SRC : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w ((rows.map colC).flatten ++ (inputs.map colC).flatten) ++ SRC)
    (htswn : (σ .tswn).length = (k + 1 + 1) * (2 * (k + 1) + 1) * w)
    (hhf : σ .hf = []) (hdf : σ .df = []) (hdout : σ .dout = []) (hmsk : σ .msk = csyms A w 0)
    (hvk : σ .vk = []) (hef : σ .ef = []) (htb : σ .tb = []) (hsr : σ .sr = []) (hbo : σ .bo = [])
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hac : σ .ac = []) (hac2 : σ .ac2 = []) (hnv : σ .nv = [])
    (hb1 : σ .b1 = []) (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = [])
    (htK : σ .tK = []) (htL : σ .tL = []) (hsel : σ .sel = []) (hsn : (σ .sn).length = s)
    (hkn : (σ .kn).length = K) (hms : (σ .ms).length = k + 1) (hm2n : (σ .m2n).length = 2 * (k + 1))
    (hmwn : (σ .mwn).length = 2 * (k + 1) * w)
    (hsmwn : (σ .smwn).length = (2 * (k + 1) + 1) * w) (hm2wn : (σ .m2wn).length = k * w)
    (hdst : (σ .dst).length = k) :
    ∃ σ', RsbRuns body rg ι (bandAxisPrepP rg hι hT hQ) σ σ' (bandAxisPrepCost w k K s) ∧
      σ' .bo = cstream A w ((facLf P K rows inputs s).map fun x => (⟨x, 0⟩ : GaussianInt)) ∧
      σ' .hf = cstream A w ((List.range s).reverse.map fun m =>
        colC (Mult.BandFactor.ucolZ (k + 1) (facUr P K rows inputs s) m)).flatten ∧
      σ' .df = cstream A w ((List.range s).reverse.map fun j =>
        (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ∧
      σ' .src = SRC ∧ (σ' .m2n).length = k + 1 ∧ (σ' .mwn).length = (k + 1) * w ∧
      (σ' .sn).length = s ∧ σ' .dout = [] ∧ σ' .vk = [] ∧ σ' .ef = [] ∧ σ' .xs = [] ∧
      (σ' .kn).length = s * (k + 1) ∧ σ' .ms = σ .dst ∧ σ' .m2n = σ .ms ∧
      σ' .kn = (List.replicate s (σ .ms)).flatten ∧ σ' .mwn = σ (.cm .wn) ++ σ .m2wn ∧
      RsbReady σ' w P ∧
      ∀ r, r ∉ ([.src, .hf, .df, .dout, .bo, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] : List RsbR) →
        σ' r = σ r := by
  have hwn := hready.wn
  set Lf := facLf P K rows inputs s with hLfdef
  set Ur := facUr P K rows inputs s with hUrdef
  have hshape := fun j (hj : j ≤ s) => facState_shape P K (k + 1) rows inputs hrows hrl hin j (by omega)
  have hLf : Lf.length = s * (k + 1) :=
    length_facLf P K (k+1) s rows inputs hrows hrl hin (by omega)
  have hUr : Ur.length = s := by simp [hUrdef, facUr]
  have hUrow : ∀ row ∈ Ur, row.length = 2 * (k + 1) + 1 := by
    intro row hrow
    simp only [hUrdef, facUr, List.mem_map, List.mem_range] at hrow
    obtain ⟨j, hj, rfl⟩ := hrow
    obtain ⟨hl, hrl'⟩ := hshape j hj.le
    cases h : facState P K rows inputs j with
    | nil => rw [h] at hl; simp at hl
    | cons a l => exact hrl' a (by rw [h]; simp)
  have h₁ := band_axisFac_runs (body := body) (ι := ι) (w := w) (B := k + 1) (K := K) (s := s) hrg hdisj
    hι hT hQ hA σ hready hw hp rows inputs hrows hrl hin hs hfit hr0 SRC hsrc htswn hhf hdf hdout hmsk
    hvk hef htb hsr hbo hhv hxa hhc hya hxs hpr hac hac2 hnv hb1 htC htA htJ htK htL hsel hsn hkn hms
    hm2n hmwn hsmwn
  set σ₁ := Function.update (Function.update (Function.update (Function.update σ
        .src SRC)
        .hf (cstream A w ((List.range s).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten))
        .df (cstream A w ((List.range s).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt))))
        .dout (cstream A w (((List.range s).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse))
  have hd₁ : σ₁ .dout = cstream A w ((Lf.map fun x => (⟨x, 0⟩ : GaussianInt)).reverse) := by
    simp [σ₁, hLfdef, facLf, colC, List.map_flatten, Function.comp_def]
  have hh₁ : σ₁ .hf = cstream A w (Ur.map colC).reverse.flatten := by
    simp [σ₁, hUrdef, facUr, List.map_reverse, Function.comp_def]
  have h₂ := band_axisOrg_runs (body := body) (ι := ι) hrg hdisj (w := w) (k := k) (s := s) (K := K) σ₁ Lf hLf Ur
    hUr hUrow SRC hd₁ hh₁ (by simp [σ₁]) (by simp [σ₁, hbo]) (by simp [σ₁, hvk]) (by simp [σ₁, hxs])
    (by simp [σ₁, hmsk]) (by simp [σ₁, hms]) (by simp [σ₁, hsn]) (by simp [σ₁, hsmwn])
    (by simp [σ₁, hwn]) (by simp [σ₁, htK]) (by simp [σ₁, htL]) (by simp [σ₁, hsel])
    (by simp [σ₁, htC]) (by simp [σ₁, hb1]) (by simp [σ₁, hac2]) (by simp [σ₁, hm2n])
    (by simp [σ₁, hkn]) (by simp [σ₁, hmwn]) (by simp [σ₁, hm2wn]) (by simp [σ₁, hdst]) hw
  set σ₂ := Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update σ₁
        .m2n (σ₁ .ms)) .kn ((List.replicate s (σ₁ .ms)).flatten)) .dout [])
        .bo (cstream A w (Lf.map fun x => (⟨x, 0⟩ : GaussianInt)))) .hf [])
        .src (cstream A w (Ur.map colC).flatten ++ SRC))
        .vk ((List.replicate (k + 1) ((List.replicate (k + 1) (csyms A w 0)).flatten)).flatten))
        .ms (σ₁ .dst)) .mwn (σ₁ (.cm .wn) ++ σ₁ .m2wn)
  have hz : (List.replicate (k + 1) ((List.replicate (k + 1) (csyms A w 0)).flatten)).flatten =
      cstream A w ((Mult.BandFactor.tWin (k + 1) Ur 0).map colC).flatten := by
    rw [Mult.BandFactor.tWin_zero]
    simp [cstream, colC, List.flatMap, List.map_replicate, List.flatten_replicate_replicate]
    have hrep : ∀ (a b : ℕ) (x : List (Fin (A + 4))),
        (List.replicate a (List.replicate b x).flatten).flatten = (List.replicate (a * b) x).flatten := by
      intro a b x
      induction a with
      | zero => simp
      | succ a ih =>
        rw [List.replicate_succ, List.flatten_cons, ih, show (a + 1) * b = b + a * b by ring,
          List.replicate_add, List.flatten_append]
    rw [hrep]; rfl
  have h₃ := band_axisTr_runs (body := body) (ι := ι) hrg hdisj (w := w) (k := k) (s := s) σ₂ Ur hUr
    hUrow SRC (by simp [σ₂]) (by simp [σ₂, hz]) (by simp [σ₂, σ₁, hef]) (by simp [σ₂])
    (by simp [σ₂, σ₁, hmsk]) (by simp [σ₂, σ₁, hpr]) (by simp [σ₂, σ₁, hxs]) (by simp [σ₂, σ₁, hya])
    (by simp [σ₂, σ₁, hnv]) (by simp [σ₂, σ₁, htC]) (by simp [σ₂, σ₁, htL]) (by simp [σ₂, σ₁, hsel])
    (by simp [σ₂, σ₁, hac2]) (by simp [σ₂, σ₁, hsn]) (by simp [σ₂, σ₁, hwn])
    (by simp [σ₂, σ₁, hwn, hm2wn]; ring) (by simp [σ₂, σ₁, hm2wn]) (by simp [σ₂, σ₁, hdst])
  refine ⟨_, (RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ h₃)).mono (le_of_eq rfl), by simp [σ₂], by simp,
    by simp [σ₂, σ₁], by simp [σ₂, σ₁], by simp [σ₂, σ₁, hms], by simp [σ₂, σ₁, hwn, hm2wn]; ring,
    by simp [σ₂, σ₁, hsn], by simp [σ₂, σ₁], by simp [σ₂, σ₁], by simp [σ₂, σ₁, hef],
    by simp [σ₂, σ₁, hxs], by simp [σ₂, σ₁, hms], by simp [σ₂, σ₁], by simp [σ₂, σ₁],
    by simp [σ₂, σ₁], by simp [σ₂, σ₁], ⟨by simp [σ₂, σ₁, hwn], by simp [σ₂, σ₁, hready.pn],
      by simp [σ₂, σ₁, hready.nn], fun c h1 h2 h3 h4 h5 h6 => by
        simp [σ₂, σ₁, hready.empty c h1 h2 h3 h4 h5 h6]⟩, fun r hr => ?_⟩
  cases r <;> simp [σ₂, σ₁] at hr ⊢

end Contracts

end IntegerMultBounds.MathlibTM2.Fast
