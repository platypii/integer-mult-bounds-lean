module

public import IntegerMultBounds.MathlibTM2.Routing.HaloFieldPass

/-! Shared dimension and header language for ordered halo prefix scans. The
context contains ordinary retained inputs, never execution or layout suppliers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloPassContext
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main PaddedFieldLayout
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

structure Parameters where
  w : ℕ
  V : ℕ
  B : ℕ
  L : ℕ
  H : ℕ
  N : ℕ
  k : ℕ
  r : ℕ
  w_pos : 0 < w
  B_pos : 0 < B
  L_pos : 0 < L
  N_pos : 0 < N
  gap : 2*H ≤ L
  fits : (N*L+2*H)*(B*w) < 2^V
  count_fits : N+2 < 2^V
  capacity : L ≤ 2^k
  return_capacity : L+2*H ≤ 2^r

def input (A : ℕ) (p : Parameters) (matrices : List (List (List GaussianInt))) :=
  (sourceRows (csyms A p.w) matrices).flatten

def output (A : ℕ) (p : Parameters) (matrices : List (List (List GaussianInt))) :=
  HaloFieldReturn.returned A p.w p.B p.L p.H p.N (HaloFieldPass.columns p.L matrices)

def Shape (p : Parameters) (matrices : List (List (List GaussianInt))) : Prop :=
  matrices.length = p.N ∧ (∀ rows ∈ matrices, rows.length = p.B) ∧
    (∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = p.L)

def scratch : List (Fin 117) := [34,35,36,96,95,94,37,38,40,41,42,93,92,114,48,49,50,51,52,53]

def Fresh (S : Stacks 117 A) : Prop := ∀ i : Fin 117, i.val < 31 ∨ i ∈ scratch → S.R i = []

structure Holds (p : Parameters) (S : Stacks 117 A) : Prop where
  rowVolume : (S.R 31).length = p.N*p.L*p.B
  haloVolume : (S.R 32).length = p.H*p.B
  wordWidth : (S.R 33).length = p.w
  metadataWidth : (S.R 115).length = p.V
  countBits : S.R 97 = binSyms p.V p.N
  lengthBits : S.R 98 = binSyms p.V (p.L*(p.B*p.w))
  overlapBits : S.R 100 = binSyms p.V (2*(p.H*(p.B*p.w)))
  zero : S.R 116 = []
  returnExponent : (S.R 43).length = p.r
  prefixCount : (S.R 44).length = p.N
  rowCount : (S.R 45).length = p.B
  currentLength : (S.R 46).length = p.L+2*p.H
  recordWidth : (S.R 47).length = p.w
  forwardExponent : (S.R 54).length = p.k
  originalLength : (S.R 55).length = p.L

theorem Holds.frame {p : Parameters} {S F : Stacks 117 A} (h : Holds p S)
    (hf : ∀ i, i ≠ 39 → i ≠ 62 → i ≠ 61 → i ≠ 60 → F.R i = S.R i) : Holds p F := by
  constructor
  · rw [hf 31 (by decide) (by decide) (by decide) (by decide)]; exact h.rowVolume
  · rw [hf 32 (by decide) (by decide) (by decide) (by decide)]; exact h.haloVolume
  · rw [hf 33 (by decide) (by decide) (by decide) (by decide)]; exact h.wordWidth
  · rw [hf 115 (by decide) (by decide) (by decide) (by decide)]; exact h.metadataWidth
  · rw [hf 97 (by decide) (by decide) (by decide) (by decide)]; exact h.countBits
  · rw [hf 98 (by decide) (by decide) (by decide) (by decide)]; exact h.lengthBits
  · rw [hf 100 (by decide) (by decide) (by decide) (by decide)]; exact h.overlapBits
  · rw [hf 116 (by decide) (by decide) (by decide) (by decide)]; exact h.zero
  · rw [hf 43 (by decide) (by decide) (by decide) (by decide)]; exact h.returnExponent
  · rw [hf 44 (by decide) (by decide) (by decide) (by decide)]; exact h.prefixCount
  · rw [hf 45 (by decide) (by decide) (by decide) (by decide)]; exact h.rowCount
  · rw [hf 46 (by decide) (by decide) (by decide) (by decide)]; exact h.currentLength
  · rw [hf 47 (by decide) (by decide) (by decide) (by decide)]; exact h.recordWidth
  · rw [hf 54 (by decide) (by decide) (by decide) (by decide)]; exact h.forwardExponent
  · rw [hf 55 (by decide) (by decide) (by decide) (by decide)]; exact h.originalLength

theorem Fresh.frame {S F : Stacks 117 A} (h : Fresh S)
    (hf : ∀ i, i ≠ 39 → i ≠ 62 → i ≠ 61 → i ≠ 60 → F.R i = S.R i) : Fresh F := by
  intro i hi
  have h39 : i ≠ 39 := by intro he; subst i; norm_num [scratch] at hi
  have h62 : i ≠ 62 := by intro he; subst i; norm_num [scratch] at hi
  have h61 : i ≠ 61 := by intro he; subst i; norm_num [scratch] at hi
  have h60 : i ≠ 60 := by intro he; subst i; norm_num [scratch] at hi
  rw [hf i h39 h62 h61 h60]
  exact h i hi

def forwardVolume (p : Parameters) := p.N*(p.B*(2^p.k*p.w))
def returnVolume (p : Parameters) := p.N*(p.B*(2^p.r*p.w))
def haloCost (p : Parameters) := GeneratedPeriodicHalo.cost (p.N*p.L*p.B) (p.H*p.B) p.w p.N p.V (p.L*p.B)
def passCost (p : Parameters) :=
  p.k*(60*forwardVolume p+3)+384*forwardVolume p+2+
    (haloCost p+p.r*(64*returnVolume p+3)+384*returnVolume p+2)
def passStock (p : Parameters) := 1000*forwardVolume p+(3*haloCost p+1000*returnVolume p)
def outputVolume (p : Parameters) := p.N*(p.B*((p.L+2*p.H)*p.w))

theorem output_length (A : ℕ) (p : Parameters) (matrices : List (List (List GaussianInt)))
    (hshape : Shape p matrices) : (output A p matrices).length = outputVolume p := by
  have hc := HaloFieldPass.columns_shape p.N p.B p.L matrices hshape.1 hshape.2.1
  have hH : p.H ≤ (HaloFieldPass.columns p.L matrices).length := by
    rw [hc.1]
    have h := Nat.le_mul_of_pos_left p.L p.N_pos
    have hg := p.gap
    omega
  exact HaloFieldReturn.returned_length A p.w p.B p.L p.H p.N _ hc.1 hH

theorem pass_exec (p : Parameters) (matrices : List (List (List GaussianInt))) (hshape : Shape p matrices)
    (hA : 4 ≤ A) (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hh : Holds p S) (hf : Fresh S) (hsrc : S.R 39 = input A p matrices++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ passCost p ∧
      Exec body HaloFieldPass.run (mk v S) n (mk vf {S with R := Function.update S.R 39 (output A p matrices++tail)}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+passStock p) depth HaloFieldPass.run
        (mk v S) n (mk vf {S with R := Function.update S.R 39 (output A p matrices++tail)})) :=
  HaloFieldPass.run_exec p.w p.V p.B p.L p.H p.N p.k p.r matrices p.w_pos p.B_pos p.N_pos p.gap
    hshape.1 hshape.2.1 hshape.2.2 p.fits p.count_fits hA p.capacity p.return_capacity tail v S
    hh.rowVolume hh.haloVolume hh.wordWidth hh.metadataWidth hh.countBits hh.lengthBits hh.overlapBits hh.zero
    hh.returnExponent hh.prefixCount hh.rowCount hh.currentLength hh.recordWidth hh.forwardExponent hh.originalLength hsrc hf

end IntegerMultBounds.MathlibTM2.Routing.HaloPassContext
