module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCoreRead
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloDescriptorPackets

/-! A returned replica block has its own coordinate accuracy, independently of
any older output suffix. Blocks remain in generated phase order in the ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def replicaPhasePackets (A V s t band a b : ℕ) (phases : List ℕ) : List (Fin (A+4)) :=
  phases.flatMap (fun phase => binSyms V (haloStart s t band a phase)++
    binSyms V (haloLength s t band a b phase))

noncomputable def ReplicaBlockAccurate {A s : ℕ} (B L q w target : ℕ)
    (lo : ZMod s) (x : ℕ → ZMod s → ℝ) (ys : List (Fin (A+4))) : Prop :=
  ys.length = B*L*w ∧ ∀ n : Fin B, ∀ i : Fin L,
    |(value q (decodeWord ((ys.drop ((n.val*L+i.val)*w)).take w))).re-
      x n (lo+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target

theorem replicaBlockAccurate_of_append {A s B L q w target : ℕ} (lo : ZMod s)
    (x : ℕ → ZMod s → ℝ) (ys tail : List (Fin (A+4))) (hlen : ys.length = B*L*w)
    (hpoint : ∀ n : Fin B, ∀ i : Fin L,
      |(value q (decodeWord (((ys++tail).drop ((n.val*L+i.val)*w)).take w))).re-
        x n (lo+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) :
    ReplicaBlockAccurate B L q w target lo x ys := by
  refine ⟨hlen,?_⟩
  intro n i
  have hidx : n.val*L+i.val+1 ≤ B*L := by
    have hh := Nat.mul_le_mul_right L (Nat.succ_le_of_lt n.isLt)
    nlinarith only [hh,i.isLt]
  have hstop : (n.val*L+i.val)*w+w ≤ ys.length := by
    rw [hlen]
    nlinarith only [Nat.mul_le_mul_right w hidx]
  have hdrop : (n.val*L+i.val)*w ≤ ys.length := by omega
  have hword : ((ys++tail).drop ((n.val*L+i.val)*w)).take w =
      (ys.drop ((n.val*L+i.val)*w)).take w := by
    rw [List.drop_append_of_le_length hdrop,List.take_append_of_le_length]
    simp only [List.length_drop]
    omega
  simpa only [hword] using hpoint n i

theorem ReplicaBlockAccurate.errorOn {A s B L q w target : ℕ} [NeZero s]
    {lo : ZMod s} {x : ℕ → ZMod s → ℝ} {ys : List (Fin (A+4))}
    (h : ReplicaBlockAccurate B L q w target lo x ys) (hfit : lo.val+L ≤ s) (n : Fin B) :
    PhaseCellInterface.ErrorOn (publishedCellCore lo L) (publishedBatchRead q w n L lo ys)
      (x n) (1/(2 : ℝ)^target) :=
  publishedBatchRead_errorOn q w n.val lo ys (x n) _ hfit (h.2 n)

theorem replicaBlocks_volume {A s B q w target : ℕ} (x : ℕ → ZMod s → ℝ)
    (length : ℕ → ℕ) (origin : ℕ → ZMod s) {phases : List ℕ}
    {blocks : List (List (Fin (A+4)))}
    (h : List.Forall₂ (fun phase ys => ReplicaBlockAccurate B (length phase) q w target
      (origin phase) x ys) phases blocks) :
    blocks.reverse.flatten.length = B*(phases.map length).sum*w := by
  have hh : (blocks.map List.length).sum = B*(phases.map length).sum*w := by
    induction h with
    | nil => simp
    | @cons phase ys phases blocks hhead htail ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [hhead.1,ih]
      ring
  simpa only [List.length_flatten,List.map_reverse,List.sum_reverse] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
