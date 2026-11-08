module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryBatch

/-! Adapt the two equal-length cached archives directly to the ordered list of
Schur RHS packets. The existing shared-factor solver accepts this exact stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 180 Q A U}

theorem cachedCyclicResidualRows_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (Cs Ds : List (ZMod s → GaussianInt)) (hlen : Cs.length = Ds.length) (w : ℕ)
    (leftTail rightTail : List (Fin (A+4))) (v : HS 180 Q A U) (S : Stacks 180 A)
    (ready : CyclicReplicaBoundaryReady (s := s) t band a n w S)
    (hleft : S.R 169 = Cs.flatMap (fun C => cstream A w (packedInterval a (min n (s-a)) C))++leftTail)
    (hright : S.R 172 = Ds.flatMap (fun D => cstream A w (packedInterval 0 (n-min n (s-a)) D))++rightTail)
    (hreplicas : (S.R 179).length = Cs.length)
    (h176 : S.R 176 = []) (h177 : S.R 177 = []) (h178 : S.R 178 = []) :
    let rows := (Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)
    ∃ v' m, v'.user = v.user ∧
      m ≤ cyclicReplicaBoundaryBatchCost Cs.length n (cyclicPrincipalBoundary s t band a n).card w ∧
      Exec body cyclicReplicaBoundaryBatch (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 6
          (cstream A w rows.flatten))}) := by
  dsimp only
  have hzip : (Cs.zip Ds).length = Cs.length := by simp [List.length_zip,hlen]
  have hleftPairs := congrArg
    (fun fields => fields.flatMap (fun C => cstream A w (packedInterval a (min n (s-a)) C)))
    (List.map_fst_zip hlen.le)
  have hrightPairs := congrArg
    (fun fields => fields.flatMap (fun D => cstream A w (packedInterval 0 (n-min n (s-a)) D)))
    (List.map_snd_zip hlen.ge)
  simp only [List.flatMap_map] at hleftPairs hrightPairs
  obtain ⟨vf,m,hu,hm,he⟩ := cyclicReplicaBoundaryBatch_exec (body := body)
    hst hA band a n ha hn (Cs.zip Ds) w leftTail rightTail v S ready
    (by rw [hleftPairs]; exact hleft) (by rw [hrightPairs]; exact hright)
    (by rw [hzip]; exact hreplicas) h176 h177 h178
  exact ⟨vf,m,hu,by simpa only [hzip] using hm,
    by simpa only [cyclicReplicaBoundaryRows_stream] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
