module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireDummyBatches

/-! The physical dummy-prefix retirement leaves the certified supplier stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s C B : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem retireRoutedGather_exec_within
    (realRows capacity replicas blockWidth batchWidth count missing saved tmp src : Fin T)
    (hreg : [realRows,capacity,replicas,blockWidth,batchWidth,count,missing,saved,tmp,src].Nodup)
    (width radius L w : ℕ) (hfit : (coreGatherIndices s width radius L).length ≤ C)
    (Fs : List (ZMod s → GaussianInt)) (rows : Fin C → Fin B → List GaussianInt)
    (hlen : ∀ i j, (rows i j).length = L)
    (hbatches : ∀ i : Fin (coreGatherIndices s width radius L).length,
      (List.ofFn fun j => cstream A w (rows (paddedCoreIndex hfit i) j)).flatten =
        cstream A w (Fs.map (packedInterval
          (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R realRows).length = (coreGatherIndices s width radius L).length)
    (hcapacity : (S.R capacity).length = C) (hreplicas : (S.R replicas).length = B)
    (hwidth : (S.R blockWidth).length = L*w)
    (hbatch : S.R batchWidth = []) (hcount : S.R count = []) (hmissing : S.R missing = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hsrc : S.R src = (List.ofFn fun i => (List.ofFn fun j => cstream A w (rows i j)).flatten).flatten)
    (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ retireDummyBatchesCost (coreGatherIndices s width radius L).length C B (L*w) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        2*retireDummyBatchesCost (coreGatherIndices s width radius L).length C B (L*w)) depth
        (retireDummyBatches realRows capacity replicas blockWidth batchWidth count missing saved tmp src)
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update S.R src
          ((List.ofFn fun i : Fin (coreGatherIndices s width radius L).length =>
            cstream A w (Fs.map (packedInterval
              (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten).flatten))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := retireDummyBatches_exec_within realRows capacity replicas blockWidth batchWidth count missing saved tmp src
    hreg v S hbatch hcount hmissing hsaved htmp depth
  rw [hrows,hcapacity,hreplicas,hwidth] at hn he
  rw [hsrc,routedGatherArchive_drop width radius L w hfit Fs rows hlen hbatches] at he
  exact ⟨v',n,hu,hn,he⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
