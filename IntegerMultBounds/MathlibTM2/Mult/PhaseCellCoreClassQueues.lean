module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreJobQueues
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreClassJobs

/-! The derived movement-class jobs match the generated queues and shared counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {A p u l targetOut s t width L : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

theorem coreClassJobs_queues (hp : 2 ≤ p) (hpacket : 8*p ≤ 2^u) (hα : 0 < α)
    (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1))
    (hbudget : α^2*gap ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hC : ∀ a b, a ≤ b → b ≤ s → a < s →
      ∀ j, ‖value (packedHaloPrecision p l s t u (targetOut+1) 2 a b) (C j)‖ ≤ (2 : ℝ)^2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hwidth : 0 < width) (hsep : L+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    let jobs := coreClassJobs (A := A) hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF
    let radius := localityDepth p targetOut*PhaseCellBand.width p u
    let w := packedHaloCommonWidth p l s u (targetOut+1) 2
    let V := inverseCallerWordWidth p u l targetOut s t
    (List.ofFn jobs).flatMap (fun r => binSyms (A := A) V r.a) =
      (coreGatherIndices s width radius L).flatMap (fun k => binSyms V (coreStart width k-radius)) ∧
    (List.ofFn jobs).flatMap PackedNormalizedJob.inputPayload =
      (List.ofFn fun i : Fin (coreGatherIndices s width radius L).length =>
        (List.ofFn fun j => cstream A w (coreGatherRows width radius L Fs i j)).flatten).flatten ∧
    ∀ i, (jobs i).inputPayload.length = Fs.length*L*w ∧
      coreLength s (jobs i).coreWidth (jobs i).k = L-2*radius ∧
      (jobs i).b-(jobs i).a = L ∧ (jobs i).a < 2^V := by
  dsimp only
  let jobs := coreClassJobs (A := A) hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF
  let radius := localityDepth p targetOut*PhaseCellBand.width p u
  let w := packedHaloCommonWidth p l s u (targetOut+1) 2
  have hf := coreClassJobs_fields (A := A) hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF
  have hw : ∀ i, (jobs i).coreWidth = width := fun i => (hf i).1
  have hk : ∀ i, (jobs i).k = (coreGatherIndices s width radius L)[i.val] := fun i => (hf i).2.1
  have hr : ∀ i, (jobs i).radius = radius := fun i => (hf i).2.2.1
  have hword : ∀ i, (jobs i).W = w := fun i => (hf i).2.2.2.1
  have hFs : ∀ i, (jobs i).Fs = Fs := fun i => (hf i).2.2.2.2
  refine ⟨coreJobs_origins width radius L _ jobs hw hr hk,
    coreJobs_payloads width radius L w Fs jobs hw hr hk hword hFs,?_⟩
  intro i
  refine ⟨coreJobs_payload_length width radius L w Fs jobs hw hr hk hword hFs i,
    coreJobs_core_length width radius L jobs hw hk i,?_,?_⟩
  · have hlen := (coreGatherIndices_spec s width radius L _ (List.getElem_mem i.isLt)).2.2
    have hhalo := (jobs i).haloLength
    rw [hw,hr,hk] at hhalo
    exact hhalo.trans hlen
  · change (jobs i).a < 2^(jobs i).Bcore
    simpa using (jobs i).hvaluesFit 6

theorem coreClassJobs_runtime_facts (hp : 2 ≤ p) (hpacket : 8*p ≤ 2^u) (hα : 0 < α)
    (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1))
    (hbudget : α^2*gap ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hC : ∀ a b, a ≤ b → b ≤ s → a < s →
      ∀ j, ‖value (packedHaloPrecision p l s t u (targetOut+1) 2 a b) (C j)‖ ≤ (2 : ℝ)^2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hwidth : 0 < width) (hsep : L+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1)
    [NeZero t] (hp4 : 4 ≤ p) (htarget : p+2 ≤ targetOut)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t α = 1) :
    let jobs := coreClassJobs (A := A) hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF
    let radius := localityDepth p targetOut*PhaseCellBand.width p u
    let V := inverseCallerWordWidth p u l targetOut s t
    ∀ r ∈ List.ofFn jobs, r.t = t ∧ 4 ≤ r.p ∧ r.p+2 ≤ r.targetOut ∧ r.localityTarget = r.targetOut ∧
      J ∘L PhaseCellOperator.exact s t r.α = 1 ∧ r.Fs.length = Fs.length ∧
      coreLength s r.coreWidth r.k = L-2*radius ∧ r.a < 2^V := by
  dsimp only
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  have hqueues := coreClassJobs_queues (A := A) hp hpacket hα hst hu hαu hθ hgap hbudget hband
    hpad hC hdom hwidth hsep Fs hF
  exact ⟨rfl,hp4,htarget,rfl,hJ,rfl,(hqueues.2.2 i).2.1,(hqueues.2.2 i).2.2.2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
