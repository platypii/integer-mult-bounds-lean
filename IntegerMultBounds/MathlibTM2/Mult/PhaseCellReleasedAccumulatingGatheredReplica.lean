module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedAccumulatingGatheredReplica
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGatheredNumericalKey

/-! A complete length-class solve, independent publication and numerical-key
retirement. The next class receives the exact released native bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def releasedAccumulatingGatheredReplica (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (generatedAccumulatingGatheredReplica plan dst hR hQ) (retireGatheredNumericalKey plan)

def releasedAccumulatingGatheredReplicaCost (p l N B V span L s t u target rhsExp : ℕ) :=
  generatedAccumulatingGatheredReplicaCost p l N B V span L s t u target rhsExp+
    (32*((N*B)*L*executionWidth p l target rhsExp)+20)

noncomputable def releasedAccumulatingGatheredReplicaWorkspace {Q A : ℕ} {U : Type} (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp : ℕ) :=
  generatedAccumulatingGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp+
    3*(32*((N*B)*L*executionWidth p l target rhsExp)+20)

theorem releasedAccumulatingGatheredReplica_exec_within (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hgd : ∀ i, plan.gather i ≠ dst) (hsd : ∀ i, plan.solver i ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (V origin span : ℕ) (windows : PublicationWindows span L) (Fs : List (ZMod s → GaussianInt))
    (ambientRows : List (List (Fin (A+4))))
    (hne : windows.origins ≠ []) (hspan : origin+span ≤ s)
    (hwV : executionWidth p l target rhsExp < 2^V) (hcoords : span < 2^V)
    (hunits : span*executionWidth p l target rhsExp < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (tail borrowed suffix packedBorrowed outputTail : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock ScalarPlacement.cr
      (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
        ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)) ≤ K) (depth : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let stage := executionStagePrecision p l target rhsExp
    let lo := fun j => ((origin+windows.origins.getD j 0 : ℕ) : ZMod s)
    let C := fun r => Fs.reverse.getD r (fun _ => 0)
    (∀ r < Fs.length, ∀ k, ‖value q (C r k)‖ ≤ (2 : ℝ)^rhsExp) →
    ∀ (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ),
    (∀ r < Fs.length, SchurDominance.Solves (realMatrix s t p u) I (x r)
      (fun k => (value q (C r k)).re)) →
    (∀ j < windows.origins.length, ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo j+(k : ZMod s)) ∧
      lo j+(k : ZMod s) ∈ I) →
    (∀ j < windows.origins.length, ∀ k < L, cell s t (lo j+(k : ZMod s)) = cell s t (lo j)) →
    (∀ j < windows.origins.length, ∀ k ∈ I, cell s t k = cell s t (lo j) → ∃ i < L, lo j+(i : ZMod s) = k) →
    embStk weightCacheCoreReg (embStk plan.solver S) =
      replicaWeightFactoryInputBank A (2^15*p) (stage+1) q l s t u (PhaseCellBand.width p u)
        Fs.length windows.origins.length L w (fun j => (lo j).val) [] borrowed tail inp out →
    (∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = []) →
    (S.R (plan.gather 115)).length = V → (S.R (plan.gather 94)).length = w →
    (S.R (plan.gather 102)).length = L →
    S.R (plan.gather 109) = windows.origins.flatMap (binSyms V)++suffix →
    S.R (plan.gather 116) = List.replicate windows.origins.length tick →
    (S.R (plan.gather 121)).length = Fs.length → (S.R (plan.gather 123)).length = span*w →
    S.R (plan.gather 124) = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++packedBorrowed →
    (∀ k : Fin 126, k.val < 19 → S.R (plan.gather k) = []) →
    (∀ k ∈ [(88 : Fin 126),89,90,91,92,103,104,105,106,107,120,122,125], S.R (plan.gather k) = []) →
    ambientRows.length = Fs.length →
    (∀ row ∈ ambientRows, row.length = span*w) →
    (∀ row ∈ ambientRows, EncodedRange A w q (interiorOutputExponent p l target rhsExp) row) →
    S.R dst = ambientRows.flatten++outputTail →
    ∃ v' F n, ∃ replicas : List (PublicationReplica A),
      replicas.map PublicationReplica.ambient = ambientRows ∧
      replicas.length = Fs.length ∧ (∀ r ∈ replicas, r.Valid windows w 0) ∧
      EncodedRange A w q (interiorOutputExponent p l target rhsExp)
        (replicas.flatMap (PublicationReplica.output windows w)) ∧ v'.user = v.user ∧
      n ≤ releasedAccumulatingGatheredReplicaCost p l Fs.length windows.origins.length V span L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+
        releasedAccumulatingGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l Fs.length
          windows.origins.length V span L s t u target rhsExp) depth
        (releasedAccumulatingGatheredReplica plan dst hR hQ) (mk v S) n (mk v' F) ∧
      embStk plan.gather F = embStk plan.gather S ∧
      F.R dst = replicas.flatMap (PublicationReplica.output windows w)++outputTail ∧
      F.R (plan.solver 93) = tail ∧ F.inp = S.inp ∧ F.out = S.out ∧
      embStk weightCacheCoreReg (embStk plan.solver F) = releasedCellBank [] borrowed tail S.inp S.out ∧
      F.R (plan.solver 117) = S.R (plan.solver 117) ∧
      (∀ k ∈ [(118 : Fin 121),119,120], F.R (plan.solver k) = []) ∧
      (∀ r : Fin Fs.length, ∀ j : Fin windows.origins.length, PhaseCellInterface.ErrorOn (publishedCellCore (lo j) L)
        (fun k => (packedIntervalRead q w origin ((F.R dst).drop (r.val*span*w)) k).re)
        (x r) (1/(2 : ℝ)^target)) ∧
      ∀ r : Fin Fs.length, ∀ (core : Finset (ZMod s)) (old : ZMod s → ℝ) (error : ℝ),
        (∀ k ∈ core, origin ≤ k.val ∧ k.val < origin+span) →
        (∀ k ∈ core, ∀ j : Fin windows.origins.length,
          k.val-origin+1 ≤ windows.origins[j.val]'j.isLt ∨
            (windows.origins[j.val]'j.isLt)+L ≤ k.val-origin) →
        PhaseCellInterface.ErrorOn core
          (fun k => (packedIntervalRead q w origin ((S.R dst).drop (r.val*span*w)) k).re) old error →
        PhaseCellInterface.ErrorOn core
          (fun k => (packedIntervalRead q w origin ((F.R dst).drop (r.val*span*w)) k).re) old error := by
  dsimp only
  intro hC I x hx hint hcell hmax hbank hcacheFresh hV hw hLcount hpackets hcount hreplicas
    hvolume hsource hblank hfresh hNambient hambient hambientRange hdst
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let lo := fun j => ((origin+windows.origins.getD j 0 : ℕ) : ZMod s)
  let C := fun r => Fs.reverse.getD r (fun _ => 0)
  obtain ⟨v₁,F,n₁,replicas,ha,hnrep,hvalid,hrange,hu₁,hn₁,he₁,hgather,hd,hs,hi,ho,hleft,hlow,hrhs,hcache,hclock,h119,h120,herror,hpreserve⟩ :=
    generatedAccumulatingGatheredReplica_exec_within (body := body) plan dst hgd hsd hR hQ hA hp hst hu hαu hθ hgap hbudget
      hL hLs hpad V origin span windows Fs ambientRows hne hspan hwV hcoords hunits
      v S tail borrowed suffix packedBorrowed outputTail inp out R K hpushR hpushK depth
      hC I x hx hint hcell hmax hbank hcacheFresh hV hw hLcount hpackets hcount hreplicas hvolume hsource
      hblank hfresh hNambient hambient hambientRange hdst
  let volume := (Fs.length*windows.origins.length)*L*w
  let rhs := cstream A w ((List.range Fs.length).flatMap (fun r =>
    (List.range windows.origins.length).flatMap (cellSourceRows L lo (fun _ => C r))))
  have hrhsLen : rhs.length = volume := by
    simp only [rhs,length_cstream,List.length_flatMap,cellSourceRows_length,List.map_const',
      List.length_range,List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
    dsimp only [volume]
    ring
  let page := batchWeightPage A w q (2^15*p) s t u (Fs.length*windows.origins.length) L
    (fun n => (lo (n%windows.origins.length)).val)
  have hpageLen : page.length = 2*volume := by simp [page,volume,Nat.mul_assoc]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retireGatheredNumericalKey_exec_within (body := body) plan volume
    rhs borrowed page (S.R (plan.solver 117)) hrhsLen hpageLen v₁ F hrhs hcache
    (by rw [hclock,List.length_replicate]; dsimp only [volume]; ring)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact hlow 116 (by decide) (by decide)
      · exact h119
      · exact h120) depth
  let G := retiredGatheredNumericalKeyBank plan F borrowed (S.R (plan.solver 117))
  have hOut : G.R dst = F.R dst := by
    simp [G,retiredGatheredNumericalKeyBank,(hsd 110).symm,(hsd 117).symm,(hsd 118).symm]
  have hsolver : embStk plan.solver G = retiredReplicaNumericalKeyBank (embStk plan.solver F) borrowed (S.R (plan.solver 117)) :=
    retiredGatheredNumericalKeyBank_solver plan F borrowed _
  have hlowBank : embStk weightCacheCoreReg (embStk plan.solver G) =
      releasedCellBank [] borrowed tail S.inp S.out := by
    rw [hsolver,retiredReplicaNumericalKeyBank_low _ _ _ hleft hlow]
    change releasedCellBank [] borrowed (F.R (plan.solver 93)) F.inp F.out = _
    rw [hs,hi,ho]
  have hGg : embStk plan.gather G = embStk plan.gather S := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hi
    · exact ho
    · have hh := congrArg (fun B : Stacks 126 A => B.L) hgather
      simpa only [G,retiredGatheredNumericalKeyBank,embStk] using hh
    · funext k
      simpa [G,retiredGatheredNumericalKeyBank,embStk,plan.disjoint k 110,plan.disjoint k 117,plan.disjoint k 118]
        using congrFun (congrArg Stacks.R hgather) k
  refine ⟨v₂,G,n₁+n₂,replicas,ha,hnrep,hvalid,hrange,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_,
    hGg,hOut.trans hd,?_,hi,ho,hlowBank,?_,?_,?_,?_⟩
  · simpa only [releasedAccumulatingGatheredReplica,releasedAccumulatingGatheredReplicaWorkspace,volume,w] using mn_seq_within_add he₁ he₂
  · simpa [G,retiredGatheredNumericalKeyBank,plan.solver_injective.eq_iff] using hs
  · simp [G,retiredGatheredNumericalKeyBank,plan.solver_injective.eq_iff]
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    · simp [G,retiredGatheredNumericalKeyBank]
    · simpa [G,retiredGatheredNumericalKeyBank,plan.solver_injective.eq_iff] using h119
    · simpa [G,retiredGatheredNumericalKeyBank,plan.solver_injective.eq_iff] using h120
  · simpa only [hOut] using herror
  · simpa only [hOut] using hpreserve

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
