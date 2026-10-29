module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishingPackedCellBatchPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparePackedCellDestination
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedBounds

/-! Generate the local destination and retained dimensions before the executed
interior gather–solve–publish chain. No destination payload or schedule is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

noncomputable def generatedPackedCellBatchPublish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 168 Q A U :=
  .seq preparePackedCellDestination (publishingPackedCellBatchPublish hR hQ)

theorem generatedPackedCellBatchPublish_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp origin N V : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (offsets : List ℕ) (hne : offsets ≠ []) (hdis : offsets.Pairwise (fun i j => i+L ≤ j))
    (hhalo : origin+N ≤ s) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : origin+N < 2^V) (hunits : (origin+N)*executionWidth p l target rhsExp < 2^V)
    (tail outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hbank : embStk packedCellCoreReg S = batchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L offsets.length
      (fun i => (packedCellOrigin (s := s) origin offsets i).val) []
      (cstream A (executionWidth p l target rhsExp) (packedInterval origin N C)++tail) outTail inp out)
    (hpublication : ∀ k ∈ [(128 : Fin 168),130,131,134,135,140], S.R k = [])
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hV : (S.R 163).length = V)
    (h153 : S.R 153 = []) (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let lo := packedCellOrigin (s := s) origin offsets
    let words := scatterRows L (packedInterval origin N C)
      (publishedWords offsets.length L
        (executedOutputWords s t p u q l offsets.length L j cExp lo (fun _ => C)))
      (windowGaps L 0 offsets)
    let D := packedField (s := s) origin words
    ∃ v' F m, v'.user = v.user ∧
      m ≤ (16*N*w+17*N+11*V+8*q+4*L+37)+(packedCellGroupInputCost V N L w offsets.length q+
        (12*N*w+21*offsets.length+6*L*w+9*L+27)+
        sizedClosedBatchCost p l offsets.length L s t u target rhsExp+(54*N*w+15)) ∧
      Exec body (generatedPackedCellBatchPublish hR hQ) (mk v S) m (mk v' F) ∧
      F.R 93 = outTail ∧ F.R 140 = [] ∧
      F.R 132 = cstream A w (packedInterval origin N D)++S.R 132 ∧
      (∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp) ∧
      (∀ k, Fits w (D k)) ∧
      embStk packedCellCoreReg F = releasedCellBank
        (cstream A w ((List.range offsets.length).flatMap (cellSourceRows L lo (fun _ => C))))
        (cstream A w (packedInterval origin N C)++tail) outTail inp out ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 130 → k ≠ 132 →
        F.L k = S.L k ∧ F.R k = S.R k) ∧
      F.R 128 = List.replicate L tick ∧ F.R 130 = List.replicate w tick ∧
      PackedCellOutputSpec t p u l target rhsExp L offsets lo (fun _ => C) (F.R 132) ∧
      ∀ n : Fin offsets.length,
        (executedRun s t p u q l w offsets.length L j cExp lo (fun _ => C) n outTail).Valid
          s t p u (lo n) L (fun k => (value q (C k)).re)
          (1/(2 : ℝ)^j) ((2 : ℝ)^inputExponent p cExp) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let E := cstream A w (packedInterval origin N C)
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hRnative (k : Fin 117) := congrArg (fun B : Stacks 117 A => B.R k) hbank
  have hclean : ∀ k ∈ [(0 : Fin 168),1,2,104,105,108,128,130,166], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hRnative 0
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hRnative 1
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hRnative 2
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hRnative 104
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hRnative 105
    | simpa [embStk,packedCellCoreReg,batchInputBank] using hRnative 108
    | exact hpublication 128 (by simp)
    | exact hpublication 130 (by simp)
    | exact h166
  have hE : E.length = N*w := by simp [E,packedInterval_length C hhalo]
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := preparePackedCellDestination_exec (body := body)
    V N L q (by omega) E tail (by simpa only [← hw] using hE) v S
    (by simpa [embStk,packedCellCoreReg,batchInputBank,q] using congrArg List.length (hRnative 112))
    (by simpa [embStk,packedCellCoreReg,batchInputBank] using congrArg List.length (hRnative 102))
    h165 (by simpa [embStk,packedCellCoreReg,batchInputBank,E,w] using hRnative 110) hclean
  let G : Stacks 168 A := {S with R := (Function.update (Function.update (Function.update S.R
    130 (List.replicate w tick)) 128 (List.replicate L tick)) 132 (E++S.R 132))}
  have he₁' : Exec body preparePackedCellDestination (mk v S) m₁ (mk v₁ G) := by
    simpa only [← hw] using he₁
  have hbankG : embStk packedCellCoreReg G = embStk packedCellCoreReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have h128 : k.val ≠ 128 := by omega
    have h130 : k.val ≠ 130 := by omega
    have h132 : k.val ≠ 132 := by omega
    simp [embStk,packedCellCoreReg,G,Fin.ext_iff,h128,h130,h132]
  have hprotectedG : ∀ k ∈ [(131 : Fin 168),134,135], G.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl
    · simpa [G] using hpublication 131 (by simp)
    · simpa [G] using hpublication 134 (by simp)
    · simpa [G] using hpublication 135 (by simp)
  obtain ⟨v₂,F,m₂,hu₂,hm₂,he₂,h93,h140,houtput,hproj,hframe,hacc,hvalid,_hleftAll⟩ := publishingPackedCellBatchPublish_sized_exec
    (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad C hC offsets hne hdis
    hhalo hfit hVeq hwV hcoords hunits tail outTail inp out v₁ G (hbankG.trans hbank)
    E (S.R 132) hE (by simp [G]) (by simp [G,w]) (by simp [G])
    (by simpa [G] using hpublication 140 (by simp)) hprotectedG
    (by simpa [G] using h165) (by simpa [G] using h166) (by simpa [G] using hV)
    (by simpa [G] using h153) (by simpa [G] using h155) (by simpa [G] using h154)
  have hframeF : ∀ k : Fin 168, 117 ≤ k.val → k ≠ 128 → k ≠ 130 → k ≠ 132 →
      F.L k = S.L k ∧ F.R k = S.R k := by
    intro k hk hn128 hn130 hn132
    have hh := hframe k hk hn132
    simpa [G,hn128,hn130,hn132] using hh
  have h128 : F.R 128 = List.replicate L tick := by
    simpa [G] using (hframe 128 (by decide) (by decide)).2
  have h130 : F.R 130 = List.replicate w tick := by
    simpa [G] using (hframe 130 (by decide) (by decide)).2
  let lo := packedCellOrigin (s := s) origin offsets
  let pub := publishedWords offsets.length L
    (executedOutputWords s t p u q l offsets.length L
      (executionStagePrecision p l target rhsExp) (sourceExponent l target rhsExp) lo (fun _ => C))
  let words := scatterRows L (packedInterval origin N C) pub (windowGaps L 0 offsets)
  let D := packedField (s := s) origin words
  have hpub : pub.length = offsets.length*L := by
    simp [pub,publishedWords_length,executedOutputWords_length]
  have hfits : ScatterFits L (packedInterval origin N C) (windowGaps L 0 offsets) := by
    simpa only [List.drop_zero] using windowGaps_fits L 0 offsets (packedInterval origin N C)
      (fun _ _ => Nat.zero_le _) hdis (fun j hj => by rw [packedInterval_length C hhalo]; exact hfit j hj)
  have hwordslen : words.length = N := by
    dsimp only [words]
    rw [length_scatterRows _ _ _ _ hfits (by simp [hpub]),packedInterval_length C hhalo]
  have hpubnorm : ∀ z ∈ pub, ‖value q z‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp :=
    publishedOutputWords_norm hp hst hu hL hαu hθ hgap hbudget hpad lo (fun _ => C) (fun _ _ k => hC k)
  have hwordsnorm : ∀ z ∈ words, ‖value q z‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp := by
    intro z hz
    rcases scatterRows_mem L (packedInterval origin N C) pub (windowGaps L 0 offsets) z hz with hz | hz
    · have hz' : z ∈ chirpLine s C := List.mem_of_mem_drop (List.mem_of_mem_take hz)
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hz'
      exact (hC (k : ZMod s)).trans (pow_le_pow_right₀ (by norm_num)
        (rhsExponent_le_interiorOutputExponent p l target rhsExp))
    · exact hpubnorm z hz
  have hzero : value q (0 : GaussianInt) = (0 : ℂ) := by apply Complex.ext <;> simp [value]
  have hDnorm : ∀ k, ‖value q (D k)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp := by
    intro k
    exact packedField_property words _ (by rw [hzero]; simp) hwordsnorm k
  have hDfits : ∀ k, Fits w (D k) := fun k =>
    fits_of_value_power (interiorOutput_width p l target rhsExp) (D k) (hDnorm k)
  have hDpacked : packedInterval origin N D = words := by
    simpa only [hwordslen] using packedInterval_packedField (s := s) words
      (by rw [hwordslen]; exact hhalo)
  have houtputD : F.R 132 = cstream A w (packedInterval origin N D)++S.R 132 := by
    rw [hDpacked]
    simpa only [E,w,words,pub,q,lo,packedCellScatter_cstream] using houtput
  exact ⟨v₂,F,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add (by simpa only [← hw] using hm₁) hm₂,
    Exec.seq he₁' he₂,h93,h140,houtputD,hDnorm,hDfits,hproj,hframeF,h128,h130,hacc,hvalid⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
