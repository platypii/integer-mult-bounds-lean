module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaConsumerInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualExportStock
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! The actual cached archives feed the existing row exporter. All retained
masters are installed once; export retires its packed controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 834 Q A U}

def cyclicReplicaConsumerExport : Pr P 834 Q A U :=
  .seq cyclicReplicaConsumerHandoff (embProg factorReg Empty.elim (exportCyclicResidualRows (P := Empty)))

def cyclicReplicaConsumerExportState (S : Stacks 834 A) (rows : List (Fin (A+4))) : Stacks 834 A :=
  embOvr factorReg
    (exportedCyclicResidualRows (embStk factorReg (cyclicReplicaConsumerState S)) rows).get
    (cyclicReplicaConsumerState S)

theorem cyclicReplicaConsumerExportState_factor (S : Stacks 834 A)
    (rows : List (Fin (A+4))) :
    embStk factorReg (cyclicReplicaConsumerExportState S rows) =
      exportedCyclicResidualRows (embStk factorReg (cyclicReplicaConsumerState S)) rows :=
  embStk_ovr factorReg_injective _ _

theorem cyclicReplicaConsumerExportState_pass_frame (S : Stacks 834 A)
    (rows : List (Fin (A+4))) (k : Fin 834) (hk : left.Owns k ∨ right.Owns k) :
    (cyclicReplicaConsumerExportState S rows).L k = (cyclicReplicaConsumerState S).L k ∧
    (cyclicReplicaConsumerExportState S rows).R k = (cyclicReplicaConsumerState S).R k := by
  apply embOvr_off
  intro j he
  rcases hk with hk | hk
  · exact (factor_disjoint j).1 (he.symm ▸ hk)
  · exact (factor_disjoint j).2 (he.symm ▸ hk)

theorem CyclicReplicaConsumerPost.afterExport {s : ℕ} [NeZero s]
    (H K : ReplicaHaloProblem s) (leftBuffers rightBuffers : ReplicaLoopBuffers A)
    (S : Stacks 834 A) (Cs Ds : List (ZMod s → GaussianInt))
    (post : CyclicReplicaConsumerPost H K leftBuffers rightBuffers S
      (cyclicReplicaConsumerState S) Cs Ds) (rows : List (Fin (A+4))) :
    embStk left.coupling.bank (cyclicReplicaConsumerExportState S rows) = embStk left.coupling.bank S ∧
    embStk right.coupling.bank (cyclicReplicaConsumerExportState S rows) = embStk right.coupling.bank S ∧
    ReplicaRecoveryRhsHeaders H left.plan.gather leftBuffers (cyclicReplicaConsumerExportState S rows) ∧
    ReplicaRecoveryRhsHeaders K right.plan.gather rightBuffers (cyclicReplicaConsumerExportState S rows) ∧
    (cyclicReplicaConsumerExportState S rows).R (factorReg 229) = List.replicate H.Fs.length tick := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine Eq.trans ?_ post.leftBank
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i; exact (cyclicReplicaConsumerExportState_pass_frame S rows _ (Or.inl (.bank i))).1
    · funext i; exact (cyclicReplicaConsumerExportState_pass_frame S rows _ (Or.inl (.bank i))).2
  · refine Eq.trans ?_ post.rightBank
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i; exact (cyclicReplicaConsumerExportState_pass_frame S rows _ (Or.inr (.bank i))).1
    · funext i; exact (cyclicReplicaConsumerExportState_pass_frame S rows _ (Or.inr (.bank i))).2
  · exact ReplicaRecoveryRhsHeaders.of_frame H left.plan.gather leftBuffers _ _ post.leftRhs
      (fun i => (cyclicReplicaConsumerExportState_pass_frame S rows _ (Or.inl (.gather i))).2)
  · exact ReplicaRecoveryRhsHeaders.of_frame K right.plan.gather rightBuffers _ _ post.rightRhs
      (fun i => (cyclicReplicaConsumerExportState_pass_frame S rows _ (Or.inr (.gather i))).2)
  · have hh := congrArg (fun F : Stacks 234 A => F.R 229) (cyclicReplicaConsumerExportState_factor S rows)
    have hread : (cyclicReplicaConsumerExportState S rows).R (factorReg 229) =
        (cyclicReplicaConsumerState S).R (factorReg 229) := by
      simpa [embStk,exportedCyclicResidualRows,cyclicResidualRowsRetired] using hh
    exact hread.trans post.replicas

def cyclicReplicaConsumerExportWorkspace {s : ℕ} (H K : ReplicaHaloProblem s) (n N : ℕ) : ℕ :=
  2*(4*(H.Fs.length+H.wordWidth+H.span*H.wordWidth+K.span*K.wordWidth)+17)+
    cyclicResidualExportPush (Q := Q) (A := A) (U := U)*
      exportCyclicResidualRowsCost H.Fs.length n N H.wordWidth

theorem cyclicReplicaConsumerExport_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (H K : ReplicaHaloProblem s)
    (leftBuffers rightBuffers : ReplicaLoopBuffers A) (S₀ S₁ : Stacks 834 A)
    (Cs Ds : List (ZMod s → GaussianInt)) (v : HS 834 Q A U) (S : Stacks 834 A)
    (hl : CachedReplicaPassPost H left leftBuffers S₀ S Cs)
    (hr : CachedReplicaPassPost K right rightBuffers S₁ S Ds)
    (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (hspanL : H.span = min n (s-a)) (hspanR : K.span = n-min n (s-a))
    (horiginL : H.origin = a) (horiginR : K.origin = 0)
    (hw : K.wordWidth = H.wordWidth) (hFs : K.Fs.length = H.Fs.length)
    (hblank : ∀ k ∈ [(130 : Fin 234),168,169,171,172,174,175,229], S.R (factorReg k) = [])
    (hleft : S.R (factorReg 170) = couplingSourceIntervalMaskSymbols true A s t band
      a (a+min n (s-a)) a (min n (s-a)))
    (hright : S.R (factorReg 173) = couplingSourceIntervalMaskSymbols true A s t band
      0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hcount : (S.R (factorReg 116)).length = (cyclicPrincipalBoundary s t band a n).card)
    (hwork : ∀ r : Fin 180, r.val < 80 → S.R (factorReg (cyclicResidualRowsReg r)) = [])
    (hfresh : ∀ r ∈ [(134 : Fin 180),135,136,137,143,174,175,176,177,178],
      S.R (factorReg (cyclicResidualRowsReg r)) = []) :
    let rows := (Cs.zip Ds).flatMap (fun z =>
      cstream A H.wordWidth (cyclicReplicaBoundaryRow t band a n z.1 z.2))
    ∃ vf m, vf.user = v.user ∧
      m ≤ ((4*(H.Fs.length+H.wordWidth+H.span*H.wordWidth+K.span*K.wordWidth)+17)+
        (4*(H.Fs.length*(H.span*H.wordWidth)+K.Fs.length*(K.span*K.wordWidth))+8))+
        exportCyclicResidualRowsCost H.Fs.length n
          (cyclicPrincipalBoundary s t band a n).card H.wordWidth ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        cyclicReplicaConsumerExportWorkspace (Q := Q) (A := A) (U := U) H K n
          (cyclicPrincipalBoundary s t band a n).card) 0 cyclicReplicaConsumerExport (mk v S) m
        (mk vf (cyclicReplicaConsumerExportState S rows)) ∧
      embStk left.coupling.bank (cyclicReplicaConsumerExportState S rows) = embStk left.coupling.bank S ∧
      embStk right.coupling.bank (cyclicReplicaConsumerExportState S rows) = embStk right.coupling.bank S ∧
      ReplicaRecoveryRhsHeaders H left.plan.gather leftBuffers (cyclicReplicaConsumerExportState S rows) ∧
      ReplicaRecoveryRhsHeaders K right.plan.gather rightBuffers (cyclicReplicaConsumerExportState S rows) ∧
    (cyclicReplicaConsumerExportState S rows).R (factorReg 229) = List.replicate H.Fs.length tick := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,post⟩ := cyclicReplicaConsumerHandoff_exec
    (body := body) H K leftBuffers rightBuffers S₀ S₁ Cs Ds v S hl hr hblank
  let F := cyclicReplicaConsumerState S
  have inputs := post.exportInputs H K leftBuffers rightBuffers S Cs Ds
    t band a n hspanL hspanR hw hleft hright hcount
    (fun r _ hr80 => hwork r hr80) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hfresh _ (by simp))
  have hlen : Cs.length = Ds.length := by rw [hl.length,hr.length,hFs]
  have hzip : (Cs.zip Ds).length = H.Fs.length := by simp [hlen,← hl.length]
  have hleftPairs := congrArg
    (fun fields => fields.flatMap (fun C => cstream A H.wordWidth (packedInterval a (min n (s-a)) C)))
    (List.map_fst_zip (by omega : Cs.length ≤ Ds.length))
  have hrightPairs := congrArg
    (fun fields => fields.flatMap (fun D => cstream A H.wordWidth (packedInterval 0 (n-min n (s-a)) D)))
    (List.map_snd_zip (by omega : Ds.length ≤ Cs.length))
  simp only [List.flatMap_map] at hleftPairs hrightPairs
  have hleftArchive : (embStk factorReg F).R 169 = (Cs.zip Ds).flatMap
      (fun z => cstream A H.wordWidth (packedInterval a (min n (s-a)) z.1)) := by
    rw [hleftPairs]
    simpa only [embStk,Function.comp_apply,horiginL,hspanL] using post.leftArchive
  have hrightArchive : (embStk factorReg F).R 172 = (Cs.zip Ds).flatMap
      (fun z => cstream A H.wordWidth (packedInterval 0 (n-min n (s-a)) z.2)) := by
    rw [hrightPairs]
    simpa only [embStk,Function.comp_apply,horiginR,hspanR,hw] using post.rightArchive
  have hreplicas : ((embStk factorReg F).R 229).length = (Cs.zip Ds).length := by
    change (F.R (factorReg 229)).length = _
    rw [show F.R (factorReg 229) = List.replicate H.Fs.length tick from post.replicas,
      List.length_replicate,hzip]
  have read (j : Fin 234) (hj : j ∉ [(130 : Fin 234),168,169,171,172,229]) :
      (embStk factorReg F).R j = S.R (factorReg j) :=
    cyclicReplicaConsumerState_factor_read S j hj
  obtain ⟨vi,m₂,hui,hm₂,hei⟩ := exportCyclicResidualRows_exec
    (body := fun z : Empty => nomatch z) hst hA band a n ha hn (Cs.zip Ds) H.wordWidth
    (embDn factorReg v₁) (embStk factorReg F) inputs
    (by intro r hr6
        have hoff : cyclicResidualRowsReg r ∉ [(130 : Fin 234),168,169,171,172,229] := by
          have hr179 : r ≠ 179 := by intro he; have hv := congrArg Fin.val he; simp at hv; omega
          have hr6' : r ≠ 6 := by intro he; have hv := congrArg Fin.val he; simp at hv; omega
          have hval : (cyclicResidualRowsReg r).val < 6 := by
            simpa [cyclicResidualRowsReg,hr6',hr179] using hr6
          intro hm
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
          rcases hm with he | he | he | he | he | he
          all_goals rw [he] at hval; norm_num at hval
        rw [read _ hoff]
        exact hwork r (by omega))
    hleftArchive hrightArchive hreplicas
    (by rw [read 176 (by decide)]; simpa [cyclicResidualRowsReg] using hfresh 176 (by simp))
    (by rw [read 177 (by decide)]; simpa [cyclicResidualRowsReg] using hfresh 177 (by simp))
    (by rw [read 178 (by decide)]; simpa [cyclicResidualRowsReg] using hfresh 178 (by simp))
  have hmExport : m₂ ≤ exportCyclicResidualRowsCost H.Fs.length n
      (cyclicPrincipalBoundary s t band a n).card H.wordWidth := by
    simpa only [hzip] using hm₂
  have heExport := exportCyclicResidualRows_exec_within_of_exec hei hmExport 0
  obtain ⟨vf,_,hu₂,he₂⟩ := exec_emb_ovr_within_stock factorReg (body' := body) (ι := Empty.elim)
    factorReg_injective (fun z => nomatch z) heExport v₁ rfl F rfl
  refine ⟨vf,_,hu₂.trans (hui.trans hu₁),?_,execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ he₁ he₂,
    post.afterExport H K leftBuffers rightBuffers S Cs Ds _⟩
  exact Nat.add_le_add hm₁ (by simpa only [hzip] using hm₂)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
