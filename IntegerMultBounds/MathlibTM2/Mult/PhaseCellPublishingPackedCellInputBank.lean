module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishingPackedCellInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellInputBank

/-! The generated gather/publication path presents the unchanged native
arithmetic bank, with the publication schedule outside that bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

theorem publishingPackedCellInputBank_exec {precision stage q l s t u band origin N L V : ℕ}
    (C : ZMod s → GaussianInt) (hhalo : origin+N ≤ s) (hL : 0 < L)
    (offsets : List ℕ) (hne : offsets ≠ []) (hdis : offsets.Pairwise (fun i j => i+L ≤ j))
    (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (hVeq : V = weightWorkspaceWidth precision q (2*q+8) t u)
    (hwV : 2*q+8 < 2^V) (hcoords : origin+N < 2^V) (hunits : (origin+N)*(2*q+8) < 2^V)
    (tail outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hbank : embStk packedCellCoreReg S = batchInputBank precision stage q l s t u band L offsets.length
      (fun i => (packedCellOrigin (s := s) origin offsets i).val) []
      (cstream A (2*q+8) (packedInterval origin N C)++tail) outTail inp out)
    (hprotected : ∀ k ∈ [(131 : Fin 168),134,135], S.R k = [])
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hV : (S.R 163).length = V)
    (h153 : S.R 153 = []) (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0) :
    let rhs := cstream A (2*q+8) ((List.range offsets.length).flatMap
      (cellSourceRows L (packedCellOrigin (s := s) origin offsets) (fun _ => C)))
    ∃ v' m, v'.user = v.user ∧ m ≤ packedCellGroupInputCost V N L (2*q+8) offsets.length q+
      (12*N*(2*q+8)+21*offsets.length+6*L*(2*q+8)+9*L+27) ∧
      Exec body rawPublishingPackedCellInputs (mk v S) m
        (mk v' {S with R := Function.update (Function.update S.R 140
        (gatherControls A (packedCellGaps L (2*q+8) offsets)++S.R 140)) 110 (rhs++S.R 110)}) ∧
      embStk packedCellCoreReg {S with R := Function.update (Function.update S.R 140
        (gatherControls A (packedCellGaps L (2*q+8) offsets)++S.R 140)) 110 (rhs++S.R 110)} =
        batchInputBank precision stage q l s t u band L offsets.length
          (fun i => (packedCellOrigin (s := s) origin offsets i).val) rhs
          (cstream A (2*q+8) (packedInterval origin N C)++tail) outTail inp out := by
  dsimp only
  let bank := batchInputBank precision stage q l s t u band L offsets.length
    (fun i => (packedCellOrigin (s := s) origin offsets i).val) []
    (cstream A (2*q+8) (packedInterval origin N C)++tail) outTail inp out
  have hR (k : Fin 117) : S.R (packedCellCoreReg k) = bank.R k :=
    congrArg (fun B : Stacks 117 A => B.R k) hbank
  have hsmall : ∀ k : Fin 168, k.val < 19 → S.R k = [] := by
    intro k hk
    let j : Fin 117 := ⟨k.val,by omega⟩
    have hh := hR j
    change S.R k = _ at hh
    exact hh.trans (batchInputBank_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j (by dsimp [j]; omega))
  have hfresh : ∀ k ∈ [(88 : Fin 168),89,90,91,92,104,105,108], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 88
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 89
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 90
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 91
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 92
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 104
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 105
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 108
  have hpublication : ∀ k ∈ [(88 : Fin 168),89,90,92,95,104,106,131,134,135], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 88
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 89
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 90
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 92
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 95
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 104
    | simpa [bank,batchInputBank,packedCellCoreReg] using hR 106
    | exact hprotected 131 (by simp)
    | exact hprotected 134 (by simp)
    | exact hprotected 135 (by simp)
  have hpackets : S.R 109 = (offsets.map (origin+·)).flatMap (binSyms V)++List.replicate l tick := by
    simpa [bank,batchInputBank,packedCellCoreReg,← hVeq,packedCellOrigin_packets V offsets hhalo hL hfit] using hR 109
  obtain ⟨v',m,hu,hm,he⟩ := rawPublishingPackedCellInputs_exec (body := body)
    C hhalo (by omega) offsets hne hdis hfit tail v S h165 h166
    (by simpa [bank,batchInputBank,packedCellCoreReg] using congrArg List.length (hR 112))
    (by simpa [bank,batchInputBank,packedCellCoreReg] using hR 94) rfl
    (by simpa [bank,batchInputBank,packedCellCoreReg] using congrArg List.length (hR 102))
    (by simpa [bank,batchInputBank,packedCellCoreReg] using hR 110)
    hwV hcoords hunits (List.replicate l tick)
    (by simpa [bank,batchInputBank,packedCellCoreReg] using hR 116)
    hpackets hV h153 h155 h154 hsmall hpublication hfresh
  have hrows : offsets.flatMap (fun j => cstream A (2*q+8) (packedInterval (origin+j) L C)) =
      cstream A (2*q+8) ((List.range offsets.length).flatMap
        (cellSourceRows L (packedCellOrigin (s := s) origin offsets) (fun _ => C))) := by
    rw [← packedCellRows_eq_sourceRows C offsets hhalo hfit]
    simp only [cstream,List.flatMap_assoc]
  refine ⟨v',m,hu,by dsimp [packedCellGroupInputCost]; omega,by simpa only [hrows] using he,?_⟩
  have hproj : embStk packedCellCoreReg {S with R := (Function.update (Function.update S.R 140
        (gatherControls A (packedCellGaps L (2*q+8) offsets)++S.R 140)) 110
      (cstream A (2*q+8) ((List.range offsets.length).flatMap
        (cellSourceRows L (packedCellOrigin (s := s) origin offsets) (fun _ => C)))++S.R 110))} =
      {embStk packedCellCoreReg S with R := (Function.update (embStk packedCellCoreReg S).R 110
        (cstream A (2*q+8) ((List.range offsets.length).flatMap
          (cellSourceRows L (packedCellOrigin (s := s) origin offsets) (fun _ => C)))++S.R 110))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hk : k.val ≠ 140 := by omega
    simp [embStk,packedCellCoreReg,Function.update_apply,Fin.ext_iff,hk]
  rw [hproj,hbank]
  have hs : S.R 110 = cstream A (2*q+8) (packedInterval origin N C)++tail := by
    simpa [bank,batchInputBank,packedCellCoreReg] using hR 110
  rw [hs]
  exact batchInputBank_prepend_rhs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
