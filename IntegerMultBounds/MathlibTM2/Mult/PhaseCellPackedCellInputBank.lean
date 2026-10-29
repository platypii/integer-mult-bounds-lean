module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawPackedCellInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInputBank
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! The local gather produces the unchanged closed arithmetic batch's native
input bank. Only the physical storage of the borrowed RHS is local. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def packedCellCoreReg (i : Fin 117) : Fin 168 := ⟨i.val,by omega⟩

theorem packedCellCoreReg_injective : Function.Injective packedCellCoreReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 168 => k.val) he)

/-- Combine the restored native left bank with the retained high-bank frame. -/
theorem packedCell_left_eq {A : ℕ} (S F : Stacks 168 A)
    (hlow : ∀ i : Fin 117, F.L (packedCellCoreReg i) = S.L (packedCellCoreReg i))
    (hhigh : ∀ k : Fin 168, 117 ≤ k.val → F.L k = S.L k) : F.L = S.L := by
  funext k
  by_cases hk : k.val < 117
  · exact hlow ⟨k.val,hk⟩
  · exact hhigh k (by omega)

def packedCellGroupInputCost (V N L w K q : ℕ) : ℕ :=
  8*q+2*w+11+(w*(4*V+10)+6*V+10+(K*(3*tblC V V+29*V+30)+8*N*w+78*V+91+
    (K*(14*L*w+27)+32*N*w+17*N+11*V+6*L*w+9*L+60)))

theorem batchInputBank_prepend_rhs (precision stage q l s t u band L B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    {batchInputBank precision stage q l s t u band L B lo [] borrowed outTail inp out with
      R := Function.update (batchInputBank precision stage q l s t u band L B lo [] borrowed outTail inp out).R
        110 (rhs++borrowed)} =
      batchInputBank precision stage q l s t u band L B lo rhs borrowed outTail inp out := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k = 110
  · subst k; simp [batchInputBank]
  · have hv : k.val ≠ 110 := by intro he; apply hk; exact Fin.ext he
    simp [batchInputBank,hk,hv]

theorem batchInputBank_update_result (precision stage q l s t u band L B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed result result' : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    {batchInputBank precision stage q l s t u band L B lo rhs borrowed result inp out with
      R := Function.update (batchInputBank precision stage q l s t u band L B lo rhs borrowed result inp out).R
        93 result'} =
      batchInputBank precision stage q l s t u band L B lo rhs borrowed result' inp out := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk : k = 93
  · subst k; simp [batchInputBank]
  · have hv : k.val ≠ 93 := by intro he; apply hk; exact Fin.ext he
    simp [batchInputBank,hk,hv]

theorem batchInputBank_low (precision stage q l s t u band L B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (k : Fin 117) (hk : k.val < 93) :
    (batchInputBank precision stage q l s t u band L B lo rhs borrowed outTail inp out).R k = [] := by
  have h101 : k.val ≠ 101 := by omega
  have h102 : k.val ≠ 102 := by omega
  have h103 : k.val ≠ 103 := by omega
  have h97 : k.val ≠ 97 := by omega
  have h98 : k.val ≠ 98 := by omega
  have h99 : k.val ≠ 99 := by omega
  have h100 : k.val ≠ 100 := by omega
  have h109 : k.val ≠ 109 := by omega
  have h112 : k.val ≠ 112 := by omega
  have h114 : k.val ≠ 114 := by omega
  have h116 : k.val ≠ 116 := by omega
  have h110 : k.val ≠ 110 := by omega
  have h93 : k.val ≠ 93 := by omega
  simp only [batchInputBank,ite_eq_right h101,ite_eq_right h102,ite_eq_right h103,ite_eq_right h97,ite_eq_right h98,ite_eq_right h99,ite_eq_right h100,ite_eq_right h109,ite_eq_right h112,ite_eq_right h114,ite_eq_right h116,ite_eq_right h110,ite_eq_right h93]

theorem packedCellInputBank_exec {precision stage q l s t u band origin N L V : ℕ}
    (C : ZMod s → GaussianInt) (hhalo : origin+N ≤ s) (hL : 0 < L)
    (offsets : List ℕ) (hne : offsets ≠ []) (hordered : offsets.Pairwise (· ≤ ·))
    (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (hVeq : V = weightWorkspaceWidth precision q (2*q+8) t u)
    (hwV : 2*q+8 < 2^V) (hcoords : origin+N < 2^V) (hunits : (origin+N)*(2*q+8) < 2^V)
    (tail outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hbank : embStk packedCellCoreReg S = batchInputBank precision stage q l s t u band L offsets.length
      (fun i => (packedCellOrigin (s := s) origin offsets i).val) []
      (cstream A (2*q+8) (packedInterval origin N C)++tail) outTail inp out)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hV : (S.R 163).length = V)
    (h153 : S.R 153 = []) (h155 : S.R 155 = binSyms V origin) (h154 : S.R 154 = binSyms V 0) :
    let rhs := cstream A (2*q+8) ((List.range offsets.length).flatMap
      (cellSourceRows L (packedCellOrigin (s := s) origin offsets) (fun _ => C)))
    ∃ v' m, v'.user = v.user ∧ m ≤ packedCellGroupInputCost V N L (2*q+8) offsets.length q ∧
      Exec body rawPackedCellInputs (mk v S) m
        (mk v' {S with R := Function.update S.R 110 (rhs++S.R 110)}) ∧
      embStk packedCellCoreReg {S with R := Function.update S.R 110 (rhs++S.R 110)} =
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
  have hpackets : S.R 109 = (offsets.map (origin+·)).flatMap (binSyms V)++List.replicate l tick := by
    simpa [bank,batchInputBank,packedCellCoreReg,← hVeq,packedCellOrigin_packets V offsets hhalo hL hfit] using hR 109
  obtain ⟨v',m,hu,hm,he⟩ := rawPackedCellInputs_exec (body := body)
    C hhalo (by omega) offsets hne hordered hfit tail v S h165 h166
    (by simpa [bank,batchInputBank,packedCellCoreReg] using congrArg List.length (hR 112))
    (by simpa [bank,batchInputBank,packedCellCoreReg] using hR 94) rfl
    (by simpa [bank,batchInputBank,packedCellCoreReg] using congrArg List.length (hR 102))
    (by simpa [bank,batchInputBank,packedCellCoreReg] using hR 110)
    hwV hcoords hunits (List.replicate offsets.length tick) (List.replicate l tick)
    (by simpa [bank,batchInputBank,packedCellCoreReg] using hR 116) (by simp)
    hpackets hV h153 h155 h154 hsmall hfresh
  have hrows : offsets.flatMap (fun j => cstream A (2*q+8) (packedInterval (origin+j) L C)) =
      cstream A (2*q+8) ((List.range offsets.length).flatMap
        (cellSourceRows L (packedCellOrigin (s := s) origin offsets) (fun _ => C))) := by
    rw [← packedCellRows_eq_sourceRows C offsets hhalo hfit]
    simp only [cstream,List.flatMap_assoc]
  refine ⟨v',m,hu,hm,by simpa only [hrows] using he,?_⟩
  have hproj : embStk packedCellCoreReg {S with R := (Function.update S.R 110
      (cstream A (2*q+8) ((List.range offsets.length).flatMap
        (cellSourceRows L (packedCellOrigin (s := s) origin offsets) (fun _ => C)))++S.R 110))} =
      {embStk packedCellCoreReg S with R := (Function.update (embStk packedCellCoreReg S).R 110
        (cstream A (2*q+8) ((List.range offsets.length).flatMap
          (cellSourceRows L (packedCellOrigin (s := s) origin offsets) (fun _ => C)))++S.R 110))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [embStk,packedCellCoreReg,Function.update_apply,Fin.ext_iff]
  rw [hproj,hbank]
  have hs : S.R 110 = cstream A (2*q+8) (packedInterval origin N C)++tail := by
    simpa [bank,batchInputBank,packedCellCoreReg] using hR 110
  rw [hs]
  exact batchInputBank_prepend_rhs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
