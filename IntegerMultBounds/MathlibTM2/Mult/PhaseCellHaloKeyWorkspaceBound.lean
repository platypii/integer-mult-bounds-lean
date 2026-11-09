module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloPreparationWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthKeyLoopStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchWorkspaceMono
import Mathlib.Tactic.GCongr

/-! Selected length keys share numerical setup and one uniform metadata allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

@[irreducible] def haloKeySharedSetup (J R K p l s t u target rhsExp L : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  generatedBatchSetupWorkspace J (2^15*p) (executionStagePrecision p l target rhsExp+1)
    q s t u (PhaseCellBand.width p u) l L 0+
  cellArithmeticWorkspace R K q (sourceExponent l target rhsExp) (8*p+1) l w 0 L

@[irreducible] def haloKeyAuxWorkspace (R K p l s t u target rhsExp V : ℕ) : ℕ :=
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let G := haloGeometryWidth t (2*q+8)
  let W := weightWorkspaceWidth P q (2*q+8) t u
  9*tblC G G+50000*(P+N+q+l+s+t+u+band+1)*(G+W+q+1)+
    (100000*(R+K+1)*(t+1)*(2^l+s+1)*(w+sourceExponent l target rhsExp+(8*p+1)+l+1)+
      30000*((t+1)+1)*(s+1)*(q+l+1))+
    20000*((t+1)+s+s+s+1)*(q+1)+3*(6*s+19*V+14)

private theorem combine_bounds {x a b c d e f g : ℕ}
    (hx : x ≤ a+b+c+d) (ha : a ≤ e) (hb : b ≤ f+g) :
    x ≤ f+(e+g+c+d) := by omega

private theorem enlarge_terms {x f e g₁ g₂ c d G₁ G₂ C D : ℕ}
    (h : x ≤ f+(e+(g₁+g₂)+c+d)) (h₁ : g₁ ≤ G₁) (h₂ : g₂ ≤ G₂)
    (hc : c ≤ C) (hd : d ≤ D) : x ≤ f+(e+(G₁+G₂)+C+D) := by omega

theorem processHaloLengthKeyWorkspace_le_shared_setup
    (J R K p l L s t u target rhsExp V a b : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) (hL : L ≤ s) :
    processHaloLengthKeyWorkspace J R K p l L s t u target rhsExp V a b ≤
      haloKeySharedSetup J R K p l s t u target rhsExp L+
      haloKeyAuxWorkspace R K p l s t u target rhsExp V := by
  have hp := conditionalHaloGroupPreparationWorkspace_le_uniform
    (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b L ha hb hL
  have hc := processHaloLengthKeyWorkspace_le_components J R K p l L s t u target rhsExp V a b
  have hs := sizedClosedBatchWorkspace_le_shared_setup J R K p l
    (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length L s t u target rhsExp
  dsimp only at hp hc hs
  have h := combine_bounds hc hp hs
  unfold haloKeySharedSetup haloKeyAuxWorkspace
  dsimp only
  have hB := (haloLengthGroup_length_le s t (PhaseCellBand.width p u) a b L).trans
    (Nat.add_le_add_right (Nat.sub_le t s) 1)
  have hd₁ := Nat.mul_le_mul_right
    (executionWidth p l target rhsExp+sourceExponent l target rhsExp+(8*p+1)+l+1)
    (Nat.mul_le_mul (Nat.mul_le_mul_left (100000*(R+K+1)) hB)
      (show 2^l+L+1 ≤ 2^l+s+1 by omega))
  have hd₂ := Nat.mul_le_mul_right (executionPrecision p l target rhsExp+l+1)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 30000
      (show (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length+1 ≤ (t+1)+1 by omega))
      (show L+1 ≤ s+1 by omega))
  have hp' := Nat.mul_le_mul_right (executionPrecision p l target rhsExp+1)
    (Nat.mul_le_mul_left 20000
      (show (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length+s+a+b+1 ≤
        (t+1)+s+s+s+1 by omega))
  have hd : 3*(6*L+19*V+14) ≤ 3*(6*s+19*V+14) := by omega
  simpa only [Nat.add_assoc] using enlarge_terms h hd₁ hd₂ hp' hd

private theorem max_map_le_add (keys : List ℕ) (f g : ℕ → ℕ) (c : ℕ)
    (h : ∀ L ∈ keys, f L ≤ g L+c) :
    (keys.map f).foldr max 0 ≤ (keys.map g).foldr max 0+c := by
  induction keys with
  | nil => simp
  | cons L keys ih =>
    simp only [List.map_cons,List.foldr_cons]
    apply max_le
    · exact (h L (by simp)).trans (Nat.add_le_add_right (le_max_left _ _) c)
    · exact (ih (fun L hL => h L (by simp [hL]))).trans
        (Nat.add_le_add_right (le_max_right _ _) c)

theorem haloLengthKeyLoopWorkspace_le_shared_setup
    (J R K p l s t u target rhsExp V a b : ℕ) (keys : List ℕ)
    (ha : a ≤ s) (hb : b ≤ s) (hkeys : ∀ L ∈ keys, L ≤ s) :
    haloLengthKeyLoopWorkspace J R K p l s t u target rhsExp V a b keys ≤
      (keys.map (haloKeySharedSetup J R K p l s t u target rhsExp)).foldr max 0+
        haloKeyAuxWorkspace R K p l s t u target rhsExp V := by
  unfold haloLengthKeyLoopWorkspace haloLengthKeyLoopSharedWorkspace
  apply max_map_le_add
  intro L hL
  exact processHaloLengthKeyWorkspace_le_shared_setup J R K p l L s t u target rhsExp V a b
    ha hb (hkeys L hL)

theorem haloKeySharedSetup_mono (J R K p l s t u target rhsExp L M : ℕ) (hL : L ≤ M) :
    haloKeySharedSetup J R K p l s t u target rhsExp L ≤
      haloKeySharedSetup J R K p l s t u target rhsExp M := by
  unfold haloKeySharedSetup
  dsimp only
  exact Nat.add_le_add (generatedBatchSetupWorkspace_zero_mono _ _ _ _ _ _ _ _ _ _ _ hL)
    (cellArithmeticWorkspace_zero_mono _ _ _ _ _ _ _ _ _ hL)

private theorem max_map_le (keys : List ℕ) (f : ℕ → ℕ) (cap : ℕ)
    (h : ∀ L ∈ keys, f L ≤ cap) : (keys.map f).foldr max 0 ≤ cap := by
  induction keys with
  | nil => simp
  | cons L keys ih =>
    simp only [List.map_cons,List.foldr_cons]
    exact max_le (h L (by simp)) (ih (fun L hL => h L (by simp [hL])))

theorem haloLengthKeyLoopWorkspace_le_uniform
    (J R K p l s t u target rhsExp V a b M : ℕ) (keys : List ℕ)
    (ha : a ≤ s) (hb : b ≤ s) (hkeys : ∀ L ∈ keys, L ≤ s ∧ L ≤ M) :
    haloLengthKeyLoopWorkspace J R K p l s t u target rhsExp V a b keys ≤
      haloKeySharedSetup J R K p l s t u target rhsExp M+
        haloKeyAuxWorkspace R K p l s t u target rhsExp V := by
  apply (haloLengthKeyLoopWorkspace_le_shared_setup J R K p l s t u target rhsExp V a b keys
    ha hb (fun L hL => (hkeys L hL).1)).trans
  apply Nat.add_le_add_right
  apply max_map_le
  intro L hL
  exact haloKeySharedSetup_mono J R K p l s t u target rhsExp L M (hkeys L hL).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
