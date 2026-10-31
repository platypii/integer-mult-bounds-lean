module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaTransposeLayout
public import IntegerMultBounds.MathlibTM2.Routing.GroupedSourceProfileGenerate

/-! Execute the existing R4 grouped-profile generator for one replica's blocks.
Every absolute position is derived from the proved block transpose layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Routing

def replicaProfilePosition (B W replica i : ℕ) : ℕ :=
  i/W*(B*W)+(i%W+replica*W)

theorem replicaProfilePosition_address {M B W : ℕ}
    (core : Fin M) (replica : Fin B) (offset : Fin W) :
    replicaProfilePosition B W replica.val (offset.val+W*core.val) =
      (replicaBlockAddress core replica offset).val :=
  replicaBlockAddress_groupedSource core replica offset

theorem replicaProfilePosition_lt {M B W : ℕ} (replica : Fin B) (i : Fin (M*W)) :
    replicaProfilePosition B W replica.val i.val < (M*B)*W := by
  have h := replicaBlockAddress_groupedSource_lt (i.divNat) replica (i.modNat)
  have he : (i.modNat).val+W*(i.divNat).val = i.val := Nat.mod_add_div _ _
  simpa only [he,replicaProfilePosition] using h

/-- Each replica's core blocks occur in strictly increasing physical order,
so the profile can use the existing sparse-coordinate compiler. -/
theorem replicaProfilePosition_strictMono {B W : ℕ} (hB : 0 < B) (hW : 0 < W) (replica : ℕ) :
    StrictMono (replicaProfilePosition B W replica) := by
  intro i j hij
  have hdiv : i/W ≤ j/W := Nat.div_le_div_right hij.le
  by_cases heq : i/W = j/W
  · have hi := Nat.mod_add_div i W
    have hj := Nat.mod_add_div j W
    rw [heq] at hi
    dsimp only [replicaProfilePosition]
    rw [heq]
    omega
  · have hnext : i/W+1 ≤ j/W := by omega
    have hm := Nat.mul_le_mul_right (B*W) hnext
    have hBW : W ≤ B*W := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right W (show 1 ≤ B by omega)
    have hmod := Nat.mod_lt i hW
    dsimp only [replicaProfilePosition]
    simp only [Nat.add_mul,Nat.one_mul] at hm
    omega

theorem replicaTransposeCoordinates_ordered {M B W C : ℕ} (hW : 0 < W)
    (replica : Fin B) (choices : Fin (M*W) → Option (Fin C)) :
    (sparsePatternCoordinates (N := (M*B)*W) (replicaProfilePosition B W replica.val) choices).Pairwise
      (fun x y => x.1 < y.1) := by
  apply sparsePatternCoordinates_ordered _
    (replicaProfilePosition_strictMono (lt_of_le_of_lt (Nat.zero_le _) replica.isLt) hW replica.val) choices
  intro i hi
  exact replicaProfilePosition_lt replica ⟨i,hi⟩

variable {T Q A M B W C : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem replicaTransposeProfile_exec
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lg Lk Ls : ℕ) (replica : Fin B) (choices : Fin (M*W) → Option (Fin C))
    (hg : W < 2^Lg) (hWpos : 0 < W) (hk : B*W < 2^Lk)
    (hwidth : Lg ≤ Li+Lk) (hN : (M*B)*W < 2^(Li+Lk))
    (hi : M*W ≤ 2^Li) (hchoices : C+1 < 2^Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile choices))
    (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg (.coordinate (.arithmetic .index))) = binSyms Li 0)
    (hgroup : S.R (rg (.coordinate (.arithmetic .group))) = binSyms Lg W)
    (hstride : S.R (rg (.coordinate (.arithmetic .stride))) = binSyms Lk (B*W))
    (hbase : S.R (rg (.coordinate (.arithmetic .base))) = binSyms (Li+Lk) (replica.val*W))
    (hlast : S.R (rg (.coordinate .last)) = binSyms (Li+Lk) ((M*B)*W-1))
    (hone : S.R (rg (.coordinate .one)) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ∉ groupedProfileLive → S.R (rg r) = []) :
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ (M*W)*(groupedProfileCallCost Li Lg Lk Ls+2)+
        2*((M*W)*(Ls+3))+16*Li+20 ∧
      Exec body (groupedProfileGenerateProgram rg saved) (mk v S) steps
        (mk v' {S with R := (Function.update S.R (rg (.coordinate .dst))
          (sparseCoordinateFrames (Li+Lk) Ls (sparseCoordinateValues
            (sparsePatternCoordinates (N := (M*B)*W) (replicaProfilePosition B W replica.val) choices))++
              S.R (rg (.coordinate .dst))))}) := by
  have hpos (i : Fin (M*W)) : (0+i.val)/W*(B*W)+((0+i.val)%W+replica.val*W) < (M*B)*W := by
    simpa only [Nat.zero_add,replicaProfilePosition] using replicaProfilePosition_lt replica i
  obtain ⟨v',steps,hu,hn,he⟩ := groupedSourceProfileGenerate_exec body rg hrg saved hsep
    Li Lg Lk Ls 0 W (B*W) (replica.val*W) ((M*B)*W) choices
    hg hWpos hk hwidth hN (by simpa only [Nat.zero_add] using hi) hpos hchoices
    v S hsrc harchive hindex hgroup hstride hbase hlast hone hsaved hblank
  have hposition : (fun i => (0+i)/W*(B*W)+((0+i)%W+replica.val*W)) =
      replicaProfilePosition B W replica.val := by
    funext i
    simp only [replicaProfilePosition,Nat.zero_add]
  rw [hposition] at he
  exact ⟨v',steps,hu,hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
