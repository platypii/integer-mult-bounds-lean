module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaTransposeProfile
public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileClosedGenerate

/-! Generate terminal-complete transpose coordinates, including the zero-base
first replica, with the same restoring runtime program for every replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Routing
variable {T Q A M B W C : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem replicaTransposeClosedProfile_exec
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lg Lk Ls : ℕ) (replica : Fin B) (choices : Fin (M*W) → Option (Fin C))
    (hM : 0 < M) (hg : W < 2^Lg) (hWpos : 0 < W) (hk : B*W < 2^Lk)
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
      steps ≤ groupedProfileClosedCost Li Lg Lk Ls (M*W) ∧
      Exec body (groupedProfileClosedProgram rg saved) (mk v S) steps
        (mk v' {S with R := (Function.update S.R (rg (.coordinate .dst))
          (sparseCoordinateFrames (Li+Lk) Ls (sparseCoordinateValues
            (sparseCoordinateClose ((M*B)*W)
              (sparsePatternCoordinates (N := (M*B)*W) (replicaProfilePosition B W replica.val) choices)))++
              S.R (rg (.coordinate .dst))))}) := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) replica.isLt
  have hpositive : 0 < (M*B)*W := Nat.mul_pos (Nat.mul_pos hM hB) hWpos
  have hbaseFit : replica.val*W < 2^(Li+Lk) := by
    have hr := Nat.mul_lt_mul_of_pos_right replica.isLt hWpos
    have hm := Nat.mul_le_mul_right (B*W) (show 1 ≤ M by omega)
    simp only [Nat.one_mul,←Nat.mul_assoc] at hm
    omega
  obtain ⟨v',steps,hu,hn,he⟩ := groupedProfileClosed_exec body rg hrg saved hsep
    Li Lg Lk Ls W (B*W) (replica.val*W) ((M*B)*W) choices
    hg hWpos hk hwidth hN hbaseFit hpositive hi (fun i => replicaProfilePosition_lt replica i) hchoices
    v S hsrc harchive hindex hgroup hstride hbase hlast hone hsaved hblank
  have hposition : (fun i => i/W*(B*W)+(i%W+replica.val*W)) =
      replicaProfilePosition B W replica.val := rfl
  rw [hposition] at he
  exact ⟨v',steps,hu,hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
