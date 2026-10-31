module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaInteriorCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPackedReplicaGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! One copied numerical key and one local-control gather prepare disjoint banks
for the counted numerical handoff. Every preparation phase is executed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def gatheredReplicaInteriorPreparation (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  .seq (embProg plan.solver Empty.elim (prepareReplicaInteriorCache (P := Empty)))
    (embProg plan.gather Empty.elim (sharedPackedReplicaGather (P := Empty)))

theorem gatheredReplicaInteriorPreparation_exec (plan : ReplicaInteriorPlacement T)
    {s : ℕ} (Pbits stage q l t u band V origin span L w : ℕ)
    (offsets : List ℕ) (Fs : List (ZMod s → GaussianInt)) (lo : ℕ → ℕ)
    (hne : offsets ≠ []) (hspan : origin+span ≤ s) (hordered : offsets.Pairwise (· ≤ ·))
    (hfit : ∀ j ∈ offsets, j+L ≤ span)
    (hwV : w < 2^V) (hcoords : span < 2^V) (hunits : span*w < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (tail borrowed suffix packedBorrowed : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) =
      replicaInteriorCacheInputBank A Pbits stage q l s t u band Fs.length offsets.length L w lo
        [] borrowed tail inp out)
    (hcacheFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = [])
    (hV : (S.R (plan.gather 115)).length = V)
    (hw : (S.R (plan.gather 94)).length = w) (hL : (S.R (plan.gather 102)).length = L)
    (hpackets : S.R (plan.gather 109) = offsets.flatMap (binSyms V)++suffix)
    (hcount : S.R (plan.gather 116) = List.replicate offsets.length tick)
    (hreplicas : (S.R (plan.gather 121)).length = Fs.length)
    (hvolume : (S.R (plan.gather 123)).length = span*w)
    (hsource : S.R (plan.gather 124) =
      Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++packedBorrowed)
    (hblank : ∀ k : Fin 126, k.val < 19 → S.R (plan.gather k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 126),89,90,91,92,104,105,106,122,125], S.R (plan.gather k) = []) :
    let rhs := Fs.reverse.flatMap (fun F => cstream A w (offsets.flatMap
      (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => F) 0)))
    ∃ v' F n, v'.user = v.user ∧
      n ≤ prepareReplicaInteriorCacheCost Fs.length offsets.length L w+
        sharedPackedReplicaGatherCost V Fs.length span L w offsets.length ∧
      Exec body (gatheredReplicaInteriorPreparation plan) (mk v S) n (mk v' F) ∧
      embStk plan.gather F = {embStk plan.gather S with R :=
        (Function.update (embStk plan.gather S).R 110 (rhs++S.R (plan.gather 110)))} ∧
      embStk weightCacheCoreReg (embStk plan.solver F) =
        batchInputBank Pbits stage q l s t u band L (Fs.length*offsets.length)
          (fun n => lo (n%offsets.length)) [] borrowed tail inp out ∧
      F.R (plan.solver 117) = batchWeightPage A w q Pbits s t u
        (Fs.length*offsets.length) L (fun n => lo (n%offsets.length))++S.R (plan.solver 117) ∧
      F.R (plan.solver 118) = List.replicate (2*((Fs.length*offsets.length)*(L*w))) tick ∧
      F.R (plan.solver 119) = [] ∧ F.R (plan.solver 120) = [] := by
  dsimp only
  obtain ⟨vi,M,n₁,hui,hn₁,hei,hbankM,hcache,hclock,h119,h120⟩ :=
    prepareReplicaInteriorCache_exec (body := fun p : Empty => nomatch p)
      Pbits stage q l s t u band Fs.length offsets.length L w
      (List.length_pos_iff.mpr hne) lo [] borrowed tail inp out
      (embDn plan.solver v) (embStk plan.solver S) hbank hcacheFresh
  obtain ⟨v₁,G,he₁,hv₁,hu₁,hsolver,hoff⟩ := exec_emb (body' := body) (ι := Empty.elim)
    plan.solver_injective (fun p => nomatch p) hei v rfl S rfl
  have hg : embStk plan.gather G = embStk plan.gather S := by
    have hI : M.inp = S.inp :=
      (congrArg Stacks.inp hbankM).trans (congrArg Stacks.inp hbank).symm
    have hO : M.out = S.out :=
      (congrArg Stacks.out hbankM).trans (congrArg Stacks.out hbank).symm
    refine Stacks.ext ((congrArg Stacks.inp hsolver).trans hI)
      ((congrArg Stacks.out hsolver).trans hO) ?_ ?_
    · funext k
      exact (hoff (plan.gather k) (fun j => (plan.disjoint k j).symm)).1
    · funext k
      exact (hoff (plan.gather k) (fun j => (plan.disjoint k j).symm)).2
  have hR (k : Fin 126) : G.R (plan.gather k) = S.R (plan.gather k) :=
    congrArg (fun M : Stacks 126 A => M.R k) hg
  obtain ⟨vg,n₂,hug,hn₂,heg⟩ := sharedPackedReplicaGather_exec
    (body := fun p : Empty => nomatch p) V origin span L w offsets Fs hne hspan hordered hfit
      hwV hcoords hunits suffix packedBorrowed (embDn plan.gather v₁) (embStk plan.gather G)
      (by simpa only [embStk,Function.comp_apply,hR] using hV) (by simpa only [embStk,Function.comp_apply,hR] using hw)
      (by simpa only [embStk,Function.comp_apply,hR] using hL) (by simpa only [embStk,Function.comp_apply,hR] using hpackets)
      (by simpa only [embStk,Function.comp_apply,hR] using hcount) (by simpa only [embStk,Function.comp_apply,hR] using hreplicas)
      (by simpa only [embStk,Function.comp_apply,hR] using hvolume) (by simpa only [embStk,Function.comp_apply,hR] using hsource)
      (by intro k hk; simpa only [embStk,Function.comp_apply,hR] using hblank k hk)
      (by intro k hk; simpa only [embStk,Function.comp_apply,hR] using hfresh k hk)
  let rhs := Fs.reverse.flatMap (fun F => cstream A w (offsets.flatMap
    (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => F) 0)))
  obtain ⟨v₂,hu₂,he₂⟩ := exec_emb_stream plan.gather plan.gather_injective Empty.elim
    (fun p : Empty => nomatch p) body (fun p => nomatch p) sharedPackedReplicaGather v₁ G vg n₂ 110
      (rhs++G.R (plan.gather 110)) heg
  let F : Stacks T A := {G with R := Function.update G.R (plan.gather 110) (rhs++G.R (plan.gather 110))}
  have hs : embStk plan.solver F = M :=
    (plan.solver_update_gather G 110 _).trans hsolver
  refine ⟨v₂,F,n₁+n₂,hu₂.trans (hug.trans (hu₁.trans hui)),Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁ he₂,?_,?_,?_,?_,?_,?_⟩
  · have hh := embStk_update_stream plan.gather plan.gather_injective G 110 (rhs++G.R (plan.gather 110))
    change embStk plan.gather F = _ at hh
    simpa only [hg,hR] using hh
  · exact (congrArg (embStk weightCacheCoreReg) hs).trans hbankM
  · exact (congrArg (fun M : Stacks 121 A => M.R 117) hs).trans hcache
  · exact (congrArg (fun M : Stacks 121 A => M.R 118) hs).trans hclock
  · exact (congrArg (fun M : Stacks 121 A => M.R 119) hs).trans h119
  · exact (congrArg (fun M : Stacks 121 A => M.R 120) hs).trans h120

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
