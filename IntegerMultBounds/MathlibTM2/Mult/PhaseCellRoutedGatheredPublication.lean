module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedEncodedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaGatherData

/-! Physical publication ports in the same disjoint placement as the generated
gathered solver. Packed halos are aligned and overwritten without extra banks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def routedGatheredPublication (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  routedEncodedPublication (plan.gather 121) (plan.gather 92) (plan.gather 88) (plan.gather 89)
    (plan.gather 103) (plan.solver 93) (plan.gather 124) (plan.gather 110) (plan.gather 1)
    (plan.gather 125) (plan.gather 7) (plan.gather 123) (plan.gather 122)

theorem routedGatheredPublication_exec_within (plan : ReplicaInteriorPlacement T)
    (origin span : ℕ) (Fs : List (ZMod s → GaussianInt)) (hspan : origin+span ≤ s)
    (windows : PublicationWindows span L) {w q e : ℕ} (hw1 : 1 ≤ w)
    (xs : BoundedEncodedStream A w q e)
    (hlen : xs.val.length = (Fs.length*windows.origins.length)*L*w)
    (sourceTail ambientTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (plan.solver 93) = xs.val++sourceTail)
    (hambient : S.R (plan.gather 124) = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++ambientTail)
    (hdst : S.R (plan.gather 110) = [])
    (hcount : (S.R (plan.gather 121)).length = Fs.length)
    (hvolume : (S.R (plan.gather 123)).length = span*w)
    (hc : S.R (plan.gather 92) = gatherControls A (windows.gaps w))
    (hwindow : (S.R (plan.gather 103)).length = L*w)
    (hclean : ∀ i ∈ [(88 : Fin 126),89,1,125,7,122], S.R (plan.gather i) = []) (depth : ℕ) :
    ∃ v' F n, ∃ replicas : List (PublicationReplica A),
      replicas.map PublicationReplica.ambient = Fs.reverse.map (fun F => cstream A w (packedInterval origin span F)) ∧
      replicas.flatMap (PublicationReplica.input w) = xs.val ∧
      (∀ r ∈ replicas, r.Valid windows w 0) ∧ v'.user = v.user ∧
      n ≤ routedEncodedPublicationCost Fs.length (span*w) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*routedEncodedPublicationCost Fs.length (span*w)) depth
        (routedGatheredPublication plan) (mk v S) n (mk v' F) ∧
      F.R (plan.solver 93) = sourceTail ∧ F.R (plan.gather 124) = ambientTail ∧
      F.R (plan.gather 110) = replicas.flatMap (PublicationReplica.output windows w) ∧
      F.R (plan.gather 121) = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ plan.solver 93 → i ≠ plan.gather 124 → i ≠ plan.gather 110 →
        i ≠ plan.gather 121 → F.R i = S.R i := by
  let regs : List (Fin 126 ⊕ Fin 121) :=
    [.inl 121,.inl 92,.inl 88,.inl 89,.inl 103,.inr 93,.inl 124,.inl 110,
      .inl 1,.inl 125,.inl 7,.inl 123,.inl 122]
  have hregs := List.Nodup.map plan.bank_injective (show regs.Nodup by decide)
  have hreg : [plan.gather 121,plan.gather 92,plan.gather 88,plan.gather 89,plan.gather 103,
      plan.solver 93,plan.gather 124,plan.gather 110,plan.gather 1,plan.gather 125,
      plan.gather 7,plan.gather 123,plan.gather 122].Nodup := by
    simpa only [regs,List.map_cons,List.map_nil,ReplicaInteriorPlacement.bank,Sum.elim_inl,Sum.elim_inr] using hregs
  let ambientRows := Fs.map (fun F => cstream A w (packedInterval origin span F))
  obtain ⟨v',F,n,replicas,ha,hinput,hvalid,hu,hn,he,hrest⟩ := routedEncodedPublication_exec_within (body := body)
    (plan.gather 121) (plan.gather 92) (plan.gather 88) (plan.gather 89) (plan.gather 103)
    (plan.solver 93) (plan.gather 124) (plan.gather 110) (plan.gather 1) (plan.gather 125)
    (plan.gather 7) (plan.gather 123) (plan.gather 122) hreg windows hw1 xs ambientRows
    (by
      intro ys hy
      obtain ⟨C,_,rfl⟩ := List.mem_map.mp hy
      rw [length_cstream,packedInterval_length C hspan])
    (by simpa only [ambientRows,List.length_map,Nat.mul_assoc] using hlen)
    sourceTail ambientTail v S hsrc (by simpa only [ambientRows,List.flatMap_def] using hambient)
    hdst (by simpa only [ambientRows,List.length_map] using hcount) hvolume hc hwindow
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp)) depth
  refine ⟨v',F,n,replicas,?_,hinput,hvalid,hu,?_,?_,hrest⟩
  · simpa only [ambientRows,List.map_reverse] using ha
  · simpa only [ambientRows,List.length_map] using hn
  · simpa only [ambientRows,List.length_map,routedGatheredPublication] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
