module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingGeometryStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Install the geometry width from its retained master and generate binary
coupling geometry in the extended bank, preserving all queues and masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareReplicaCouplingGeometry {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) : Pr P T Q A U :=
  .seq (ucopy (plan.gather 115) (placement.bank 163) (plan.gather 7))
    (embProg placement.bank Empty.elim (generateCouplingGeometry (P := Empty)))

def prepareReplicaCouplingGeometryCost (V s t band a b : ℕ) :=
  4*V+4+generateCouplingGeometryCost V s t band a b

theorem prepareReplicaCouplingGeometry_exec_within {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (V s t band a b : ℕ) (hab : a ≤ b)
    (hbV : b < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (v : HS T Q A U) (S : Stacks T A) (hV : (S.R (plan.gather 115)).length = V)
    (hheaders : ∀ p ∈ couplingGeometryAssignments,
      (S.R (placement.bank p.1)).length = couplingGeometryHeaderValue s t band a b p.1)
    (hblank : ∀ k ∈ ([(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,155,156,157,163,164,165]), S.R (placement.bank k) = [])
    (htmp : S.R (plan.gather 7) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ prepareReplicaCouplingGeometryCost V s t band a b ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        3*prepareReplicaCouplingGeometryCost V s t band a b) depth
        (prepareReplicaCouplingGeometry placement) (mk v S) n (mk v' F) ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk placement.bank F) ∧
      embStk plan.gather F = embStk plan.gather S ∧
      embStk weightCacheCoreReg (embStk plan.solver F) = embStk weightCacheCoreReg (embStk plan.solver S) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ i : Fin 168, placement.bank i ≠ k) → F.R k = S.R k) ∧
      (∀ k : Fin 168, k ≠ 163 →
        k ∉ [145,146,147,148,149,151,154,155,156,164,165] → F.R (placement.bank k) = S.R (placement.bank k)) := by
  have hsrc : plan.gather 115 ≠ placement.bank 163 := (placement.bank_gather_disjoint 163 115).symm
  have hdst : placement.bank 163 ≠ plan.gather 7 := placement.bank_gather_disjoint 163 7
  have htmpSrc : plan.gather 115 ≠ plan.gather 7 := plan.gather_injective.ne (by decide)
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) hsrc htmpSrc hdst v S htmp
  let J : Stacks T A := {S with R := Function.update S.R (placement.bank 163) (List.replicate V tick)}
  have he₁' : Exec body (ucopy (plan.gather 115) (placement.bank 163) (plan.gather 7))
      (mk v S) (4*V+4) (mk v₁ J) := by
    simpa [J,hV,hblank 163 (by simp)] using he₁
  have hj (k : Fin 168) (hk : k ≠ 163) : J.R (placement.bank k) = S.R (placement.bank k) := by
    exact Function.update_of_ne (placement.bank_injective.ne hk) _ _
  obtain ⟨vi,C,n₂,hu₂,hn₂,he₂,hmeta,hleft,hi,ho,hframe⟩ := generateCouplingGeometry_exec
    (body := fun p : Empty => nomatch p) V s t band a b hab hbV hfitV
    (embDn placement.bank v₁) (embStk placement.bank J)
    (by simp [J,embStk])
    (by intro p hp
        change (J.R (placement.bank p.1)).length = _
        rw [hj p.1 (by
          simp only [couplingGeometryAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
        exact hheaders p hp)
    (by intro k hk
        change J.R (placement.bank k) = []
        rw [hj k (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
        apply hblank
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have hei := mn_native_exec_within he₂ 3 generateCouplingGeometry_native depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn₂) _)
  obtain ⟨v₂,_,hu₂',he⟩ := exec_emb_ovr_within_stock placement.bank placement.bank_injective
    (body' := body) (ι := Empty.elim) (fun p : Empty => nomatch p) hei v₁ rfl J rfl
  let F := embOvr placement.bank C.get J
  have hview : embStk placement.bank F = C := embStk_ovr placement.bank_injective C J
  have hleftF : F.L = S.L := by
    funext k
    by_cases hk : ∃ i, placement.bank i = k
    · obtain ⟨i,rfl⟩ := hk
      change (embOvr placement.bank C.get J).L (placement.bank i) = _
      exact (congrFun (congrArg Stacks.L hview) i).trans (congrFun hleft i)
    · exact (embOvr_off C.get J (by simpa using hk)).1
  have hRoff (k : Fin T) (hk : ∀ i, placement.bank i ≠ k) : F.R k = S.R k := by
    exact ((embOvr_off C.get J hk).2).trans (Function.update_of_ne (hk 163).symm _ _)
  have hn : ∀ i : Fin 117, C.R (Fin.castLE (by decide) i) = S.R (plan.solver (weightCacheCoreReg i)) := by
    intro i
    have hi := i.isLt
    have hhigh : ∀ k : Fin 168, k ∈ [145,146,147,148,149,151,154,155,156,164,165] → 145 ≤ k.val := by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hoff := hframe (Fin.castLE (by decide : 117 ≤ 168) i) (by
      intro hm
      have hh := hhigh _ hm
      change 145 ≤ i.val at hh
      omega)
    change C.R _ = J.R (placement.bank _) at hoff
    rw [placement.bank_native] at hoff
    apply hoff.trans
    have hne : (Fin.castLE (by decide : 117 ≤ 168) i : Fin 168) ≠ 163 := by
      intro h
      have hv : i.val = 163 := congrArg Fin.val h
      omega
    simpa only [placement.bank_native] using hj (Fin.castLE (by decide : 117 ≤ 168) i) hne
  have hecopy := mn_native_exec_within he₁' 2 (by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]) depth _ (le_refl _)
  refine ⟨v₂,F,(4*V+4)+n₂,hu₂'.trans (hu₂.trans hu₁),by unfold prepareReplicaCouplingGeometryCost; omega,?_,?_,?_,?_,hleftF,?_,?_,hRoff,?_⟩
  · have hsize := hecopy.final
    change mnSize (mk v₁ J)+depth ≤ mnSize (mk v S)+depth+2*(4*V+4) at hsize
    refine .seq (hecopy.mono ?_) (he.mono ?_)
    all_goals intro d z hz; dsimp only [prepareReplicaCouplingGeometryCost] at *; omega
  · change CouplingIntervalMetadata _ _ _ _ _ _ _ _ (embStk placement.bank (embOvr placement.bank C.get J))
    rw [embStk_ovr placement.bank_injective]
    exact hmeta
  · refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hi
    · exact ho
    · exact congrArg (fun L => L ∘ plan.gather) hleftF
    · funext k
      exact hRoff _ (fun i => placement.bank_gather_disjoint i k)
  · rw [← placement.native_view F]
    refine Stacks.ext hi ho ?_ ?_
    · funext i
      change F.L (placement.bank (Fin.castLE (by decide) i)) = _
      rw [placement.bank_native]
      exact congrFun hleftF _
    · funext i
      change F.R (placement.bank (Fin.castLE (by decide) i)) = _
      exact (congrFun (congrArg Stacks.R hview) _).trans (hn i)
  · exact hi
  · exact ho

  · intro k h163 hk
    exact (congrFun (congrArg Stacks.R hview) k).trans ((hframe k hk).trans (hj k h163))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
