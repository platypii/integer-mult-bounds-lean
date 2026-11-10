module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSeedGeneratorLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSeedInstallation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGeneratedHeaders

/-! Generate the ten seed masters in the blank selector table, install both
physical seed banks, and retire the masters before selection begins. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

theorem seedBank_eq (side : Bool) (i : Fin 392) :
    seedBank side i = if side then seedR i else seedL i := by
  cases side <;> rfl

theorem selector_ne_seedBank (r : Fin LocalRecoveryLayout.tapes) (side : Bool) (i : Fin 392) :
    selector r ≠ seedBank side i := by
  cases side
  · exact selector_ne_seedL r i
  · exact selector_ne_seedR r i

theorem aux_ne_seedBank (k : Fin 9) (side : Bool) (i : Fin 392) : aux k ≠ seedBank side i := by
  cases side <;> simp [seedBank,seedL,seedR,aux,port_injective.eq_iff]

/-- The masters avoid every right stack read by ordinary caller readiness. -/
theorem seedMaster_ne_context (r : Fin tapes) (hr : caller.contextSupport r) (i : Fin 10) :
    seedMaster i ≠ r := by
  rcases hr with ⟨j,rfl⟩ | ⟨j,_,rfl | rfl⟩ | ⟨j,rfl⟩ | hr
  · exact selector_ne_numeric _ j
  · exact selector_ne_seedL _ j
  · exact selector_ne_seedR _ j
  · change seedMaster i ≠ controls j
    fin_cases j
    · intro h
      have hg := congrArg Fin.val ((selector_injective.comp LocalRecoveryLayout.geometry_injective) h)
      have hi := i.isLt
      change i.val = 94 at hg
      omega
    · exact selector_ne_aux _ 0
    · exact selector_ne_aux _ 1
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact selector_ne_aux _ 3
    · exact selector_ne_aux _ 4

/-- Unary installation bill of one seed bank, from header values alone. -/
def seedInstallCost {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (W N : ℕ) : ℕ :=
  (recoverySeedHeaderPorts.map fun k => 4*recoverySeedHeader H W N k+4).sum+1

theorem copySeedHeaders_cost {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (W N : ℕ)
    (source work : Fin 392 → Fin tapes) (S : Stacks tapes A)
    (hvalues : ∀ k ∈ recoverySeedHeaderPorts, (S.R (source k)).length = recoverySeedHeader H W N k) :
    copyUnaryHeadersCost (fun r => (S.R r).length) (recoverySeedHeaderCopies source work) =
      seedInstallCost H W N := by
  simp only [copyUnaryHeadersCost,recoverySeedHeaderCopies,seedInstallCost,List.map_map,Function.comp_def]
  congr 2
  apply List.map_congr_left
  intro k hk
  rw [hvalues k hk]

def generatedSeedSetup : Pr P tapes Q A U :=
  .seq seedGenerator.program
    (.seq (installRetainedSeedPair seedGenerator.left seedGenerator.right)
      (clearWords (List.ofFn seedMaster)))

/-- From ordinary scalar headers and blank seed banks, the complete setup
produces caller readiness and changes no right stack outside the seed banks. -/
theorem generatedSeedSetup_exec {B p u l target s t a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hfit : a+n ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^B)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B)
    (hprecisionRoom : inversePrecisionRoom p l target
      (haloBoundary s t (PhaseCellBand.width p u) a (a+n)).card (PhaseCellBand.width p u) < 2^B)
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,a+n] i < 2^B) :
    let stage := initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2
    ∀ (Fs : List (ZMod s → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ i, ‖value (executionPrecision p l stage 2) (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem stage 2 a n (by omega) Fs hF
    ∀ (W N radius rows : ℕ) (v : HS tapes Q A U) (S : Stacks tapes A),
    seedGenerator.Ready B p u l target s t a n W N S →
    (∀ side i, S.R (seedBank side i) = []) →
    (∀ i, S.L (caller.bank i) = [] ∧ S.R (caller.bank i) = []) →
    (∀ i, (S.R (caller.controls i)).length = ![W,radius,rows] i) →
    let install := seedInstallCost H W N+seedInstallCost K W N
    ∃ v' D steps, v'.user = v.user ∧ caller.InputContext H K W N radius rows D ∧
      D.L = S.L ∧ D.inp = S.inp ∧ D.out = S.out ∧
      (∀ r, (∀ side i, r ≠ seedBank side i) → D.R r = S.R r) ∧
      steps ≤ CyclicSeedLayout.timeCost B p u l target s t a n+
        (install+(2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+21)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
          (CyclicSeedLayout.workspace B p u l target s t a n+2*install)) 0
        generatedSeedSetup (Host.mk v S) steps (Host.mk v' D) := by
  dsimp only
  intro Fs hF W N radius rows v S ready hseedBlank hbank hcontrols
  obtain ⟨v₁,G,n₁,hu₁,hn₁,he₁,hleftSeed,hrightSeed,hI,hO,hL,hframe⟩ :=
    seedGenerator.program_exec (body := body) axis ha hfit hbandRoom hgeometryRoom hprecisionRoom
      hvaluesFit Fs hF W N v S ready
  have hstable (r : Fin tapes) (hr : caller.contextSupport r) : G.R r = S.R r :=
    hframe r (fun i => seedMaster_ne_context r hr i)
  have hsources (r : Fin tapes) (hgeometry : ∀ i, geometry i ≠ r) (hreplicas : aux 7 ≠ r) (i : Fin 392) :
      seedGenerator.left i ≠ r ∧ seedGenerator.right i ≠ r :=
    ⟨(seedGenerator_sources_ne r hgeometry hreplicas).1 i,
      (seedGenerator_sources_ne r hgeometry hreplicas).2 i⟩
  obtain ⟨v₂,F,hu₂,hcontext,hFL,hFI,hFO,hinstalled,he₂⟩ :=
    installRetainedSeedPair_exec (body := body) seedGenerator.left seedGenerator.right
      _ _ W N radius rows v₁ G
      (fun side i j => hsources _ (fun k => selector_ne_seedBank _ side j) (aux_ne_seedBank 7 side j) i)
      (fun i => hsources _ (fun k => selector_ne_aux _ 4)
        (by simp [aux,port_injective.eq_iff]) i)
      hleftSeed hrightSeed
      (fun side i => (hframe _ (fun k => selector_ne_seedBank _ side i)).trans (hseedBlank side i))
      (fun i => ⟨(congrFun hL _).trans (hbank i).1,
        (hstable _ (Or.inl ⟨i,rfl⟩)).trans (hbank i).2⟩)
      (fun i => by rw [hstable _ (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))]; exact hcontrols i)
      ((hstable _ (Or.inr (Or.inr (Or.inr (by simp))))).trans (ready.scratch _ (by simp [seedGenerator])))
      ((hstable _ (Or.inr (Or.inr (Or.inr (by simp))))).trans (ready.scratch _ (by simp [seedGenerator])))
  rw [copySeedHeaders_cost _ W N _ _ G hleftSeed,copySeedHeaders_cost _ W N _ _ G hrightSeed] at he₂
  let D : Stacks tapes A := {F with R := fun k => if k ∈ List.ofFn seedMaster then [] else F.R k}
  have hmaster (i : Fin 10) : D.R (seedMaster i) = [] := by
    simp only [D,List.mem_ofFn,exists_apply_eq_apply,ite_true]
  have hrest (r : Fin tapes) (hr : ∀ i, seedMaster i ≠ r) : F.R r = D.R r := by
    have hk : ¬∃ i, seedMaster i = r := by simpa only [not_exists] using hr
    simp only [D,List.mem_ofFn,hk,ite_false]
  have hgenerated (i : Fin 10) :
      (F.R (seedMaster i)).length = inverseMasterValues p u l target s t a (a+n) i := by
    have hm : recoveryMasterPort i ∈ recoverySeedHeaderPorts := recoverySeedHeaderPorts_perm.mem_iff.mpr
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    have hv := hleftSeed _ hm
    simp only [CyclicSeedLayout.left,recoverySeedSources_master,recoverySeedHeader_master] at hv
    rw [hinstalled (seedMaster i) (fun side j => selector_ne_seedBank _ side j)]
    exact hv.trans (congrFun (axis.fittingCyclicLeftMasterValues target a n ha hfit Fs hF) i)
  obtain ⟨v₃,hu₃,he₃⟩ := retireGeneratedHeaders_exec (body := body) seedMaster seedMaster_injective
    (inverseMasterValues p u l target s t a (a+n)) v₂ D F hmaster hgenerated rfl rfl rfl hrest 0
  have hclear : 2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+2*10+1 =
      2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+21 := by omega
  rw [hclear] at he₃
  have hinstall := he₂ 0
  rw [←Nat.mul_add] at hinstall
  have hsetup := mn_seq_within_no_growth hinstall he₃
  have hwhole := mn_seq_within_add he₁ hsetup
  refine ⟨v₃,D,_,hu₃.trans (hu₂.trans hu₁),?_,hFL.trans hL,hFI.trans hI,hFO.trans hO,?_,
    Nat.add_le_add_right hn₁ _,hwhole⟩
  · exact hcontext.frame (fun _ => rfl) (fun r hr => (hrest r (fun i => seedMaster_ne_context r hr i)).symm)
  · intro r hr
    by_cases hk : ∃ i, seedMaster i = r
    · obtain ⟨i,rfl⟩ := hk
      exact (hmaster i).trans (ready.masters i).symm
    · have hoff : ∀ i, seedMaster i ≠ r := by simpa only [not_exists] using hk
      exact ((hrest r hoff).symm.trans (hinstalled r hr)).trans (hframe r hoff)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
