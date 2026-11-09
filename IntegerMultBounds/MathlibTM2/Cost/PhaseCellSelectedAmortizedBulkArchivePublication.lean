module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactReversedGroupedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPublicationClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGroupedPublicationReady
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatherSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreArchiveCopy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileSourceFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTilePlanStock
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! Transpose and publish one exact core class in a single physical trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.NLogN
open Filter IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement
variable {t₀ T Q K c d : ℕ} {P U : Type}

theorem selectedAmortizedBulkArchivePublication_exec (body : P → Pr P T Q (prime+K) U)
    (ct : ℕ) : ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    let p := Sizes.p m
    let s := Sizes.s m i
    let width := amortizedCoreWidth ct p
    ∀ (u target : ℕ) (htarget : target ≤ ct*p),
    let radius := localityDepth p target*PhaseCellBand.width p u
    let hw : 0 < width := (amortizedCoreWidth_bounds ct p u target (by have := h.thirteen_le_p; omega) htarget).1
    let g := gatherPublicationClass s width radius (width+2*radius)
    ∀ (W : ℕ) (hW : 1 ≤ W) (hA : 4 ≤ prime+K),
    ∀ (route : ArchiveTilePlan t₀ T Q c d (g.length*W))
    (dst : Fin T) (pub : PreparedPublicationPlan T route.src dst) (clock lineRows : Fin T)
    (hports : (pub.support++[route.src,dst,clock,lineRows]).Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^d)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (outputs : List (List (Fin (prime+K+4))))
    (houtputs : ∃ batches, outputs = batches.map (fun rows => cstream (prime+K) W rows.flatten) ∧
      List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows)
        (coreBulkIndices s width (PhaseCellBand.width p u) (localityDepth p target)) batches)
    (hcapacity : g.indices.length ≤ (2^d)^c)
    (ambient : Fin Fs.length → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*W)
    (outputTail borrowed : List (Fin (prime+K+4))) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (count savedCount rowWidth source archive saved tmp : Fin T)
    (hcopyReg : [count,savedCount,rowWidth,source,archive,route.src,saved,tmp].Nodup)
    (sourceTail : List (Fin (prime+K+4)))
    (ready : GroupedPublication.Ready g hw route pub clock lineRows count savedCount rowWidth archive saved tmp
      Fs.length ambient outputTail borrowed S)
    (hsource : S.R source = outputs.reverse.flatten++sourceTail) (depth : ℕ),
    let bill := replicaPublicationCost Fs.length s ((2^d)^c-g.indices.length) g.length W+
      37*s*W+6*Fs.length+31
    let copyBill := reverseCopyRowsCost g.indices.length (Fs.length*(g.length*W))
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' F n, v'.user = v.user ∧ n ≤ copyBill+(route.cost S+bill) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+
        (2*copyBill+(route.stockAllowance+2*bill))) depth
        (.seq (reverseCopyRows count savedCount rowWidth source archive route.src saved tmp)
          (.seq route.program (pub.replicaProgram clock lineRows))) (mk v S) n (mk v' F) ∧
      F.R route.src = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ dst → F.R r = S.R r := by
  dsimp only
  filter_upwards [selectedAmortizedGatherSchedule ct] with m hschedule
  intro h i _ u target htarget W hW hA route dst pub clock lineRows hports Fs hFs J outputs houtputs
    hcapacity ambient hambient outputTail borrowed v S count savedCount rowWidth source archive saved tmp
    hcopyReg sourceTail ready hsource depth
  obtain ⟨batches,houtputs,hrows⟩ := houtputs
  have hbulk := (hschedule h i u target htarget).2.2.2.1
  rw [hbulk] at hrows
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have hw := (amortizedCoreWidth_bounds ct (Sizes.p m) u target hp htarget).1
  have hpacket : 0 < (gatherPublicationClass (Sizes.s m i) (amortizedCoreWidth ct (Sizes.p m))
      (localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u)
      (amortizedCoreWidth ct (Sizes.p m)+2*(localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u))).length*W := by
    simpa only [gatherPublicationClass,Nat.add_sub_cancel_right] using Nat.mul_pos hw hW
  exact exactReversedGroupedPublication_exec body (Sizes.p m) W hW _ hw hpacket hA
    route dst pub clock lineRows hports Fs hFs J batches hrows hcapacity ambient hambient outputTail borrowed
    v S count savedCount rowWidth source archive saved tmp hcopyReg ready.count ready.rowWidth sourceTail ready.fresh
    ready.sourceBlank ready.bank (by simpa only [houtputs] using hsource) ready.publication ready.destination ready.clock ready.line depth

end IntegerMultBounds.MathlibTM2.Cost
