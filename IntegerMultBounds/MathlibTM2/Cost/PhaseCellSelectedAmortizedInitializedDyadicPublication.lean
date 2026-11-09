module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedDyadicPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPublicationHeaders
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDyadicPublicationHeaderBudget

/-! Generate binary dimensions from unary masters, execute selected dyadic
publication, and retire the owned headers. Only source and output change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement PackedTranspose FixedStreamedBank
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
variable {Q K : ℕ} {P U : Type}

theorem selectedAmortizedInitializedDyadicPublication_exec (body : P → Pr P PackedTranspose.tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    let p := Sizes.p m
    let s := Sizes.s m i
    ∀ (u target : ℕ) (htarget : target ≤ ct*p) (W : ℕ) (hW : 1 ≤ W) (b V : ℕ),
    V ≤ cV*p → 2^b ≤ Sizes.T m →
    let width := amortizedCoreWidth ct p
    let radius := localityDepth p target*PhaseCellBand.width p u
    let g := gatherPublicationClass s width radius (width+2*radius)
    let hw : 0 < width := (amortizedCoreWidth_bounds ct p u target (by have := h.thirteen_le_p; omega) htarget).1
    let a := Nat.clog 2 g.indices.length
    ∀
    (hbits : a+b < V) (hfit : (g.length*W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (exponent packet pad tmp saved : Fin PackedTranspose.tapeCount)
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^b)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (batches : List (List (List GaussianInt)))
    (hrows : List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows) (coreBulkIndices s width (PhaseCellBand.width p u) (localityDepth p target)) batches)
    (depth : ℕ)
    (v : HS PackedTranspose.tapeCount Q (prime+K) U) (S : Stacks PackedTranspose.tapeCount (prime+K))
    (hworkspace : PublicationWorkspaceReady (fun i => i) exponent packet pad tmp saved a b g.length W V S)
    (hpadOff : ∀ r ∈ [exponent,packet,pad,tmp,saved], r ∉ countedPublicationHeaderRegisters)
    (hsourceA : (S.R replicaCount).length = 2^b)
    (hsourceB : (S.R realRows).length = g.indices.length)
    (hsourceC : (S.R packetWidth).length = g.length*W)
    (hheaderBlank : ∀ i ∈ [(84 : Fin 117),85,97,98,102,40,41,42,43,44,45], S.R (headerReg i) = [])
    (hsrc : S.R (extra 1) = (batches.map (fun rows => cstream (prime+K) W rows.flatten)).flatten)
    (dst : Fin PackedTranspose.tapeCount) (pub : PreparedPublicationPlan PackedTranspose.tapeCount (extra 1) dst)
    (clock lineRows : Fin PackedTranspose.tapeCount)
    (hports : (pub.support++[extra 1,dst,clock,lineRows]).Nodup)
    (hpubOff : ∀ r ∈ pub.support++[extra 1,dst,clock,lineRows], r ∉ countedPublicationHeaderRegisters)
    (ambient : Fin Fs.length → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*W)
    (outputTail borrowed : List (Fin (prime+K+4)))
    (pubReady : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W (2^a-g.indices.length) borrowed S)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s),
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ (n : ℝ) ≤ (2*(Sizes.T m : ℝ)+(2220+100*cV : ℕ)*(2^b*(s*W) : ℕ)+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (2^b*(s*W) : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (2*Sizes.T m+(3720+100*cV+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W)))) depth
        (.seq (.seq countedPublicationHeadersProgram (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (PackedTranspose.program hstates)) (pub.replicaProgram clock lineRows))) (clearWords countedPublicationHeaderRegisters)) (Host.mk v S) n (Host.mk v' F) ∧
      F.R (extra 1) = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ extra 1 → r ≠ dst → F.R r = S.R r := by
  dsimp only
  filter_upwards [selectedAmortizedDyadicPublication_exec body hstates ct cV,selectedAmortizedCoreGeometry ct] with m hpub hgeometry
  intro h i _ u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hpadReg
    Fs hFs J batches hrows depth v S hworkspace hpadOff hsourceA hsourceB hsourceC hheaderBlank hsrc
    dst pub clock lineRows hports hpubOff ambient hambient outputTail borrowed pubReady hdst hclock hline
  let p := Sizes.p m
  let s := Sizes.s m i
  let width := amortizedCoreWidth ct p
  let radius := localityDepth p target*PhaseCellBand.width p u
  let g := gatherPublicationClass s width radius (width+2*radius)
  let a := Nat.clog 2 g.indices.length
  let M := countedPublicationHeadersState b g.indices.length (g.length*W) V S
  have hread (r : Fin PackedTranspose.tapeCount) (hr : r ∉ countedPublicationHeaderRegisters) : M.R r = S.R r :=
    countedPublicationHeadersState_off b g.indices.length (g.length*W) V S r hr
  obtain ⟨v₁,n₁,hu₁,hn₁,ready,he₁⟩ := countedPublicationHeaders_exec_within body exponent packet pad tmp saved
    b g.indices.length g.length W V depth hbits hfit v S hworkspace hpadOff hsourceA hsourceB hsourceC hheaderBlank
  have pubReadyM := pubReady.of_frame (F := M) (by
    intro r hr
    exact hread r (hpubOff r (List.mem_append_left _ hr)))
  have hsrcOff := hpubOff (extra 1) (by simp)
  have hdstOff := hpubOff dst (by simp)
  obtain ⟨lines,v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,hgood,hi,ho,hl,hframe⟩ := hpub h i u target htarget W hW b V hV hreplicas
    hbits hfit hA exponent packet pad tmp saved hpadReg Fs hFs J batches hrows depth v₁ M
    ready.exponent ready.packet ready.pad ready.tmp ready.saved ready.a ready.b ready.seed ready.zero ready.width
    ready.blank ready.stages ready.left ready.fresh (by rw [hread _ hsrcOff]; exact hsrc) ready.count ready.codec
    dst pub clock lineRows hports ambient hambient outputTail borrowed pubReadyM
    (by rw [hread _ hdstOff]; exact hdst)
    (by rw [hread _ (hpubOff clock (by simp))]; exact hclock)
    (by rw [hread _ (hpubOff lineRows (by simp))]; exact hline)
  have hF : F = {M with R := Function.update (Function.update M.R (extra 1) []) dst (lines.flatten++outputTail)} := by
    refine Stacks.ext hi ho hl ?_
    funext r
    by_cases hr : r = dst
    · subst r; simp only [Function.update_self,hd]
    · by_cases hs' : r = extra 1
      · subst r
        change F.R (extra 1) = Function.update (Function.update M.R (extra 1) []) dst _ (extra 1)
        rw [Function.update_of_ne hr,Function.update_self,hs]
      · change F.R r = Function.update (Function.update M.R (extra 1) []) dst _ r
        rw [Function.update_of_ne hr,Function.update_of_ne hs']
        exact hframe r hs' hr
  have hblank : ∀ r ∈ countedPublicationHeaderRegisters, S.R r = [] := by
    intro r hr
    simp only [countedPublicationHeaderRegisters,publicationExponentRegisters,publicationBinaryRegisters,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with (rfl | rfl) | (rfl | rfl | rfl) <;> apply hheaderBlank <;> simp
  obtain ⟨v',hu₃,he₃⟩ := retireCountedPublicationHeaders_exec_within body b g.indices.length (g.length*W) V
    (extra 1) dst hsrcOff hdstOff [] (lines.flatten++outputTail) S hblank depth v₂
  have he₂' := he₂.cast rfl (congrArg (Host.mk v₂) hF)
  have heTotal := execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ 0
    (execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ he₁ he₂') he₃
  obtain ⟨hw,hpow,hr,hroom,_⟩ := hgeometry h i u target htarget
  have hp : 1 ≤ p := by have := h.thirteen_le_p; omega
  have hps : p ≤ s := by
    have hpower : p ≤ p^8 := by simpa only [pow_one] using pow_le_pow_right' hp (show 1 ≤ 8 by decide)
    change p^8 ≤ width at hpow
    change 3*width+PhaseCellBand.width p u ≤ s at hroom
    omega
  have hlength : g.length = width := Nat.add_sub_cancel_right _ _
  have hspan : g.length ≤ s := by
    rw [hlength]
    change 3*width+PhaseCellBand.width p u ≤ s at hroom
    omega
  let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
  have hrowsVolume : g.indices.length*g.length ≤ s := by
    have hv := windows.gaps_volume 1
    simp only [windows,scatterVolume,PublicationWindows.gaps_length,coreSubsetPublicationWindows,
      PublicationWindows.restrict,List.length_map,Nat.mul_one] at hv
    omega
  obtain ⟨hheaderTime,hheaderStock⟩ := dyadicPublicationHeaderCosts_le g.indices.length b s g.length W V p cV
    hrowsVolume (by rw [hlength]; exact hw) hspan hW hp hps hV
  obtain ⟨hexponentTime,hexponentStock⟩ := dyadicPublicationExponentCosts_le g.indices.length b s g.length W
    hrowsVolume (by rw [hlength]; exact hw) (hp.trans hps) hW
  have hprepTime : countedPublicationHeadersCost b g.indices.length (g.length*W) V+
      (2*(b+Nat.clog 2 g.indices.length+3*V)+11) ≤ (520+100*cV)*(2^b*(s*W)) := by
    unfold countedPublicationHeadersCost
    nlinarith only [hheaderTime,hexponentTime]
  have hprepStock : 2*countedPublicationHeadersCost b g.indices.length (g.length*W) V ≤
      (520+100*cV)*(2^b*(s*W)) := by
    unfold countedPublicationHeadersCost
    nlinarith only [hheaderStock,hexponentStock]
  have hne := pub.src_ne_dst
  refine ⟨lines,v',_,n₁+n₂+(2*(b+Nat.clog 2 g.indices.length+3*V)+11),hu₃.trans (hu₂.trans hu₁),?_,heTotal.mono (by
    intro z state hz
    nlinarith only [hz,hprepStock]),?_,?_,hgood,rfl,rfl,rfl,?_⟩
  · have hn₁Real := Nat.cast_le (α := ℝ).mpr hn₁
    simp only [countedPublicationHeadersCost,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hn₁Real hn₂ ⊢
    have hheaderReal := Nat.cast_le (α := ℝ).mpr hprepTime
    simp only [countedPublicationHeadersCost,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hheaderReal
    linarith only [hn₁Real,hn₂,hheaderReal]
  · exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
  · exact Function.update_self _ _ _
  · intro r hs hd
    exact (Function.update_of_ne hd _ _).trans (Function.update_of_ne hs _ _)

end IntegerMultBounds.MathlibTM2.Cost
