module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationGroups
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaPublication

/-! Ordinary grouped-publication inputs, independent of the numerical archive.
An output-only producer preserves them by one explicit register-separation fact. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.GroupedPublication
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q K c d s width W : ℕ}

noncomputable def Reads (g : CorePublicationClass s width)
    (route : ArchiveTilePlan t₀ T Q c d (g.length*W)) {dst : Fin T}
    (pub : PreparedPublicationPlan T route.src dst)
    (clock lineRows count savedCount rowWidth archive saved tmp r : Fin T) : Prop :=
  r ∈ route.support ∨ r ∈ pub.support ∨
    r ∈ [count,savedCount,rowWidth,archive,saved,tmp,route.src,dst,clock,lineRows]

structure Ready (g : CorePublicationClass s width) (hw : 0 < width)
    (route : ArchiveTilePlan t₀ T Q c d (g.length*W)) {dst : Fin T}
    (pub : PreparedPublicationPlan T route.src dst)
    (clock lineRows count savedCount rowWidth archive saved tmp : Fin T)
    (N : ℕ) (ambient : Fin N → List (Fin (prime+K+4)))
    (outputTail borrowed : List (Fin (prime+K+4))) (S : Stacks T (prime+K)) : Prop where
  bank : route.BankReady S
  publication : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
    W ((2^d)^c-g.indices.length) borrowed S
  count : (S.R count).length = g.indices.length
  rowWidth : (S.R rowWidth).length = N*(g.length*W)
  fresh : ∀ r ∈ [savedCount,archive,saved,tmp], S.R r = []
  sourceBlank : S.R route.src = []
  destination : S.R dst = (List.ofFn ambient).flatten++outputTail
  clock : (S.R clock).length = N
  line : (S.R lineRows).length = s

variable {g : CorePublicationClass s width} {hw : 0 < width}
  {route : ArchiveTilePlan t₀ T Q c d (g.length*W)} {dst : Fin T}
  {pub : PreparedPublicationPlan T route.src dst}
  {clock lineRows count savedCount rowWidth archive saved tmp : Fin T} {N : ℕ}

  {ambient : Fin N → List (Fin (prime+K+4))}
  {outputTail borrowed : List (Fin (prime+K+4))} {S F : Stacks T (prime+K)}

theorem Ready.frame
    (h : Ready g hw route pub clock lineRows count savedCount rowWidth archive saved tmp
      N ambient outputTail borrowed S) (hL : F.L = S.L)
    (hR : ∀ r, Reads g route pub clock lineRows count savedCount rowWidth archive saved tmp r →
      F.R r = S.R r) :
    Ready g hw route pub clock lineRows count savedCount rowWidth archive saved tmp
      N ambient outputTail borrowed F := by
  have control (r : Fin T)
      (hr : r ∈ [count,savedCount,rowWidth,archive,saved,tmp,route.src,dst,clock,lineRows]) :=
    hR r (Or.inr (Or.inr hr))
  refine ⟨h.bank.of_frame (fun r hr => hR r (Or.inl hr)) hL,
    h.publication.of_frame (fun r hr => hR r (Or.inr (Or.inl hr))),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [control count (by simp)]; exact h.count
  · rw [control rowWidth (by simp)]; exact h.rowWidth
  · intro r hr
    rw [control r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      tauto)]
    exact h.fresh r hr
  · rw [control route.src (by simp)]; exact h.sourceBlank
  · rw [control dst (by simp)]; exact h.destination
  · rw [control clock (by simp)]; exact h.clock
  · rw [control lineRows (by simp)]; exact h.line

theorem Ready.after_output
    (h : Ready g hw route pub clock lineRows count savedCount rowWidth archive saved tmp
      N ambient outputTail borrowed S)
    (source : Fin T) (word : List (Fin (prime+K+4)))
    (hoff : ∀ r, Reads g route pub clock lineRows count savedCount rowWidth archive saved tmp r → r ≠ source) :
    Ready g hw route pub clock lineRows count savedCount rowWidth archive saved tmp
      N ambient outputTail borrowed {S with R := Function.update S.R source (word++S.R source)} := by
  apply h.frame
  · rfl
  · intro r hr
    exact Function.update_of_ne (hoff r hr) _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.GroupedPublication
