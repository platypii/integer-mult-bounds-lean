module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGlobals
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies

/-! Produce the fixed format rulers from retained counters, then construct the
ordinary setup input by executing ruler copying and global scalar conversion. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
noncomputable section
variable {T A D p u l target s t B W N radius width Vg Vr : ℕ}

def rulerCopies (T : ℕ) (src : Fin 3 → Fin T) : List (Fin (MachineTapes T) × Fin (MachineTapes T)) :=
  List.ofFn fun f => (unarySource T (src f),rulers T f)

def rulersLoaded (src : Fin 3 → Fin T) (S : Stacks (MachineTapes T) A) : Stacks (MachineTapes T) A :=
  {S with R := unaryCopiesR (fun k => (S.R k).length) S.R (rulerCopies T src)}

theorem rulerCopies_nodup (T : ℕ) (src : Fin 3 → Fin T) : ((rulerCopies T src).map Prod.snd).Nodup := by
  rw [rulerCopies,List.map_ofFn,List.nodup_ofFn]
  exact rulers_injective T

theorem rulersLoaded_header (src : Fin 3 → Fin T) (S : Stacks (MachineTapes T) A) (r : Role)
    (hr : ∀ f, r ≠ .ruler f) :
    (rulersLoaded src S).R (fullHeader T r) = S.R (fullHeader T r) := by
  apply unaryCopiesR_off
  intro q hq
  obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hq
  exact ((fullHeader_injective T).ne (hr f)).symm

theorem rulersLoaded_unarySource (src : Fin 3 → Fin T) (S : Stacks (MachineTapes T) A) (k : Fin T) :
    (rulersLoaded src S).R (unarySource T k) = S.R (unarySource T k) := by
  apply unaryCopiesR_off
  intro q hq
  obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hq
  exact fullHeader_ne_bank id (.ruler f) k

theorem rulersLoaded_routing (src : Fin 3 → Fin T) (S : Stacks (MachineTapes T) A) (i : Fin tapeCount) :
    (rulersLoaded src S).R (Fin.natAdd ((T+headerCount)+175) i) = S.R (Fin.natAdd ((T+headerCount)+175) i) := by
  apply unaryCopiesR_off
  intro q hq
  obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hq
  exact prefix_ne_routing (Fin.castAdd 175 (header T (.ruler f))) i

theorem rulersLoaded_length (src : Fin 3 → Fin T) (S : Stacks (MachineTapes T) A)
    (hblank : ∀ f, S.R (rulers T f) = []) (f : Fin 3) :
    ((rulersLoaded src S).R (rulers T f)).length = (S.R (unarySource T (src f))).length := by
  change (unaryCopiesR (fun k => (S.R k).length) S.R (rulerCopies T src) (rulers T f)).length = _
  rw [unaryCopiesR_at _ _ _ (rulerCopies_nodup T src)
    (unarySource T (src f),rulers T f) (List.mem_ofFn.mpr ⟨f,rfl⟩)]
  simp only [hblank,List.append_nil,List.length_replicate]

theorem prepareRulers_exec {Q : ℕ} {P U : Type}
    (body : P → Pr P (MachineTapes T) Q A U)
    (src : Fin 3 → Fin T) (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hvalues : ∀ f, (S.R (unarySource T (src f))).length = formatWidths B Vg Vr f)
    (htmp : S.R (seedReg T (.z 0)) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyUnaryHeaders (seedReg T (.z 0)) (rulerCopies T src))
        (Host.mk v S) (4*(B+Vg+Vr)+13) (Host.mk v' (rulersLoaded src S)) := by
  have hregs : ∀ q ∈ rulerCopies T src, [q.1,q.2,seedReg T (.z 0)].Nodup := by
    intro q hq
    obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hq
    have hs : unarySource T (src f) ≠ rulers T f := (fullHeader_ne_bank id (.ruler f) (src f)).symm
    have ht := unarySource_ne_seed T (src f) (.z 0)
    have hr : rulers T f ≠ seedReg T (.z 0) := fullHeader_ne_seed T (.ruler f) (.z 0)
    simp [List.nodup_cons,hs,ht,hr]
  have hsep : ∀ q ∈ rulerCopies T src, ∀ r ∈ rulerCopies T src, q.2 ≠ r.1 := by
    intro q hq r hr
    obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hq
    obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hr
    exact fullHeader_ne_bank id (.ruler f) (src g)
  have hcost : copyUnaryHeadersCost (fun k => (S.R k).length) (rulerCopies T src) = 4*(B+Vg+Vr)+13 := by
    simp [copyUnaryHeadersCost,rulerCopies,List.ofFn_succ,hvalues,formatWidths]
    omega
  obtain ⟨v',hu,he⟩ := copyUnaryHeaders_exec (body := body) (seedReg T (.z 0)) (rulerCopies T src)
    hregs hsep (fun k => (S.R k).length) v S (fun _ _ => rfl) htmp
  exact ⟨v',hu,by simpa only [hcost,rulersLoaded] using he⟩

def baselineProgram {Q : ℕ} {P U : Type} (src : Fin 11 → Fin T) (widthSource : Fin T)
    (widths : Fin 3 → Fin T) : Pr P (MachineTapes T) Q A U :=
  .seq (copyUnaryHeaders (seedReg T (.z 0)) (rulerCopies T widths))
    (binaryHeaderBank (unarySource T widthSource) (seedReg T (.z 0)) (seedReg T (.z 1))
      (seedReg T (.z 2)) (globalCopies T src))

def baselineLoaded (D : ℕ) (src : Fin 11 → Fin T) (widths : Fin 3 → Fin T)
    (S : Stacks (MachineTapes T) A) : Stacks (MachineTapes T) A :=
  globalsLoaded D src (rulersLoaded widths S)

theorem baselineSetupInput (src : Fin 11 → Fin T) (widths : Fin 3 → Fin T) (S : Stacks (MachineTapes T) A)
    (hvalues : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hwidths : ∀ f, (S.R (unarySource T (widths f))).length = formatWidths B Vg Vr f)
    (hblank : ∀ f, S.R (rulers T f) = [])
    (howned : ∀ r ∈ ownedRoles, S.R (fullHeader T r) = [])
    (hzero : S.R (fullHeader T .zero) = [])
    (hrouting : ∀ i, S.R (Fin.natAdd ((T+headerCount)+175) i) = []) :
    SetupInput T A D p u l target s t B W N radius width Vg Vr (baselineLoaded D src widths S) := by
  apply setupInput_of_globalsLoaded src (rulersLoaded widths S)
  · intro i
    rw [rulersLoaded_unarySource]
    exact hvalues i
  · intro f
    rw [rulersLoaded_length widths S hblank f]
    exact hwidths f
  · intro r hr
    rw [rulersLoaded_header widths S r (fun f => (retained_ne_owned (.ruler f) rfl r hr).symm)]
    exact howned r hr
  · rw [rulersLoaded_header widths S .zero (by intro f h; cases h)]
    exact hzero
  · intro i
    rw [rulersLoaded_routing]
    exact hrouting i

/-- Both retained scalar words and consumer rulers are actual outputs of one
program, starting from ordinary prefix counters and fresh header storage. -/
theorem prepareBaseline_exec_within {Q : ℕ} {P U : Type}
    (body : P → Pr P (MachineTapes T) Q A U)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (widths : Fin 3 → Fin T)
    (hwidthOff : ∀ i, src i ≠ widthSource)
    (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hwidth : (S.R (unarySource T widthSource)).length = D)
    (hvalues : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hwidths : ∀ f, (S.R (unarySource T (widths f))).length = formatWidths B Vg Vr f)
    (hblank : ∀ i, S.R (globals T i) = [])
    (hrouting : ∀ i, S.R (Fin.natAdd ((T+headerCount)+175) i) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (4*(B+Vg+Vr)+13)+globalConversionCost D p u l target s t B W N radius width ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*((4*(B+Vg+Vr)+13)+globalConversionCost D p u l target s t B W N radius width)) depth
        (baselineProgram src widthSource widths) (Host.mk v S) n (Host.mk v' (baselineLoaded D src widths S)) := by
  obtain ⟨v₁,hu₁,he₁⟩ := prepareRulers_exec body widths v S hwidths (hrouting _)
  obtain ⟨v₂,n,hu₂,hn,he₂⟩ := prepareGlobals_exec_within (D := D) (p := p) (u := u) (l := l) (target := target)
    (s := s) (t := t) (B := B) (W := W) (N := N) (radius := radius) (width := width) body src widthSource hwidthOff v₁ (rulersLoaded widths S)
    (by simpa only [rulersLoaded_unarySource] using hwidth)
    (by intro i; simpa only [rulersLoaded_unarySource] using hvalues i)
    (by
      intro i
      rw [show globals T i = fullHeader T (.scalar i) from rfl,
        rulersLoaded_header widths S (.scalar i) (by intro f h; cases h)]
      exact hblank i)
    (by exact (rulersLoaded_routing widths S _).trans (hrouting _))
    (by exact (rulersLoaded_routing widths S _).trans (hrouting _)) 0
  have he := Exec.seq he₁ he₂.toExec
  have hnative : mnNativePushBound 3 (baselineProgram (Q := Q) (P := P) (A := A) (U := U) src widthSource widths) :=
    ⟨mnNativePushBound_mono (by decide) (copyUnaryHeaders_native _ _),binaryHeaderBank_native _ _ _ _ _⟩
  exact ⟨v₂,_,hu₂.trans hu₁,Nat.add_le_add_left hn _,
    mn_native_exec_within he 3 hnative depth _ (by omega)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
