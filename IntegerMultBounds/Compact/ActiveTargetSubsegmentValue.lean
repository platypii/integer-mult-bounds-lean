import IntegerMultBounds.Machine.BinaryPackedLateData
import IntegerMultBounds.Machine.CountedIdealToggle

/-! The guarded packed kernel acts on the n*q active bits only. Low and high
spectators are retained independently of the compact capacity H. -/
namespace IntegerMultBounds.Compact.ActiveTargetSubsegmentValue
noncomputable section
open IntegerMultBounds.Machine
open Radix

/-- Little-endian reconstruction of one containing target slot. -/
def splice (rho m : ℕ) (lo mid hi : ℤ) : ℤ := lo+2^rho*(mid+2^m*hi)

theorem active_fits (q n rho : ℕ) (hr : rho ≤ q) : rho+n*q ≤ (n+1)*q := by nlinarith

theorem remaining_width (q n rho : ℕ) (hr : rho ≤ q) :
    rho+n*q+(q-rho)=(n+1)*q := by rw [Nat.add_mul]; omega

/-- The highest selected bit lies in the remaining high spectator segment. -/
theorem highest_position (q n rho : ℕ) (hr : rho < q) :
    rho+n*q < (n+1)*q ∧ 0 < q-rho := by
  constructor
  · nlinarith
  · omega

def earlyTarget {S : Type*} (q b n rho : ℕ) (x : BinaryPackedEarlyData.State q b n (ℤ×ℤ×S)) :=
  splice rho (n*q) x.2.2.1 x.1.val x.2.2.2.1

def lateTarget {S : Type*} (q b n rho : ℕ) (x : BinaryPackedLateData.State q b n (ℤ×ℤ×S)) :=
  splice rho (n*q) x.2.2.2.1 x.1.val x.2.2.2.2.1

theorem early_good {S : Type*} (q b n rho : ℕ) (Z : List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : BinaryPackedEarlyData.State q b n (ℤ×ℤ×S)) (ds : List DigitState)
    (hc : ds.map DigitState.z=Z.map PowerTwo.ctrl)
    (hv : (x.1.val : ℤ)=pack ((2 : ℤ)^q) (ds.map DigitState.v))
    (hw : (x.2.1.val : ℤ)=pack ((2 : ℤ)^b) (ds.map DigitState.w))
    (hg : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    earlyTarget q b n rho (BinaryPackedEarlyData.run q b n Z hb hbq x)=
      splice rho (n*q) x.2.2.1 (pack ((2 : ℤ)^q) (ds.map (fun d => toggle d.v d.z))) x.2.2.2.1 ∧
    (BinaryPackedEarlyData.run q b n Z hb hbq x).2=x.2 := by
  have h := BinaryPackedEarlyData.good_value q b n Z hb hbq hZ x ds hc hv hw hg
  have ht := congrArg Prod.fst h
  dsimp only at ht
  constructor
  · unfold earlyTarget splice
    rw [BinaryPackedEarlyData.spectator,ht]
  · exact Prod.ext (BinaryPackedEarlyData.good_temp q b n Z hb hbq hZ x ds hc hv hw hg)
      (BinaryPackedEarlyData.spectator q b n Z hb hbq x)

theorem late_good {S : Type*} (q b n rho : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (X : List Bool) (hX : X.length=n)
    (x : BinaryPackedLateData.State q b n (ℤ×ℤ×S)) (ds : List LateDigitState)
    (hc : ds.map LateDigitState.x=X.map PowerTwo.ctrl)
    (hv : (x.1.val : ℤ)=pack ((2 : ℤ)^q) (ds.map LateDigitState.v))
    (hw : (x.2.1.val : ℤ)=pack ((2 : ℤ)^b) (ds.map LateDigitState.w))
    (hu : (x.2.2.1.val : ℤ)=pack ((2 : ℤ)^b) (ds.map LateDigitState.u))
    (hg : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    lateTarget q b n rho (BinaryPackedLateData.run q b n hb hbq X hX x)=
      splice rho (n*q) x.2.2.2.1 (pack ((2 : ℤ)^q) (ds.map (fun d => toggle d.v d.x))) x.2.2.2.2.1 ∧
    (BinaryPackedLateData.run q b n hb hbq X hX x).2=x.2 := by
  have h := BinaryPackedLateData.good_value q b n hb hbq X hX x ds hc hv hw hu hg
  have ht := congrArg Prod.fst h
  dsimp only at ht
  constructor
  · unfold lateTarget splice
    rw [BinaryPackedLateData.spectator,ht]
  · apply Prod.ext
    · apply Fin.ext
      have hw' := congrArg (fun z => z.2.1) h
      dsimp only at hw'
      exact_mod_cast hw'
    · exact Prod.ext (BinaryPackedLateData.restored_control q b n hb hbq X hX x)
        (BinaryPackedLateData.spectator q b n hb hbq X hX x)

theorem toggle_projections (ds : List DigitState) :
    toggleList (ds.map DigitState.v) (ds.map DigitState.z)=ds.map (fun d => toggle d.v d.z) := by
  induction ds <;> simp_all [toggleList]

theorem guarded_target_bound (q b : ℕ) (hq : 1≤q) (d : DigitState)
    (hg : d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) : 0≤d.v ∧ d.v<(2 : ℤ)^q := by
  have hb : 0 < (2 : ℤ)^b := by positivity
  have he : (2 : ℤ)^q=2*(2 : ℤ)^(q-1) := by
    rw [←pow_succ']; congr 1; omega
  rw [he]
  obtain ⟨hlo,hhi,_,_,_⟩ := hg
  omega

/-- Guarded digit-level toggles are exactly the literal stride-q XOR word. -/
theorem early_toggle_word (q b : ℕ) (hq : 1≤q) (V Z : List Bool) (ds : List DigitState)
    (hV : V.length=Z.length*q) (hc : ds.map DigitState.z=Z.map PowerTwo.ctrl)
    (hv : (Counter.value V : ℤ)=pack ((2 : ℤ)^q) (ds.map DigitState.v))
    (hg : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    pack ((2 : ℤ)^q) (ds.map (fun d => toggle d.v d.z))=
      (Counter.value (CountedIdealToggle.word q V Z) : ℤ) := by
  have hl : ds.length=Z.length := by
    have h := congrArg List.length hc
    simpa only [List.length_map] using h
  have hd : Radix.Bounded ((2 : ℤ)^q) (ds.map DigitState.v) := by
    intro v hv
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hv
    exact guarded_target_bound q b hq d (hg d hd)
  have hdigits := digits_pack ((2 : ℤ)^q) (by positivity) _ hd
  simp only [List.length_map,hl] at hdigits
  rw [CountedIdealToggle.value q hq V Z hV,hv,hdigits,←hc,toggle_projections]


theorem late_toggle_word (q b : ℕ) (hq : 1≤q) (V X : List Bool) (ds : List LateDigitState)
    (hV : V.length=X.length*q) (hc : ds.map LateDigitState.x=X.map PowerTwo.ctrl)
    (hv : (Counter.value V : ℤ)=pack ((2 : ℤ)^q) (ds.map LateDigitState.v))
    (hg : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    pack ((2 : ℤ)^q) (ds.map (fun d => toggle d.v d.x))=
      (Counter.value (CountedIdealToggle.word q V X) : ℤ) := by
  let es := ds.map (fun d => (⟨d.v,d.w,d.x⟩ : DigitState))
  have h := early_toggle_word q b hq V X es hV (by simpa [es,Function.comp_def] using hc)
    (by simpa [es,Function.comp_def] using hv) (by
      intro e he
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
      have hh := hg d hd
      exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.2.2⟩)
  simpa [es,Function.comp_def] using h

end
end IntegerMultBounds.Compact.ActiveTargetSubsegmentValue
