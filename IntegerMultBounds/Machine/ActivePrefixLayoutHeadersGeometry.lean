import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersBudget
import IntegerMultBounds.Machine.ActivePrefixLayoutAbsorption
import IntegerMultBounds.Machine.ActivePrefixParityOnlyBank

/-! The constructed numeric headers are exactly those used by the unchanged
active-prefix selected/correction and compact parity/negative consumers. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutHeadersGeometry
open ActivePrefixLayoutHeadersData
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixLayoutGeometry CompactActiveTargetGeometry

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)

def inputs : Inputs where
  H := s.H
  B := s.B
  F := s.F
  before := p.before
  after := p.after
  m := p.n*p.q
  w := p.n*p.b
  q := p.q
  b := p.b
  n := p.n
  rho := p.rho
  sourceOffset := offset
  rows := rows
  payload := s.payload

def room (mode : Mode) := match mode with | .compactAfter => p.after | _ => p.before

theorem target_values (hfit : offset+p.f*p.q≤p.before) (i : Fin 8) :
    values .target (inputs s p offset rows) (Fin.castAdd 2 i)=
      ActivePrefixSelectedOffsetBank.values (targetShape s p offset hfit) i := by
  have hf := p.hnf
  fin_cases i <;> simp [values,inputs,prefixWidth,targetStart,sourceStart,
    ActivePrefixSelectedOffsetBank.values,targetShape,targetWidth,tStart,hf]

theorem compact_before_values (hfit : offset+p.f*p.q≤p.before) (i : Fin 8) :
    values .compactBefore (inputs s p offset rows) (Fin.castAdd 2 i)=
      ActivePrefixParityOnlyBank.values (backBeforeShape s p offset hfit) i := by
  have hf := p.hnf
  fin_cases i <;> simp [values,inputs,prefixWidth,targetStart,sourceStart,
    ActivePrefixParityOnlyBank.values,backBeforeShape,backWidth,targetWidth,hf,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem compact_after_values (hfit : offset+p.f*p.q≤p.after) (i : Fin 8) :
    values .compactAfter (inputs s p offset rows) (Fin.castAdd 2 i)=
      ActivePrefixParityOnlyBank.values (backAfterShape s p offset hfit) i := by
  have hf := p.hnf
  fin_cases i <;> simp [values,inputs,prefixWidth,targetStart,sourceStart,
    ActivePrefixParityOnlyBank.values,backAfterShape,backWidth,targetWidth,hf,Nat.add_assoc]

theorem target_suffix : suffix .target (inputs s p offset rows)=targetSuffix s p.after := by
  simp only [suffix,inputs,exponent,targetSuffix,pow_add]
  ring

theorem compact_suffix (mode : Mode) (hm : mode≠.target) :
    suffix mode (inputs s p offset rows)=compactSuffix s (p.n*p.b) := by
  cases mode <;> simp_all [suffix,inputs,exponent,compactSuffix,Nat.mul_comm]

theorem originals_bound (mode : Mode) (hfit : offset+p.f*p.q≤room s p mode)
    (hrows : 0<rows) (hrecord : s.bits+1≤s.payload) :
    ∀ i, originalValues (inputs s p offset rows) i≤rows*s.recordWidth := by
  have hp : 0<s.payload := by omega
  have hpay : s.payload≤rows*s.recordWidth := by
    have h₀ : s.payload≤s.recordWidth := Nat.le_mul_of_pos_left _ (by positivity)
    exact h₀.trans (Nat.le_mul_of_pos_left _ hrows)
  have hrow : rows≤rows*s.recordWidth := Nat.le_mul_of_pos_right _ (by unfold Shape.recordWidth; positivity)
  have hbits : s.bits≤rows*s.recordWidth := by omega
  have ha := p.activeSize
  have hw := p.compactFits
  have hb := p.hbq
  have hbp := p.hb
  have hn := p.hnf
  have hr := p.hr
  have hqpos : 0<p.q := by omega
  have hnf : p.q≤p.f*p.q := Nat.le_mul_of_pos_left _ (by omega)
  have hnq : p.n≤p.n*p.q := Nat.le_mul_of_pos_right _ hqpos
  have hroom : room s p mode≤s.bits := by cases mode <;> simp only [room] <;> unfold Shape.bits <;> omega
  have hoff : offset≤s.bits := by omega
  have hq : p.q≤s.bits := by omega
  have hfields : s.H≤s.bits ∧ s.B≤s.bits ∧ s.F≤s.bits ∧ p.before≤s.bits ∧
      p.after≤s.bits ∧ p.n*p.q≤s.bits := by unfold Shape.bits; omega
  intro i; fin_cases i
  all_goals simp [originalValues,inputs]
  all_goals omega

theorem suffix_bound (mode : Mode) (hrows : 0<rows) :
    suffix mode (inputs s p offset rows)≤rows*s.recordWidth := by
  have ha := p.activeSize
  have hexp : exponent mode (inputs s p offset rows)≤s.bits := by
    cases mode <;> simp only [exponent,inputs] <;> unfold Shape.bits <;> omega
  have hpow := Nat.pow_le_pow_right (by decide : 0<2) hexp
  have hs : suffix mode (inputs s p offset rows)≤s.recordWidth := by
    change s.payload*2^exponent mode (inputs s p offset rows)≤2^s.bits*s.payload
    nlinarith only [hpow]
  exact hs.trans (Nat.le_mul_of_pos_left _ hrows)

end IntegerMultBounds.Machine.ActivePrefixLayoutHeadersGeometry
