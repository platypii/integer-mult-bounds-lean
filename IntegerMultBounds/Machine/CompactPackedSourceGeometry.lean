import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatValue
import IntegerMultBounds.Machine.BinaryPackedOffsetData

/-! Exact source-field factorization inside one fixed physical gap. A selected
contiguous source occupies u bits, with all preceding/following bits retained
as spectators. The coordinate conversions preserve literal serialized order. -/
namespace IntegerMultBounds.Machine.CompactPackedSourceGeometry
open RadixRangePadding (index)
open RecursiveInterchangeRows (pack pack_val)
open BinaryAddressOffsetRepeatData (copies expanded)

def prefixRange (before : ℕ) := 2^before
def suffixRange (after : ℕ) := 2^after

theorem gap_range (before u after : ℕ) :
    2^(before+u+after)=prefixRange before*2^u*suffixRange after := by
  simp only [prefixRange,suffixRange,pow_add]

def sourceAddress (w u after B i : ℕ) := (((i/B)/2^w)/suffixRange after)%2^u

/-- Reading a middle source field from the actual serialized array address
recovers precisely its value, independently of both fronts and every spectator.
The divisions remove actual trailing payload/back/source-suffix fields. -/
theorem source_address (P w before u after B : ℕ)
    (p : Fin P) (front back : Fin (2^w))
    (h : Fin (prefixRange before)) (y : Fin (2^u)) (l : Fin (suffixRange after)) (j : Fin B) :
    sourceAddress w u after B (index p front (pack (pack h y) l) back j).val=y.val := by
  have hB : 0<B := Nat.zero_lt_of_lt j.isLt
  have hF : 0<2^w := by positivity
  have hL : 0<suffixRange after := by unfold suffixRange; positivity
  have he : ((p.val*2^w+front.val)*(prefixRange before*2^u*suffixRange after)+
      ((h.val*2^u+y.val)*suffixRange after+l.val)) =
      (((p.val*2^w+front.val)*prefixRange before+h.val)*2^u+y.val)*suffixRange after+l.val := by ring
  have strip (a d e : ℕ) (hd : 0<d) (he : e<d) : (a*d+e)/d=a := by
    rw [Nat.mul_comm a d,Nat.mul_add_div hd,Nat.div_eq_of_lt he,Nat.add_zero]
  unfold sourceAddress
  simp only [index,pack_val]
  rw [strip _ B j.val hB j.isLt,strip _ (2^w) back.val hF back.isLt,he,
    strip _ (suffixRange after) l.val hL l.isLt]
  rw [Nat.mul_comm _ (2^u),Nat.mul_add_mod,Nat.mod_eq_of_lt y.isLt]

/-- The index read by the offset machine after the physical field swap.
Its ordering retains every preceding bit and the dirty back coordinate. -/
theorem rotation_row (P w before u after : ℕ)
    (p : Fin P) (back : Fin (2^w))
    (h : Fin (prefixRange before)) (y : Fin (2^u)) (l : Fin (suffixRange after)) :
    (BinaryPackedOffsetData.rowIndex p back (pack (pack h y) l)).val=
      (((p.val*2^w+back.val)*prefixRange before+h.val)*2^u+y.val)*suffixRange after+l.val := by
  simp only [BinaryPackedOffsetData.rowIndex,pack_val]
  ring

/-- The exact physically repeated table word, read at the actual rotation row.
This connects source-axis placement to the generic paid repetition engine. -/
theorem repeated_field (P w before u after W : ℕ) (table : List (List Bool))
    (hu : BlockRotationData.Uniform W table) (hlen : table.length=2^u)
    (p : Fin P) (back : Fin (2^w))
    (h : Fin (prefixRange before)) (y : Fin (2^u)) (l : Fin (suffixRange after)) :
    Gather.field (copies (expanded table (suffixRange after))
      ((P*prefixRange before)*2^w))
      ((BinaryPackedOffsetData.rowIndex p back (pack (pack h y) l)).val*W) W=
      table[y.val]'(by rw [hlen]; exact y.isLt) := by
  have hpback : p.val*2^w+back.val<P*2^w := by nlinarith [p.isLt,back.isLt]
  have hk : (p.val*2^w+back.val)*prefixRange before+h.val<
      (P*prefixRange before)*2^w := by nlinarith [h.isLt]
  have ht := BinaryAddressOffsetRepeatValue.repeated_field table W (suffixRange after)
    ((P*prefixRange before)*2^w) ((p.val*2^w+back.val)*prefixRange before+h.val)
    y.val l.val hu hk (by rw [hlen]; exact y.isLt) l.isLt
  simpa only [rotation_row,hlen] using ht

/-- Source in the prefix before the acted-on front field. Removing actual
suffix/back/gap/front/prefix-tail bits retains precisely this source address. -/
def prefixSourceAddress (w u after G B i : ℕ) := (((((i/B)/2^w)/G)/2^w)/suffixRange after)%2^u

theorem prefix_source_address (P w u after G B : ℕ)
    (r : Fin P) (y : Fin (2^u)) (h : Fin (suffixRange after))
    (front back : Fin (2^w)) (g : Fin G) (j : Fin B) :
    prefixSourceAddress w u after G B
      (index (pack (pack r y) h) front g back j).val=y.val := by
  have hB : 0<B := Nat.zero_lt_of_lt j.isLt
  have hG : 0<G := Nat.zero_lt_of_lt g.isLt
  have hF : 0<2^w := by positivity
  have hH : 0<suffixRange after := by unfold suffixRange; positivity
  have strip (a d e : ℕ) (hd : 0<d) (he : e<d) : (a*d+e)/d=a := by
    rw [Nat.mul_comm a d,Nat.mul_add_div hd,Nat.div_eq_of_lt he,Nat.add_zero]
  unfold prefixSourceAddress
  simp only [index,pack_val]
  rw [strip _ B j.val hB j.isLt,strip _ (2^w) back.val hF back.isLt,
    strip _ G g.val hG g.isLt,strip _ (2^w) front.val hF front.isLt,
    strip _ (suffixRange after) h.val hH h.isLt,
    Nat.mul_comm r.val (2^u),Nat.mul_add_mod,Nat.mod_eq_of_lt y.isLt]

/-- Prefix-source rows repeat each source's offset through every unused
prefix-tail bit, dirty back value and entire gap, in their literal tape order. -/
theorem prefix_rotation_row (P w u after G : ℕ)
    (r : Fin P) (y : Fin (2^u)) (h : Fin (suffixRange after))
    (back : Fin (2^w)) (g : Fin G) :
    (BinaryPackedOffsetData.rowIndex (pack (pack r y) h) back g).val=
      (r.val*2^u+y.val)*(suffixRange after*2^w*G)+(h.val*2^w+back.val)*G+g.val := by
  simp only [BinaryPackedOffsetData.rowIndex,pack_val]
  ring

theorem prefix_repeated_field (P w u after G W : ℕ) (table : List (List Bool))
    (hu : BlockRotationData.Uniform W table) (hlen : table.length=2^u)
    (r : Fin P) (y : Fin (2^u)) (h : Fin (suffixRange after))
    (back : Fin (2^w)) (g : Fin G) :
    Gather.field (copies (expanded table (suffixRange after*2^w*G)) P)
      ((BinaryPackedOffsetData.rowIndex (pack (pack r y) h) back g).val*W) W=
      table[y.val]'(by rw [hlen]; exact y.isLt) := by
  have hh : h.val*2^w+back.val<suffixRange after*2^w := by nlinarith [h.isLt,back.isLt]
  have hl : (h.val*2^w+back.val)*G+g.val<suffixRange after*2^w*G := by nlinarith [g.isLt]
  have ht := BinaryAddressOffsetRepeatValue.repeated_field table W (suffixRange after*2^w*G)
    P r.val y.val ((h.val*2^w+back.val)*G+g.val) hu r.isLt
    (by rw [hlen]; exact y.isLt) hl
  simpa only [prefix_rotation_row,hlen,Nat.add_assoc] using ht

end IntegerMultBounds.Machine.CompactPackedSourceGeometry
