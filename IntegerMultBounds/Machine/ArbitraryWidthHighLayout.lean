import IntegerMultBounds.Machine.ArbitraryWidthHighRows
import IntegerMultBounds.Machine.RecursiveRowPadding

/-! Exact high-field exchange, joined-row view, low transpose and separation.
Every view is a bijection of literal serialized cell indices. No physical
exchange or join runtime is asserted by this semantic bridge. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighLayout
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

structure Coordinate (P H L G B : ℕ) where
  pre : Fin P
  highH : Fin H
  lowH : Fin L
  middle : Fin G
  highD : Fin H
  lowD : Fin L
  after : Fin B

def highSwap {P H L G B : ℕ} (a : Coordinate P H L G B) : Coordinate P H L G B :=
  {a with highH := a.highD,highD := a.highH}
def lowSwap {P H L G B : ℕ} (a : Coordinate P H L G B) : Coordinate P H L G B :=
  {a with lowH := a.lowD,lowD := a.lowH}
def fullSwap {P H L G B : ℕ} (a : Coordinate P H L G B) : Coordinate P H L G B :=
  highSwap (lowSwap a)

@[simp] theorem highSwap_twice {P H L G B : ℕ} (a : Coordinate P H L G B) : highSwap (highSwap a) = a := rfl
@[simp] theorem lowSwap_twice {P H L G B : ℕ} (a : Coordinate P H L G B) : lowSwap (lowSwap a) = a := rfl
theorem swap_commute {P H L G B : ℕ} (a : Coordinate P H L G B) : lowSwap (highSwap a) = fullSwap a := rfl

def pairLeft {X : Type*} {A : ℕ} (e : X ≃ Fin A) (B : ℕ) : X × Fin B ≃ Fin (A*B) :=
  (Equiv.prodCongr e (Equiv.refl _)).trans finProdFinEquiv

theorem pairLeft_val {X : Type*} {A B : ℕ} (e : X ≃ Fin A) (a : X) (b : Fin B) :
    (pairLeft e B (a,b)).val = (e a).val*B+b.val := by
  exact RecursiveInterchangeRows.pack_val (e a) b

def originalProduct (P H L G B : ℕ) :
    Coordinate P H L G B ≃ ((((((Fin P × Fin H) × Fin L) × Fin G) × Fin H) × Fin L) × Fin B) where
  toFun a := ((((((a.pre,a.highH),a.lowH),a.middle),a.highD),a.lowD),a.after)
  invFun a := ⟨a.1.1.1.1.1.1,a.1.1.1.1.1.2,a.1.1.1.1.2,a.1.1.1.2,a.1.1.2,a.1.2,a.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨⟨⟨⟨⟨⟨p,h⟩,l⟩,g⟩,d⟩,s⟩,b⟩; rfl

def joinedProduct (P H L G B : ℕ) :
    Coordinate P H L G B ≃ ((((((Fin P × Fin H) × Fin H) × Fin L) × Fin G) × Fin L) × Fin B) where
  toFun a := ((((((a.pre,a.highD),a.highH),a.lowH),a.middle),a.lowD),a.after)
  invFun a := ⟨a.1.1.1.1.1.1,a.1.1.1.1.2,a.1.1.1.2,a.1.1.2,a.1.1.1.1.1.2,a.1.2,a.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨⟨⟨⟨⟨⟨p,d⟩,h⟩,l⟩,g⟩,s⟩,b⟩; rfl

def originalRaw (P H L G B : ℕ) : Coordinate P H L G B ≃ Fin (P*H*L*G*H*L*B) :=
  (originalProduct P H L G B).trans
    (pairLeft (pairLeft (pairLeft (pairLeft (pairLeft (pairLeft (Equiv.refl (Fin P)) H) L) G) H) L) B)

def joinedRaw (P H L G B : ℕ) : Coordinate P H L G B ≃ Fin (P*H*H*L*G*L*B) :=
  (joinedProduct P H L G B).trans
    (pairLeft (pairLeft (pairLeft (pairLeft (pairLeft (pairLeft (Equiv.refl (Fin P)) H) H) L) G) L) B)

theorem originalRaw_val (P H L G B : ℕ) (a : Coordinate P H L G B) :
    (originalRaw P H L G B a).val =
      (((((a.pre.val*H+a.highH.val)*L+a.lowH.val)*G+a.middle.val)*H+a.highD.val)*L+a.lowD.val)*B+a.after.val := by
  simp only [originalRaw,Equiv.trans_apply,originalProduct,Equiv.coe_fn_mk,pairLeft_val,Equiv.refl_apply]

theorem joinedRaw_val (P H L G B : ℕ) (a : Coordinate P H L G B) :
    (joinedRaw P H L G B a).val =
      (((((a.pre.val*H+a.highD.val)*H+a.highH.val)*L+a.lowH.val)*G+a.middle.val)*L+a.lowD.val)*B+a.after.val := by
  simp only [joinedRaw,Equiv.trans_apply,joinedProduct,Equiv.coe_fn_mk,pairLeft_val,Equiv.refl_apply]

def originalDescriptor (P e G B : ℕ) : Descriptor := ⟨P,1,1,e,G,B⟩
def joinedDescriptor (q P e r G B : ℕ) : Descriptor := ⟨P,q^(2*r),1,e-r,G,B⟩

theorem split_power (q e r : ℕ) (hr : r ≤ e) : q^e = q^r*q^(e-r) := by
  rw [← pow_add,Nat.add_sub_of_le hr]

theorem original_volume (q P e r G B : ℕ) (hr : r ≤ e) :
    P*q^r*q^(e-r)*G*q^r*q^(e-r)*B = volume q (originalDescriptor P e G B) := by
  simp only [volume,originalDescriptor]
  rw [split_power q e r hr]
  ring

theorem joined_volume (q P e r G B : ℕ) :
    P*q^r*q^r*q^(e-r)*G*q^(e-r)*B = volume q (joinedDescriptor q P e r G B) := by
  simp only [volume,joinedDescriptor]
  have he : q^(2*r) = q^r*q^r := by rw [← pow_add]; congr 1; omega
  rw [he]
  ring

def originalEquiv (q P e r G B : ℕ) (hr : r ≤ e) :
    Coordinate P (q^r) (q^(e-r)) G B ≃ Fin (volume q (originalDescriptor P e G B)) :=
  (originalRaw P (q^r) (q^(e-r)) G B).trans (finCongr (original_volume q P e r G B hr))

def joinedEquiv (q P e r G B : ℕ) :
    Coordinate P (q^r) (q^(e-r)) G B ≃ Fin (volume q (joinedDescriptor q P e r G B)) :=
  (joinedRaw P (q^r) (q^(e-r)) G B).trans (finCongr (joined_volume q P e r G B))

/-- The original scalar layout really stores [h+,h−,g,d+,d−]. -/
theorem original_index (q P e r G B : ℕ) (hr : r ≤ e)
    (a : Coordinate P (q^r) (q^(e-r)) G B) :
    (originalEquiv q P e r G B hr a).val = RecursiveInterchangeLayout.index q
      (originalDescriptor P e G B) a.pre.val 0 0
      (a.highH.val*q^(e-r)+a.lowH.val) a.middle.val
      (a.highD.val*q^(e-r)+a.lowD.val) a.after.val := by
  change (originalRaw P (q^r) (q^(e-r)) G B a).val = _
  rw [originalRaw_val]
  simp only [RecursiveInterchangeLayout.index,originalDescriptor]
  rw [split_power q e r hr]
  ring

/-- After the high exchange the leading d+/h+ fields are the joined row;
the two low fields keep their literal within-row addresses. -/
theorem joined_index (q P e r G B : ℕ) (a : Coordinate P (q^r) (q^(e-r)) G B) :
    (joinedEquiv q P e r G B a).val = RecursiveInterchangeLayout.index q
      (joinedDescriptor q P e r G B) a.pre.val
      (a.highD.val*q^r+a.highH.val) 0 a.lowH.val a.middle.val a.lowD.val a.after.val := by
  change (joinedRaw P (q^r) (q^(e-r)) G B a).val = _
  rw [joinedRaw_val]
  simp only [RecursiveInterchangeLayout.index,joinedDescriptor]
  have he : q^(2*r) = q^r*q^r := by rw [← pow_add]; congr 1; omega
  rw [he]
  ring

/-- The middle transpose leaves the joined row d+/h+ fixed and exchanges
only h−/d− at their actual numeric addresses. -/
theorem low_index (q P e r G B : ℕ) (a : Coordinate P (q^r) (q^(e-r)) G B) :
    (joinedEquiv q P e r G B (lowSwap a)).val = RecursiveInterchangeLayout.index q
      (joinedDescriptor q P e r G B) a.pre.val
      (a.highD.val*q^r+a.highH.val) 0 a.lowD.val a.middle.val a.lowH.val a.after.val :=
  joined_index q P e r G B (lowSwap a)

/-- Separation and the final high exchange produce the exact full swapped
scalar address, rather than an equality only of coordinate tuples. -/
theorem final_index (q P e r G B : ℕ) (hr : r ≤ e)
    (a : Coordinate P (q^r) (q^(e-r)) G B) :
    (originalEquiv q P e r G B hr (fullSwap a)).val = RecursiveInterchangeLayout.index q
      (originalDescriptor P e G B) a.pre.val 0 0
      (a.highD.val*q^(e-r)+a.lowD.val) a.middle.val
      (a.highH.val*q^(e-r)+a.lowH.val) a.after.val :=
  original_index q P e r G B hr (fullSwap a)

def joinedAddress (P e r G B : ℕ) (a : Coordinate P (prime^r) (prime^(e-r)) G B) :
    RecursiveInterchangeScaling.Address (joinedDescriptor prime P e r G B) where
  beforeRows := a.pre
  row := Fin.cast (by rw [← pow_add]; congr 1; omega : prime^r*prime^r = prime^(2*r))
    (RecursiveInterchangeRows.pack a.highD a.highH)
  before := ⟨0,by change 0 < 1; decide⟩
  h := a.lowH
  middle := a.middle
  d := a.lowD
  after := a.after

theorem joinedAddress_index (P e r G B : ℕ) (a : Coordinate P (prime^r) (prime^(e-r)) G B) :
    RecursiveInterchangeScaling.index (joinedAddress P e r G B a) = joinedEquiv prime P e r G B a := by
  apply Fin.ext
  rw [RecursiveInterchangeScaling.index_val,joined_index]
  simp only [joinedAddress]
  congr 1
  exact RecursiveInterchangeRows.pack_val a.highD a.highH

theorem transpose_joined {α : Type*} (P e r G B : ℕ)
    (x : Fin (volume prime (joinedDescriptor prime P e r G B)) → α)
    (a : Coordinate P (prime^r) (prime^(e-r)) G B) :
    Shared50RecursiveNodeRows.transpose (one_dvd _) x (joinedEquiv prime P e r G B a) =
      x (joinedEquiv prime P e r G B (lowSwap a)) := by
  have h := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)
    (one_dvd _) x (joinedAddress P e r G B (lowSwap a))
  have hs : Shared50RecursiveNodeTranspose.swapAddress (joinedAddress P e r G B (lowSwap a)) =
      joinedAddress P e r G B a := rfl
  rw [hs,joinedAddress_index,joinedAddress_index] at h
  exact h

def originalAddress (P e r G B : ℕ) (hr : r ≤ e)
    (a : Coordinate P (prime^r) (prime^(e-r)) G B) :
    RecursiveInterchangeScaling.Address (originalDescriptor P e G B) where
  beforeRows := a.pre
  row := ⟨0,by change 0 < 1; decide⟩
  before := ⟨0,by change 0 < 1; decide⟩
  h := Fin.cast (split_power prime e r hr).symm (RecursiveInterchangeRows.pack a.highH a.lowH)
  middle := a.middle
  d := Fin.cast (split_power prime e r hr).symm (RecursiveInterchangeRows.pack a.highD a.lowD)
  after := a.after

theorem originalAddress_index (P e r G B : ℕ) (hr : r ≤ e)
    (a : Coordinate P (prime^r) (prime^(e-r)) G B) :
    RecursiveInterchangeScaling.index (originalAddress P e r G B hr a) =
      originalEquiv prime P e r G B hr a := by
  apply Fin.ext
  rw [RecursiveInterchangeScaling.index_val,original_index]
  simp only [originalAddress]
  congr 1
  · exact RecursiveInterchangeRows.pack_val a.highH a.lowH
  · exact RecursiveInterchangeRows.pack_val a.highD a.lowD

theorem transpose_original {α : Type*} (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (originalDescriptor P e G B)) → α)
    (a : Coordinate P (prime^r) (prime^(e-r)) G B) :
    Shared50RecursiveNodeRows.transpose (one_dvd _) x (originalEquiv prime P e r G B hr a) =
      x (originalEquiv prime P e r G B hr (fullSwap a)) := by
  have h := Shared50RecursiveNodeTranspose.transpose_all (by decide : 0 < 1)
    (one_dvd _) x (originalAddress P e r G B hr (fullSwap a))
  have hs : Shared50RecursiveNodeTranspose.swapAddress (originalAddress P e r G B hr (fullSwap a)) =
      originalAddress P e r G B hr a := rfl
  rw [hs,originalAddress_index,originalAddress_index] at h
  exact h

/-- Exact word view after exchanging d+ before h+ and joining these two
high fields. This maps every cell via the full finite serialized bijection. -/
def exchangeJoin {α : Type*} (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (originalDescriptor P e G B)) → α) :
    Fin (volume prime (joinedDescriptor prime P e r G B)) → α := fun z =>
  x (originalEquiv prime P e r G B hr ((joinedEquiv prime P e r G B).symm z))

/-- Separate the joined row and exchange h+ past the low fields, yielding
[d+,d−,g,h+,h−] after the intervening low transpose. -/
def separateExchange {α : Type*} (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (joinedDescriptor prime P e r G B)) → α) :
    Fin (volume prime (originalDescriptor P e G B)) → α := fun z =>
  x (joinedEquiv prime P e r G B (highSwap ((originalEquiv prime P e r G B hr).symm z)))

theorem exchangeJoin_entry {α : Type*} (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (originalDescriptor P e G B)) → α)
    (a : Coordinate P (prime^r) (prime^(e-r)) G B) :
    exchangeJoin P e r G B hr x (joinedEquiv prime P e r G B a) =
      x (originalEquiv prime P e r G B hr a) := by simp only [exchangeJoin,Equiv.symm_apply_apply]

theorem separateExchange_entry {α : Type*} (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (joinedDescriptor prime P e r G B)) → α)
    (a : Coordinate P (prime^r) (prime^(e-r)) G B) :
    separateExchange P e r G B hr x (originalEquiv prime P e r G B hr a) =
      x (joinedEquiv prime P e r G B (highSwap a)) := by
  simp only [separateExchange,Equiv.symm_apply_apply]

/-- The low-width row transpose between the two high exchanges is exactly
the original full-width transpose, on every serialized input cell. -/
theorem exchange_transpose_separate {α : Type*} (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (originalDescriptor P e G B)) → α) :
    separateExchange P e r G B hr
      (Shared50RecursiveNodeRows.transpose (one_dvd _)
        (exchangeJoin P e r G B hr x)) =
      Shared50RecursiveNodeRows.transpose (one_dvd _) x := by
  funext z
  obtain ⟨a,rfl⟩ := (originalEquiv prime P e r G B hr).surjective z
  rw [separateExchange_entry,transpose_joined,exchangeJoin_entry,swap_commute,transpose_original]

/-- Actual row padding followed by the proved low transpose and crop retains
the exact full-width swap after both high-field exchanges and separation. -/
theorem padded_exchange_transpose_separate {α : Type*} (P e r G B R' : ℕ) (hr : r ≤ e)
    (hrows : (joinedDescriptor prime P e r G B).rows ≤ R') (zero : α)
    (x : Fin (volume prime (originalDescriptor P e G B)) → α) :
    separateExchange P e r G B hr
      (RecursiveRowPadding.cropArray hrows
        (Shared50RecursiveNodeRows.transpose (one_dvd _)
          (RecursiveRowPadding.padArray R' zero (exchangeJoin P e r G B hr x)))) =
      Shared50RecursiveNodeRows.transpose (one_dvd _) x := by
  rw [RecursiveRowPadding.cropArray_transpose_padArray,exchange_transpose_separate]

/-- Selecting rho by the exact high-row algorithm yields the manuscript's
dominating joined row range and its strict q² overshoot bound. -/
theorem selected_rows (q P e D G B : ℕ) (hq : 2 ≤ q) (hD : 0 < D) :
    D ≤ (joinedDescriptor q P e (ArbitraryWidthHighRows.rho q D) G B).rows ∧
      (joinedDescriptor q P e (ArbitraryWidthHighRows.rho q D) G B).rows < q*q*D :=
  ⟨ArbitraryWidthHighRows.dominates q D hq,ArbitraryWidthHighRows.row_lt q D hq hD⟩

end
end IntegerMultBounds.Machine.ArbitraryWidthHighLayout
