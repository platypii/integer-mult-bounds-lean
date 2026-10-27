module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOriginPackets
public import IntegerMultBounds.NLogN.PhaseCellHaloScheduleCost

/-! An ordered family stores each exact grouped page with its symbol-count header. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def weightKeyPacket {A : ℕ} (page : List (Fin (A+4))) : List (Fin (A+4)) :=
  List.replicate page.length tick++blank::page

def weightKeyFamily {A : ℕ} (pages : List (List (Fin (A+4)))) : List (Fin (A+4)) :=
  pages.flatMap weightKeyPacket

@[simp] theorem weightKeyPacket_length {A : ℕ} (page : List (Fin (A+4))) :
    (weightKeyPacket page).length = 2*page.length+1 := by simp [weightKeyPacket]; omega

@[simp] theorem weightKeyFamily_cons {A : ℕ} (page : List (Fin (A+4))) (pages : List (List (Fin (A+4)))) :
    weightKeyFamily (page::pages) = weightKeyPacket page++weightKeyFamily pages := rfl

theorem weightKeyFamily_length {A : ℕ} (pages : List (List (Fin (A+4)))) :
    (weightKeyFamily pages).length = 2*(pages.map List.length).sum+pages.length := by
  induction pages with
  | nil => rfl
  | cons page pages ih => simp only [weightKeyFamily_cons,List.length_append,weightKeyPacket_length,
      List.map_cons,List.sum_cons,List.length_cons,ih]; omega

def haloWeightKeyPages (A w q P s t u band a b : ℕ) (keys : List ℕ) : List (List (Fin (A+4))) :=
  keys.map fun L => batchWeightPage A w q P s t u
    (haloLengthGroup s t band a b L).length L (fun n => (haloGroupOrigin s t band a b L n).val)

theorem haloWeightKeyPages_volume (A w q P s t u band a b : ℕ) (keys : List ℕ) :
    ((haloWeightKeyPages A w q P s t u band a b keys).map List.length).sum =
      2*w*(keys.map (fun L => (haloLengthGroup s t band a b L).length*L)).sum := by
  induction keys with
  | nil => simp [haloWeightKeyPages]
  | cons L keys ih =>
    simp only [haloWeightKeyPages,List.map_cons,List.sum_cons,batchWeightPage_length] at ih ⊢
    rw [ih]
    ring

theorem haloWeightKeyFamily_length (A w q P s t u band a b : ℕ) (keys : List ℕ) :
    (weightKeyFamily (haloWeightKeyPages A w q P s t u band a b keys)).length =
      4*w*(keys.map (fun L => (haloLengthGroup s t band a b L).length*L)).sum+keys.length := by
  rw [weightKeyFamily_length,haloWeightKeyPages_volume]
  simp only [haloWeightKeyPages,List.length_map]
  ring

theorem haloWeightKeyFamily_length_le {s t : ℕ} [NeZero s] (hst : s < t)
    (A w q P u band a b : ℕ) :
    (weightKeyFamily (haloWeightKeyPages A w q P s t u band a b (haloLengthKeys s t band a b))).length ≤
      4*s*w+(haloLengthKeys s t band a b).length := by
  rw [haloWeightKeyFamily_length,haloLengthKeys_volume hst]
  have hcard : (haloInterior s t band a b).card ≤ s := by
    simpa using Finset.card_le_univ (s := haloInterior s t band a b)
  have h := Nat.mul_le_mul_left (4*w) hcard
  nlinarith only [h]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
