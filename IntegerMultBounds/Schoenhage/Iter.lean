import Mathlib.Tactic

/-! The twisted transform as the tape computes it: layer by layer over
natural-number residues modulo `2^N + 1`, each block carrying the unary shift
of its butterfly multiplier. A forward layer maps a block `U ++ V` to
`(u + 2^t v) ++ (u - 2^t v)`; an inverse layer maps `P ++ Q` to
`(p + q) ++ (p - q) 2^(2N - t)`, computed as the negation of `(p - q) 2^(N - t)`.
Children of a block with shift `t` get the shifts `t / 2` and `t / 2 + N / 2`. -/

namespace IntegerMultBounds.Schoenhage

/-- The modulus `2^N + 1`. -/
def Fm (N : ℕ) : ℕ := 2 ^ N + 1

/-- Forward butterfly sums. -/
def bfS (N t : ℕ) (U V : List ℕ) : List ℕ :=
  List.zipWith (fun u v => (u + 2 ^ t * v % Fm N) % Fm N) U V

/-- Forward butterfly differences. -/
def bfD (N t : ℕ) (U V : List ℕ) : List ℕ :=
  List.zipWith (fun u v => (u + Fm N - 2 ^ t * v % Fm N) % Fm N) U V

/-- One forward layer: blocks of size `2H`, one shift per block. -/
def layerF (N H : ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | t :: E, D => bfS N t (D.take H) ((D.drop H).take H) ++ bfD N t (D.take H) ((D.drop H).take H) ++
      layerF N H E (D.drop (2 * H))

/-- Inverse butterfly sums. -/
def ibS (N : ℕ) (P Q : List ℕ) : List ℕ := List.zipWith (fun p q => (p + q) % Fm N) P Q

/-- Inverse butterfly differences, multiplied by `2^(2N - t) = -2^(N - t)`. -/
def ibD (N t : ℕ) (P Q : List ℕ) : List ℕ :=
  List.zipWith (fun p q => (Fm N - 2 ^ (N - t) * ((p + Fm N - q) % Fm N) % Fm N) % Fm N) P Q

/-- One inverse layer. -/
def layerI (N H : ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | t :: E, D => ibS N (D.take H) ((D.drop H).take H) ++ ibD N t (D.take H) ((D.drop H).take H) ++
      layerI N H E (D.drop (2 * H))

/-- The shifts of the children blocks. -/
def kids (N : ℕ) (E : List ℕ) : List ℕ := E.flatMap fun t => [t / 2, t / 2 + N / 2]

/-- The shifts at depth `s`. -/
def shiftsAt (N : ℕ) : ℕ → List ℕ
  | 0 => [N / 2]
  | s + 1 => kids N (shiftsAt N s)

/-- `s` forward layers starting with half-block size `H`. -/
def fwdIter (N : ℕ) : ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, D => D
  | s + 1, H, E, D => fwdIter N s (H / 2) (kids N E) (layerF N H E D)

/-- The full inverse transform of size `2^k`: layers from the deepest to the top. -/
def invIter (N : ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, D => D
  | s + 1, k, D => invIter N s k (layerI N (2 ^ (k - 1 - s)) (shiftsAt N s) D)

end IntegerMultBounds.Schoenhage
