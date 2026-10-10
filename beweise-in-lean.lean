import Mathlib

-- Beispiel 1.12: Sind m, n natuerliche Zahlen mit m^2 < n^2, so ist m < n.
-- Cursor in eine Beweiszeile setzen: rechts erscheint der Beweiszustand.

-- Beweis durch Kontraposition
example (m n : Nat) (h : m ^ 2 < n ^ 2) : m < n := by
  -- Kontraposition: danach ist h : n <= m und das Ziel n^2 <= m^2
  contrapose! h
  -- h mit n bzw. mit m multipliziert, dann beides hintereinander:
  have h1 : n * n <= m * n := Nat.mul_le_mul_right n h
  have h2 : m * n <= m * m := Nat.mul_le_mul_left m h
  have h3 : n * n <= m * m := Nat.le_trans h1 h2
  -- Ziel als n * n <= m * m schreiben, das ist h3
  rw [sq, sq]
  exact h3

-- Widerspruchsbeweis
example (m n : Nat) (h : m ^ 2 < n ^ 2) : m < n := by
  -- Angenommen, es gilt nicht m < n. Das Ziel ist jetzt False.
  by_contra h1
  have h2 : n <= m := Nat.le_of_not_lt h1
  -- h2 mit n multipliziert:
  have h3 : n * n <= m * n := Nat.mul_le_mul_right n h2
  -- h als m * m < n * n schreiben und mit h3 verbinden:
  rw [sq, sq] at h
  have h4 : m * m < m * n := lt_of_lt_of_le h h3
  -- durch m teilen:
  have h5 : m < n := Nat.lt_of_mul_lt_mul_left h4
  -- Widerspruch zu h1
  exact absurd h5 h1

-- Zum Vergleich: In Mathlib steht die Aussage schon als Satz,
-- m ^ k < n ^ k <-> m < n fuer k ungleich 0. Der Beweis ist dann eine Zeile.
example (m n : Nat) (h : m ^ 2 < n ^ 2) : m < n :=
  (Nat.pow_lt_pow_iff_left two_ne_zero).mp h
