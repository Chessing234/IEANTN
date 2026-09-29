/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Goldbach

/-!
# Node `Richstein2001.v1` — the even Goldbach conjecture verified to `4·10¹⁴`

One conclusion, and it is a computation: Richstein's 2001 verification.

Superseded in fact by `OliveiraESilva2014.v1`, which reaches `4·10¹⁸`, and kept anyway. The
network records where a number came from, and the Ramaré–Saouter height for odd Goldbach was
derived from *this* verification, a decade before the later one existed. A node that only recorded
the current best would lose that.
-/

namespace Richstein2001.v1

open IEANTN

/-- **Even Goldbach up to `4·10¹⁴`.** Every even `n` with `4 ≤ n ≤ 4·10¹⁴` is a sum of two primes.

Richstein's computation, which also produced the minimal Goldbach partitions and the list of
`n` requiring a large prime. Only the verification itself is stated here. -/
def even_up_to_4e14 : Prop :=
  GoldbachEvenUpTo (4 * 10 ^ 14)

end Richstein2001.v1
