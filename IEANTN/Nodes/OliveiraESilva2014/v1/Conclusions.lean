/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Goldbach

/-!
# Node `OliveiraESilva2014.v1` — the even Goldbach conjecture verified to `4·10¹⁸`

One conclusion, and it is a computation: the verification of Oliveira e Silva, Herzog and Pardi,
which is the current record and the base case of every finite odd-Goldbach range the network
knows.

**On the third author.** PrimeNumberTheoremAnd names this computation after
"e Silva–Herzog–Piranian", in its theorem name and in its blueprint text. That is wrong: the third
author is Silvio Pardi. PNT+'s own bibliography has it right, and so does Crossref. George
Piranian was a complex analyst at Michigan with no part in this. The error is transcription, not
attribution — but it is in the name a reader sees.
-/

namespace OliveiraESilva2014.v1

open IEANTN

/-- **Even Goldbach up to `4·10¹⁸`.** Every even `n` with `4 ≤ n ≤ 4·10¹⁸` is a sum of two primes.

The computation also produced the prime gaps below `4·10¹⁸`, which is what the paper's title
advertises alongside the Goldbach verification and what much of its length is about. Only the
Goldbach half is stated here.

The paper reports the verification as exhaustive over the range, performed twice with independent
implementations. -/
def even_up_to_4e18 : Prop :=
  GoldbachEvenUpTo (4 * 10 ^ 18)

end OliveiraESilva2014.v1
