/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import GoldbachDev
import IEANTN.Nodes.Goldbach.v1.Conclusions
import IEANTN.Nodes.Richstein2001.v1.Conclusions
import IEANTN.Nodes.OliveiraESilva2014.v1.Conclusions
import IEANTN.Nodes.RamareSaouter2003.v1.Conclusions
import IEANTN.Nodes.KadiriLumley.v1.Conclusions

/-!
# Solution for `Goldbach.v1`

The six conclusions, from `GoldbachDev`, which is the port of
`PrimeNumberTheoremAnd/IEANTN/Goldbach.lean`.

The three unconditional ones are theorems there. The three ranges take the imported statements as
hypotheses, exactly as the generated challenge supplies them: two verifications that no kernel
checks, and two prime-gap results this network cites.
-/

theorem Goldbach.v1.challenge_even_implies_odd : Goldbach.v1.even_implies_odd :=
  GoldbachSol.even_implies_odd

theorem Goldbach.v1.challenge_even_and_gaps_imply_odd : Goldbach.v1.even_and_gaps_imply_odd :=
  GoldbachSol.even_and_gaps_imply_odd

theorem Goldbach.v1.challenge_even_up_to_30 : Goldbach.v1.even_up_to_30 :=
  GoldbachSol.even_up_to_30

theorem Goldbach.v1.challenge_odd_up_to_ramare_saouter
    (richstein2001_v1_even_up_to_4e14 : Richstein2001.v1.even_up_to_4e14)
    (ramaresaouter2003_v1_prime_in_short_interval :
      RamareSaouter2003.v1.prime_in_short_interval) :
    Goldbach.v1.odd_up_to_ramare_saouter :=
  GoldbachSol.odd_up_to_ramare_saouter richstein2001_v1_even_up_to_4e14
    ramaresaouter2003_v1_prime_in_short_interval

theorem Goldbach.v1.challenge_odd_up_to_1_1325e26
    (oliveiraesilva2014_v1_even_up_to_4e18 : OliveiraESilva2014.v1.even_up_to_4e18)
    (ramaresaouter2003_v1_prime_in_short_interval :
      RamareSaouter2003.v1.prime_in_short_interval) :
    Goldbach.v1.odd_up_to_1_1325e26 :=
  GoldbachSol.odd_up_to_1_1325e26 oliveiraesilva2014_v1_even_up_to_4e18
    ramaresaouter2003_v1_prime_in_short_interval

theorem Goldbach.v1.challenge_odd_up_to_kadiri_lumley
    (oliveiraesilva2014_v1_even_up_to_4e18 : OliveiraESilva2014.v1.even_up_to_4e18)
    (kadirilumley_v1_prime_in_interval_above_exp_59 :
      KadiriLumley.v1.prime_in_interval_above_exp_59)
    (kadirilumley_v1_prime_in_interval_above_exp_60 :
      KadiriLumley.v1.prime_in_interval_above_exp_60)
    (ramaresaouter2003_v1_prime_in_short_interval :
      RamareSaouter2003.v1.prime_in_short_interval) :
    Goldbach.v1.odd_up_to_kadiri_lumley :=
  GoldbachSol.odd_up_to_kadiri_lumley oliveiraesilva2014_v1_even_up_to_4e18
    kadirilumley_v1_prime_in_interval_above_exp_59
    kadirilumley_v1_prime_in_interval_above_exp_60
    ramaresaouter2003_v1_prime_in_short_interval
