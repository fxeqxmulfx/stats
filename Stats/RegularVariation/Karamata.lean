/-
  Karamata's theory of regular variation — the `o`-bound `log L = o(log s)`.

  Two variants:
  * **Measurable** (`log_isLittleO_log`): direct corollary of the measurable
    Korevaar UCT.  The "sandwich" step `|log L(s) − log L(T·rⁿ)| ≤ δ²` is
    discharged by uniform convergence on `[1, r]`; the telescoping argument
    at the geometric grid is unchanged.
  * **Monotone** (`log_isLittleO_log_of_monotone`): proved directly, via a
    step bound from pointwise SV, telescoping, and a sandwich argument
    using monotonicity at the grid points `T·rⁿ`.

  Umbrella module — the formalisation is split into submodules:

  * `Stats.RegularVariation.Karamata.Helpers` — auxiliary step / telescope
    lemmas (`log_step_bound_eventually`, `log_L_telescope`,
    `log_one_add_ge_half`).
  * `Stats.RegularVariation.Karamata.Monotone` — monotone variant
    `log_isLittleO_log_of_monotone`.
  * `Stats.RegularVariation.Karamata.Measurable` — measurable variant
    `log_isLittleO_log`.
  * `Stats.RegularVariation.Karamata.Grid` — multiplicative-grid form
    (`subexp_along_exp_grid{,_of_monotone}`).
-/
import Stats.RegularVariation.Karamata.Helpers
import Stats.RegularVariation.Karamata.Monotone
import Stats.RegularVariation.Karamata.Measurable
import Stats.RegularVariation.Karamata.Grid
