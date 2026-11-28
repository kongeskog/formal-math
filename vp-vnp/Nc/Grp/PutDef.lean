/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Lists

/-!
# Comparing units with the stored contents: definitions
-/

namespace Nc.Grp

open NS1 NS1.Tree

/-- The first `ub` bits, filled with zeros. -/
def padTake (ub : ℕ) (r : List Bool) : List Bool := r.take ub ++ List.replicate (ub - r.length) false

/-- Compare the units of a string (with its final 1) with the contents at the keys; fail if the
number of keys is wrong. -/
def putL (ub : ℕ) : List (List Bool) → List Bool → Tree → List Tree
  | [], r, t => if r = [] then [t] else []
  | k :: ks, r, t =>
    if r ≠ [] ∧ ofBits (padTake ub r) = tget k t then putL ub ks (r.drop ub) t else []

/-- Compare several strings. -/
def putsL (ub : ℕ) : List (List (List Bool)) → List (List Bool) → Tree → List Tree
  | [], _, t => [t]
  | ks :: kss, strs, t => (putL ub ks (strs.headD []) t).flatMap (putsL ub kss strs.tail)

end Nc.Grp
