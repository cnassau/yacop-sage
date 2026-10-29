# Verification scripts for `dickson.tex`

These scripts produce the computer checks reported in `dickson.tex` (Table 1 and the
remark after Corollary 5.10) and in Section 6 (the Mùi generators). Except for
`hung_minh.py` and the two `mui_*` scripts, they compute the Steenrod action
directly on polynomials and do not use yacop's Dickson algebra code.

Run the Sage scripts from the repository root through the yacop container
(`.sage` and `.py` files can't be passed as file arguments there, so the code is
passed with `-c`):

```
./yacop.sh -c "$(cat dickson-checks/peterson_action.py)"
```

The plain Python scripts run with `python3`.

The `mui_*` scripts test the code in this checkout.  The yacop installed in the
container may be older, so put the checkout first on the path:

```
./yacop.sh -c "import sys; sys.path.insert(0, '$PWD'); from sage.all import *; import yacop
$(cat dickson-checks/mui_action.py)"
```

| script | checks | paper | runtime |
|---|---|---|---|
| `k1_fit.py` (Python) | exact coefficient for k = 1; shows the formula holds for wt_n = (-1)^n omega_n | Table 1, row 1 | ~40 s |
| `peterson_action.py` (Sage) | action formula (*) and conjugate formula on invariant wt_n; decomposition into Dickson monomials | Table 1, rows 2–4 | ~40 s |
| `lagrange_action.py` (Sage) | (*) for the Lagrange elements Omega_n in all degrees | Table 1, row 5 | ~10 s |
| `primitives.py` (Sage) | (*) for the Milnor primitives P(0,…,0,1) | Table 1, row 6 | ~5 s |
| `digit_lemma.py` (Python) | vanishing of G_{R,E} (Proposition 5.8), at D0 = p^k and at general D0 | Table 1 | ~2 s |
| `antipode.py` (Python) | identity (8) of Prop. 5.12 and Lemma 5.13 (conjugate formula, Theorem 4.6) | Table 1, last rows | ~15 s |
| `arnon.py` (Sage) | p = 2: Omega_n equals Arnon's generalized Peterson element (= Theta_n); transvection identity and invariance criterion sigma(n) >= k | Section 5.5, Table 1 | ~5 s |
| `twosided.py` (Sage) | all p: Omega_n equals the two-sided Peterson element Theta_n; integrality and invariance criterion sigma_p(n) >= k; transvection formula | Section 5.5, Table 1 | ~25 s |
| `hung_minh.py` (Sage + yacop) | yacop's P^i on Dickson invariants against Hung (p = 2) and Hung–Minh (odd p) | remark after Cor. 5.10 | ~15 s |
| `mui_action.py` (Sage + yacop) | P^r on the Mùi generators tau_j against a direct computation in H^*(BV) | Section 6 | ~5 s |
| `mui_associativity.py` (Sage + yacop) | associativity of the ordinary and conjugate action on the tau_j; conjugate = antipode | Section 6 | ~20 min |

Every line of output should report `bad=0`, `0 disagree`, `violations 0`, `OK`
or `True`.
