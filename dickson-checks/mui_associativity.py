# Associativity checks for the action on the Mui generators (Theorem 6.1):
# ordinary and conjugate action on regions containing the tau_j, and agreement
# of the conjugate action with the antipode.  The first case (p=2, k=3, generic)
# is where the old model failed, e.g. for P(8), Q_0 on tau1*tau2.
#
# Uses the yacop in this checkout.  Run from the repository root:
#   ./yacop.sh -c "import sys; sys.path.insert(0, '$PWD'); from sage.all import *; import yacop
#   $(cat dickson-checks/mui_associativity.py)"
import sys
from yacop.modules.dickson import DicksonAlgebra
from yacop.utils.region import region
def t(label, X, reg, conj):
    try:
        (X._manual_test_left_conj_action if conj else X._manual_test_left_action)(reg)
        print(label, "conj" if conj else "ordinary", "OK")
    except Exception as e:
        print(label, "conj" if conj else "ordinary", "FAILED:", repr(e)[:150])
    sys.stdout.flush()
cases = [("p=2 k=3 generic", DicksonAlgebra(2,3,generic=True), region(tmin=-12,tmax=8)),
         ("p=2 k=2 generic", DicksonAlgebra(2,2,generic=True), region(tmin=-6,tmax=12)),
         ("p=3 k=2 e=-1", DicksonAlgebra(3,2), region(tmin=-30,tmax=20,emin=-1,emax=-1)),
         ("p=3 k=2 e=-2", DicksonAlgebra(3,2), region(tmin=-30,tmax=20,emin=-2,emax=-2))]
for (lab, X, reg) in cases:
    t(lab, X, reg, False)
    t(lab, X, reg, True)
A = SteenrodAlgebra(3); E = DicksonAlgebra(3,2); E.inject_variables()
ok = all(op % m == op.antipode()*m
         for op in [A.Q(0), A.Q(1), A.P(1), A.P(0,1), A.Q(0)*A.P(1)]
         for m in [tau1*d16, tau0*tau1, tau0*d12, tau1])
print("conjugate action == antipode:", ok)
