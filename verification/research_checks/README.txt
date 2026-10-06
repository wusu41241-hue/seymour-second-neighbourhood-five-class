Auxiliary research checks

These directories preserve the graph-identity, completion, deletion and control
programs associated with the mathematical development. Their checks are not
substitutes for the proofs and do not certify an unknown all-deficient graph.
Some historical programs retain references to their original local helper or
input locations. The coverage inventory records their provenance and scope.

The finite computer-assisted theorem in the main article is fully checked by
the two portable integer replays in the parent verification directory, together
with incoming_core_certificates_n1.json through incoming_core_certificates_n5.json.
It does not require any historical script or external solver archive.

Useful standalone control programs include:
  global_round2/audit_closure_exact_control_models.js
  global_round2/verify_strict_surplus_control.js
  global_followup/verify_transport_obstruction_family.js
  global_round3/audit_simultaneous_row_clone.js

For the optional table generator in the parent directory, install/use an existing
standard z3-solver Python environment and run with --n 1 through --n 5.
The generator is outside the independent verifier's trusted boundary.
