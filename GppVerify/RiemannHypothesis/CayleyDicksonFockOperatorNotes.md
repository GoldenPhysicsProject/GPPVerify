# Cayley--Dickson / finite-prime Fock operator boundary

The proved Lean bridge is currently dimension/Hodge-energy level:

- Fock state count after n binary channels is 2^n.
- Cayley--Dickson vector-space dimension after n doublings is 2^n.
- The common sequence begins 1,2,4,8,16,... .
- The finite Hodge energy E(z)=sum_i |z_i|^2 is nonnegative and vanishes iff every z_i vanishes.
- With z_i(s)=1-exp(-s log p_i), any nonempty finite family with p_i>1 has strictly positive
  Hodge energy on Re(s)=1/2.

The exact operator theorem suggested by the discovery experiment is

    Q = sum_i z_i a_i^†,       Q^2 = 0,
    D = Q + Q^†,               D^2 = (sum_i |z_i|^2) I,

for a finite CAR family.  This has been numerically checked with an explicit Jordan--Wigner
representation for n=1,...,6 in GPPDiscovery2.  It is the next Lean target.

No identification of Cayley--Dickson multiplication with the exterior/CAR product is made.
The common structure established so far is the binary doubling skeleton; a stronger bridge
would require an explicit functor/intertwiner or Clifford-module construction.
