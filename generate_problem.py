from sage.all import *
set_random_seed(0)

# Base field
ea = 37
for eb in range(20,100):
    p = ZZ(2**ea * 3**eb - 1)
    if p.is_prime():
        break
else:
    exit('No prime found')

print(f'{ea = }, {eb = }')
Fp = GF(p)
g = Fp.multiplicative_generator()

r = Fp(-1)
assert not r.is_square()
s = (p**2-1)//2

print(f'Set modulus to {p}')
print(f'Set generator to {g}')
print(f'Set NONRESIDUE to {r.lift_centered()}')
print(f'Set S to {s}')
print(f'Make sure base has {ceil(ZZ(p).nbits()/64)} blocks')
print(f'Make sure exponent has at least {ceil(ZZ(s).nbits()/64)} blocks')

Fp2, i = GF((p, 2), 'i', modulus=[1,0,-r]).objgen()

# Public parameters
E0 = EllipticCurve(Fp2, j=0)

P, Q = E0.torsion_basis(2**ea)
K = P + Fp.random_element() * Q
phi = E0.isogeny(K, algorithm='factored')
E1 = phi.codomain()
j0 = E0.j_invariant()
j1 = E1.j_invariant()

a0, b0 = E0.a4(), E0.a6()
assert E0.is_supersingular() and E1.is_supersingular()
print(f'cargo run --release {a0[0]} {a0[1]} {b0[0]} {b0[1]} {j1[0]} {j1[1]} {ea}')