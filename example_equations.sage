# In this example we show how one uses our code to find equations of Shimura curves
p=53
Nm=2
Np=1
k=2
#Y=BTQuotient(p,2,use_magma = False)
Y=BTQuotient(p,2)
genus=Y.genus()
print 'genus=%s'%genus

# Define a space of harmonic cocycles
prec=30
M2=HarmonicCocycles(Y,k,prec)
time B0=M2.basis()
print "Dimension = %s"%M2.dimension()

# This computes a basis of eigenforms, at least when we don't need to enlarge the field!
D=M2.decomposition()

# This is only needed to match the calculation in the paper
D = [D[1],D[0],D[3],D[2]]

assert(all([M.dimension()==1 for M in D]))
B0 = [M.gen(0) for M in D]

# Now, create the space of overconvergent automorphic forms and lift the basis.
MM=pAutomorphicForms(Y,k,prec,overconvergent=True)
BB=[MM.lift(f) for f in B0]

PolyRing=PolynomialRing(QQ,genus,names='x')
V=find_relations(BB,3,prec,PolyRing.gens(),h=0)
save(V,'Vrelations.sobj')
V=load('Vrelations.sobj')
F,lst=find_invariants(genus,V,PolyRing)
PolyRingParams=F[0].parent()
PolyRingParams.inject_variables()
Params=PolyRingParams.base_ring()
Params.inject_variables()

f,g=substitute(F,x0=1/(5*a2)*x0, x1=1/(a3)*x1, x2=1/(a1)*x2,x3=1/(3*a1)*x3)

#f,g=substitute(F,x0=-1/(7*41*a2)*x0, x1=17/(2*5*7*41*a3)*x1, x2=1/(3*5*17*a1)*x2,x3=1/(3*5*17*a1)*x3)

#f,g = substitute(F,x0=1/(3^2*2^5*a2)*x0,x1=-17/(2^6*3^2*5*a3)*x1,x2=1/(3^3*5*17*a1)*x2,x3=1/(3*3*3*5*17*a1)*x3)
print f
print g

# 2*x0^2 + 12*x0*x1 + (-17)*x1^2 + 2*a0*x2^2 + 2*a1*x3^2
# 5*x0^3 + 33*x0^2*x1 + 16*x1^3 + 3*a1*x0*x3^2 + 15*a1*x1*x3^2

#Figure out the Atkin-Lehner involutions:

# Action of w2 on basis:
print [d.hecke_matrix(2)[0,0].rational_reconstruction() for d in D]
# [1, 1, -1, -1]

# Action of w53 on basis:
print [d.hecke_matrix(53)[0,0].rational_reconstruction() for d in D]
# [-1, -1, -1, 1]

# This will allow us to find the divisor of x3 and of x2 by taking the fixed points by
# w53 and w(2*53) respectively.

#Find the divisor of x3
QQy.<y>=PolynomialRing(RationalField())
phi=f.parent().hom([y,1,0,0],codomain=QQy,check=False)
f0,g0=substitute([f,g],x3=0,x1=1)
# X1=1
# X3=0
phig0=phi(g0)/phi(g0).leading_coefficient()
den = phig0.denominator()
phig0subs=(den^phig0.degree()*phig0).subs(y=1/den*y)
L.<b>=NumberField(phig0subs,names='a').galois_closure()
X0s=[r[0] for r in phi(g0).roots(L)]
X0=X0s[0] # This is one of the possible coordinates for a point in the divisor
print X0
# 121/3760935138*b^5 - 141569/37609351380*b^4 - 179707/18804675690*b^3 + 342139721/37609351380*b^2 + 4065340/1880467569*b - 53107194877/9402337845

"""
We take w(53) because it should act by -1 in x3 and by 1 on the rest (or the opposite, as it happens, since we work projectively).
"""
M.<c>=NumberField(y^2+53)
print M.class_number()
# 6
print factor(M.discriminant())
# -1 * 2^2 * 53

"""
Messy part now. The points in the divisor should generate the HCF of M.
In other words, they should be unramified
"""
#x2sq=(17-2*X0^2-12*X0)/2
x2sq = -f0.subs(x0=X0).constant_coefficient()/2

# We construct the field where the coordinates x0 are defined
LM,M_into_LM,L_into_LM,_=M.composite_fields(L,both_maps=True)[0]
LM_rel=LM.relativize(M_into_LM,['e','c'])
relative_map = LM_rel.structure()[1]

print LM_rel.relative_degree()
# 3
print LM_rel.relative_discriminant()
# Fractional ideal (1)

# Since LM is unramified over M we know that LM is inside H, the Hilbert Class Field of M. We
# must obtain H by taking the square root of x2sq0, after adjusting a0
x2sq0=relative_map(L_into_LM(x2sq))

I=LM_rel.ideal(x2sq0)
print [factor(v[0].absolute_norm()) for v in I.factor()]
# [2, 2, 2, 3^3, 3^3, 5^2, 53]

# We see 3 and 5 appearing above (other than 2 and 53, which are expected),
# and these would add extra ramification. So we need that a0 has 3 and 5:

# We try to take the square root and check that it is unramified. We also need that
# the element is not a square, because its root must generate the HCF.
a00=1
x2sq01=x2sq0*a00
x2sq01=x2sq01*x2sq01.denominator()**2
MMz.<Z>=PolynomialRing(LM_rel)
MM.<z> = LM_rel.extension(Z^2-x2sq01)
print MM.relative_discriminant(),'norm=', factor(MM.relative_discriminant().absolute_norm())

# The problematic primes are 2 and 3 (and maybe we need to adjust by -1 as well).
a00=-2*3
x2sq01=100*x2sq0*a00
MMz.<Z>=PolynomialRing(LM_rel)
MM.<z> = LM_rel.extension(Z^2-x2sq01)
x = MM.absolute_polynomial().parent().gen()
MMabs.<z> = NumberField(MM.absolute_polynomial())
MMrel = MMabs.relativize(MMabs(-53).sqrt(),names='h,i')
print MMrel.relative_discriminant()


# We took the -1 because without it the element is a square. We took the 2 because otherwise the extension
# is ramified.

"""
Up to squares
and up to powers of 53, it is a0=-2*3
"""

#Find the divisor of x2
QQy.<y>=PolynomialRing(RationalField())
phi=f.parent().hom([y,1,0,0],codomain=QQy,check=False)
f0,g0=substitute([f,g],x2=0,x1=1)
# X1=1
# X2=0
# We find X0 by substituting a1x3^2 into the second equation
a1x32 = (-2*x0^2-12*x0+17)/2
phig0 = phi(5*x0^3+3*x0*a1x32+33*x0^2+15*a1x32+16)
phig0subs = phig0/phig0.leading_coefficient()
den = phig0subs.denominator()
phig0subs=(den^phig0subs.degree()*phig0subs).subs(y=1/den*y)
L.<b>=NumberField(phig0subs,names='a').galois_closure()
X0s=[r[0] for r in phig0.roots(L)]
X0=X0s[0] # This is one of the possible coordinates for a point in the divisor
print X0
# 215/7795916928*b^5 - 14063/7795916928*b^4 - 323575/1948979232*b^3 + 16228415/1948979232*b^2 + 138336613/487244808*b - 531193663/121811202

"""
We take w(2*53) because it should act by -1 in x2 and by 1 on the rest (or the opposite, as it happens, since we work projectively).
"""
M.<c>=NumberField(y^2+(2*53))
print M.class_number()
# 6
print factor(M.discriminant())
# -1 * 2^3 * 53

print L(-2*53).is_square()
# True
# So we can work in the extension L of M, which is unramified of course

alpha = L(-2*53).sqrt()
Lrel = L.relativize(alpha,['e','c'])
M = Lrel.base_field()
c = M.gen()
abs_to_rel = Lrel.structure()[1]
print factor(Lrel.relative_discriminant())
# 1
"""
Messy part now. The points in the divisor should generate the HCF of M.
In other words, they should be unramified
"""
x3sq0 = abs_to_rel(-f0.subs(x0=X0).constant_coefficient()/2)

# Since L is unramified over M we know that L is inside H, the Hilbert Class Field of M. We
# must obtain H by taking the square root of x3sq, after adjusting a1

# We try to create take the square root and check that it is unramified. We also need that
# the element is not a square, because its root must generate the HCF.
a10=1
x3sq01=x3sq0*a10
MMz.<Z>=PolynomialRing(Lrel)
MM.<z> = Lrel.extension(Z^2-x3sq01)
print factor(MM.relative_discriminant().absolute_norm())

# The problematic prime is 3 (and maybe we need to adjust by -1 as well).
a10 = -3 # Note that 2*3*53 also works, since they differ by a square in M!
x3sq01=x3sq0*a10
MMz.<Z>=PolynomialRing(Lrel)
MM.<z> = Lrel.extension(Z^2-x3sq01)
x = MM.absolute_polynomial().parent().gen()
MMabs.<z> = NumberField(4096*MM.absolute_polynomial().subs(x=1/2*x))
MMrel = MMabs.relativize(MMabs(-106).sqrt(),names='h,i')
print factor(MMrel.relative_discriminant().absolute_norm())

# We took the -3 so that the extension is unramified (note that 3 alone does not work).

"""
Up to squares it is a1=-3
"""

# Finally, we need to find the factors of 2 and 53. This is done using the local data. In fact it
# is enough in this case to look at p = 53 and the valuations of the coefficients involved
# (which are both 0) to conclude that the values of a0 and a1 are good as we found them.

#######
# After finding the proper twist, which is
# a0 = -2*3, a1 = -3
# We get

SR0 = f.parent().base_ring()
phi = SR0.hom([-2*3,-3,0,0], codomain = QQ, check = False)
fgood0 = f.map_coefficients(phi)
ggood0 = g.map_coefficients(phi)

# To fix the bad reduction of the model at 3
fgood,ggood = substitute([fgood0,ggood0],x0=3*x0,x1=3*x1)

print fgood
print ggood

# 6*x0^2 + 36*x0*x1 - 51*x1^2 - 36*x2^2 - 2*x3^2
# 5*x0^3 + 33*x0^2*x1 + 16*x1^3 - x0*x3^2 - 5*x1*x3^2

save([ fgood, ggood ],'equations_53_2.sobj')
fgood,ggood = load('equations_53_2.sobj')


# Crazy tests
S106=ModularForms(Gamma0(106),2).new_subspace()

magma.eval('P4<x0,x1,x2,x3> := ProjectiveSpace(Integers(),3)')
magma.eval('f := %s'%fgood)
magma.eval('g := %s'%ggood)
magma.eval('C:=Curve(P4,[f,g])')

for n in filter(lambda n:ZZ(n).is_prime(),range(10000)):
    print n
    magma.eval('Pn:=%s+1-#RationalPoints(BaseChange(C,GF(%s)))'%(n,n));
    Pn=magma('Pn')
    if Pn != S106.hecke_matrix(n).trace():
        print 'n = %s fails!'%n

