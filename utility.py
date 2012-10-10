#########################################################################
#       Copyright (C) 2011 Cameron Franc and Marc Masdeu
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#                  http://www.gnu.org/licenses/
#########################################################################


from itertools import product,chain
from sage.rings.all import Qp

def getcoords(E,u,prec=20,R = None):
    if R is None:
        R = u.parent()
        u = R(u)
    p = R.prime()
    jE = E.j_invariant()

    # Calculate the Tate parameter
    E4 = EisensteinForms(weight=4).basis()[0]
    Delta = CuspForms(weight=12).basis()[0]
    j = (E4.q_expansion(prec+7))**3/Delta.q_expansion(prec+7)
    qE =  (1/j).power_series().reversion()(R(1/jE))

    # Normalize the period by appropriate powers of qE
    un = u * qE**(-(u.valuation()/qE.valuation()).floor())

    precn = (prec/qE.valuation()).floor() + 4
    # formulas in Silverman II (Advanced Topics in the Arithmetic of Elliptic curves, p. 425)
    xx = un/(1-un)**2 + sum( [qE**n*un/(1-qE**n*un)**2 + qE**n/un/(1-qE**n/un)**2-2*qE**n/(1-qE**n)**2 for n in range(1,precn) ])
    yy = un**2/(1-un)**3 + sum( [qE**(2*n)*un**2/(1-qE**n*un)**3 - qE**n/un/(1-qE**n/un)**3+qE**n/(1-qE**n)**2 for n in range(1,precn) ])


    sk = lambda q,k,pprec: sum( [n**k*q**n/(1-q**n) for n in range(1,pprec+1)] )
    n = qE.valuation()
    precp = ((prec+4)/n).floor() + 2;

    tate_a4 = -5  * sk(qE,3,precp)
    tate_a6 = (tate_a4 - 7 * sk(qE,5,precp) )/12
    Eq = EllipticCurve([R(1),R(0),R(0),tate_a4,tate_a6])

    C2 = (Eq.c4() * E.c6()) / (Eq.c6() * E.c4())

    C = our_sqrt(C2,R)
    s = (C - R(E.a1()))/R(2)
    r = (s*(C-s) - R(E.a2())) / 3
    t =  (r*(2*s-C)-R(E.a3())) / 2

    return  ( r + C2 * xx, t + s * C2 * xx + C * C2 * yy )


from sage.modular.modform.constructor import EisensteinForms, CuspForms

def tate_parameter(E, p, prec = 20, R = None):
    if R is None:
        R = Qp(p,prec)
    jE = E.j_invariant()
    E4 = EisensteinForms(weight=4).basis()[0]
    Delta = CuspForms(weight=12).basis()[0]
    j = (E4.q_expansion(prec+3))**3/Delta.q_expansion(prec+3)
    jinv = (1/j).power_series()
    q_in_terms_of_jinv = jinv.reversion()
    return q_in_terms_of_jinv(R(1/E.j_invariant()))



def our_sqrt(x,K):
    if x==0:
        return x
    x=K(x)
    p=K.base_ring().prime()
    valp = x.valuation(p)
    try:
        eK = K.ramification_index()
    except AttributeError:
        eK = 1
    valpi = eK * valp
    if valpi % 2 != 0:
        raise RuntimeError,'Not a square'
    x = p**(-valp) * x
    z=K.gen()
    deg=K.degree()
    found=False
    for avec in product(range(p),repeat=deg):
        y0 = avec[0]
        for a in avec[1:]:
            y0 = y0*z + a
        if((y0**2-x).valuation()>0):
            found=True
            break
    if found == False:
        raise RuntimeError,'Not a square'
    y1=y0
    y=0
    while y != y1:
        y=y1
        y1=(y**2+x)/(2*y)
    return K.uniformizer()**(ZZ(valpi/2)) * y

def our_log(x,prec = None):
    K=x.parent()
    if prec is None:
        prec=K.precision_cap()+10
    x0=x.unit_part()
    y=x0/K.teichmuller(x0)-1
    tmp=K(0)
    ypow=y
    for ii in range(1,prec+1):
        tmp+=(-1)**(ii+1)*ypow/ii
        ypow*=y
    return tmp

def our_exp(x,prec=None):
    K=x.parent()
    if prec is None:
        prec=K.precision_cap()+10
    tmp=K(1+x)
    xpow=x**2
    iifact=2
    for ii in range(3,prec):
        tmp+=xpow/iifact
        xpow*=x
        iifact*=ii
    return tmp

def my_algdep(z,n,prec = None):
    K = z.parent()
    p = K.prime()
    z = p**(-z.valuation(p))*z
    zpows = [K(1)]
    for ii in range(n):
        zpows.append(zpows[ii]*z)

    if prec is None:
        prec = z.precision_absolute()
    field_deg = K.degree()

    M = matrix(Qp(p,prec),field_deg,n+1)
    for ii in range(field_deg):
        for jj in range(n+1):
            M[ii,jj]=O(p^prec)
    for jj in range(n+1):
        V = zpows[jj]._ntl_rep().list()
        for ii in range(len(V)):
            M[ii,jj]+= ZZ(V[ii])+O(p^prec)

    argmax = None
    vmax = -1
    Rx = PolynomialRing(QQ,names = 'x')
    x = Rx.gens()[0]
    for ii in range(field_deg):
        lincomb = gp.lindep(M.row(ii).list())
        lincomb = Rx([lincomb[ii+1].sage() for ii in range(n+1)])
        newval = lincomb.subs(z).valuation()
        if newval > vmax:
            argmax = lincomb
            vmax = newval
    print vmax
    return argmax

def fix_deg_monomials(v,n):
    return [reduce(lambda x,y:x*y,[v[ii]**(part[ii]-1) for ii in range(len(v))]) for part in OrderedPartitions(len(v)+n,len(v))]


#The list of elements elts must be in the form [a1,a1^-1,a2,a2^{-1}, etc]
def free_group_words(elts,op=None,init=[1]):
    if op is None:
        op=lambda x,y:x*y
    allwords=[]

    ii=0
    n=1
    # Generate words of length 1
    for i in range(len(elts)):
        wd=[i,op(elts[i],init),[i]]
        ii+=1
        if ii%10000==0:
            print ii
        yield wd[1]
        #yield wd[1],n,wd[2]
        allwords.append(wd)

    # Generate longer words
    while True:
        n+=1
        newwords = []
        for pairs in allwords:
            leftind = pairs[0]
            if leftind % 2 == 0:
                omit = leftind+1
            else:
                omit = leftind-1
            for i in range(omit)+range(omit+1,len(elts)):
                wd=[i,op(elts[i],pairs[1]),[i]+pairs[2]]
                ii+=1
                if ii%10000==0:
                    print ii
                yield wd[1]
                #yield wd[1],n,wd[2]
                newwords.append(wd)
        allwords=newwords


#Act by a fractional linear transformation on an element of the p-adic upper half plane
# The parameter twist corresponds to applying a change of variables given by the
# matrix [1,0,twist,1]
def act_by_flt(g,Z,twist = 0):
    bb=g[0,1]
    btwist=bb*twist
    aa, dd=g[0,0]+btwist,g[1,1]-btwist
    cc=g[1,0]+(g[1,1]-aa)*twist
    try:
        return [(aa*z + bb)/(cc*z + dd) for z in Z]
    except TypeError:
        return (aa*Z + bb)/(cc*Z + dd)


def get_action_flt(twist):
    return lambda g,Z:act_by_flt(g,Z,twist)

def find_good_monomial(f):
    d=max(f.degrees())
    for x in f.parent().gens():
        x2d=x**d
        print 'Trying monomial ',x
        print 'Appears in degree',f.degree(x)
        print 'and the other deg is',(f-f.coefficient(x2d)*x2d).degree(x)

        if f.degree(x)>0 and (f-f.coefficient(x2d)*x2d).degree(x)==0:
            return x2d
    return None

# Finds relations among the modular forms in X
# Up to a given degree
def find_relations(X,dmax,prec,generators,h=0):
    genus=len(X)
    p=X[0].parent().prime()
    K=Qq(p^2,prec = prec, names = 'g')
    g=K.gen()
    max_num_monomials=binomial(genus+dmax-1,dmax)

    sys.stdout.flush()
    CEP=[]
    for ii in range(max_num_monomials+h):
        Pt=g+p*ii
        sys.stdout.write("#")
        sys.stdout.flush()
        CEP.append([f.modular_form(Pt) for f in X])

    V=[]
    for d in range(2,dmax+1):
        num_monomials=binomial(genus+d-1,d)
        A=Matrix(K,num_monomials+h,num_monomials,[fix_deg_monomials(CEP[ii][:num_monomials],d) for ii in range(num_monomials+h)])
        for v in V:
            # Find a suitable monomial to cancel higher degrees
            d0=v[0]
            f0=sum([x[0] for x in v[1]])
            xi2d=find_good_monomial(f0)
            if xi2d is None:
                raise RuntimeError,'Ooh too bad...the automated search did not work.'
            tmons=fix_deg_monomials(generators,d-d0)
            degdmons=fix_deg_monomials(generators,d)
            pos=[(xi2d*t,degdmons.index(xi2d*t)) for t in tmons]
            A=A.stack(Matrix(K,len(pos),num_monomials,dict([((ii,pos[ii][1]),1) for ii in range(len(pos))])))
        B=A.right_kernel().matrix()
        assert B.nrows()==1
        mons=fix_deg_monomials(generators,d)
        tmp=B.row(0)
        newV=filter(lambda x:x[1]!=0,zip(mons,tmp))
        print 'newV=',newV
        V.append((d,newV))
    return V


def find_invariants(genus,V,P):
    generators=P.gens()
    goodMons=list(chain.from_iterable([v[1] for v in V]))
    assert all([x[1]!=0 for x in goodMons])

    A=copy(Matrix(ZZ,len(goodMons),genus,[tuple(x[0].degrees()) for x in goodMons]).kernel().matrix())

    print 'A='
    print A

    n_invariants=A.nrows()
    goodcols=[]

    # Try to select columns to become dependent variables
    for ii in range(A.nrows()):
        found=False
        for jj in range(A.ncols()):
            if ZZ(A[ii,jj]).abs()==1 and all([all([A[i1,jj]*A[i1,j1]==0 for j1 in goodcols]) for i1 in range(ii+1,A.nrows())]):
                goodcols.append(jj)
                found=True
                break
        if not found: raise RuntimeError
        A.rescale_row(ii,A[ii,jj])
        assert A[ii,jj] == 1
        for i0 in range(ii)+range(ii+1,A.nrows()):
            A.add_multiple_of_row(i0,ii,-A[i0,jj])

    badcols=range(A.ncols())
    for x in goodcols:
        badcols.remove(x)

    ################
    # Just to gather more information
    print 'goodcols=',goodcols
    print 'badcols=',badcols
    for ii in range(A.nrows()):
        print 'ii=',ii
        r=A.row(ii)
        tmp=1
        for jj in range(A.ncols()):
            if(A[ii,jj]!=0):
                tmp*=goodMons[jj][1]**ZZ(A[ii,jj])
                if True:#jj<5:
                    print 'a%s^(%s)'%(jj,ZZ(A[ii,jj])),
                else:
                    print 'b%s^(%s)'%(jj-5,ZZ(A[ii,jj])),
        print '.'
        print 'tmp = %s'%tmp
        rat=algdep(tmp,1).roots(RationalField())[0][0]
        print 'rat=',factor(rat)
    ################

    S0=PolynomialRing(QQ,genus,names='a')
    S=S0.fraction_field()
    lst=[]
    for j0 in range(A.ncols()):
        try:
            lst.append(S.gen(badcols.index(j0)))
            print 'rat=',1
        except ValueError:
            ii=goodcols.index(j0)
            r=A.row(ii)
            tmp=1
            mon=1
            for jj in range(A.ncols()):
                if(A[ii,jj]!=0):
                    tmp*=goodMons[jj][1]**ZZ(A[ii,jj])
                    if jj!=j0:
                        mon*=S.gen(badcols.index(jj))**(-ZZ(A[ii,jj]))
            rat=algdep(tmp,1).roots(RationalField())[0][0]
            print 'mon = %s, rat = %s'%(mon,1/rat)
            lst.append(S(rat*mon))
    PolyS=P.change_ring(S)
    F=[]
    ii=0
    for d,v in V:
        f=PolyS(0)
        for x in filter(lambda x:x[1]!=0,v):
            f+=PolyS(lst[ii])*PolyS(x[0])
            ii+=1
        F.append(f*f.denominator())
    PolyS0=P.change_ring(S0)
    return [PolyS0(f) for f in F],lst

def substitute(F,**args):
    R=F[0].parent()
    tmp=[R(f.subs(**args)) for f in F]
    tmp = [lcm([x.denominator() for x in f.coefficients()])*f for f in tmp]
    return [1/f.content()*f for f in tmp]

def quick_subst(F,**args):
    R=F[0].parent()
    tmp=[R(f.subs(**args)) for f in F]
    return [f for f in tmp if f != 0]

def find_divisor(F,x):
    R=F[0].parent()
    gens=R.gens()
    y=gens[(gens.index(x)+1)%len(gens)]
    F1=[f.subs(dict([(x,0),(y,1)])) for f in F]
    S = PolynomialRing(RationalField(),names = 'y')
    y = S.gen(0)
    others=[]
    for f in F1:
        if list(f.degrees()).count(0)==len(gens)-1:
            # It means that it is really a single variable polynomial
            ii=list(f.degrees()).index(f.degree())
            xi=gens[ii]
            lst=[]
            for jj in range(len(gens)):
                if jj==ii:
                    lst.append(S.gen(0))
                else:
                    lst.append(0)
            phi=R.hom(lst,codomain=S,check=False)
            fone=phi(f)
            S0=S.base_extend((fone/fone.leading_coefficient()).root_field('a'))
            a=S0(fone).roots()[0][0]
        else:
            others.append(f)
    others=[f.subs(dict([(f.parent().gen(ii),a)])) for f in others]
    return others
