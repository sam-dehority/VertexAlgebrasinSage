"""
Vertex Algebra Element

AUTHORS:

- Samuel DeHority (2023-10-??): Initial implementation.


Derived from the Lie conformal algebras module of SageMath 9.5 originally contirbuted by Reimundo Heluani.
"""
# *****************************************************************************
#       Copyright (C) 2019 Samuel DeHority <spd2133@columbia.edu>

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************
from sage.arith.misc import (factorial, binomial)
from sage.misc.misc_c import prod
from sage.misc.repr import repr_lincomb
from sage.misc.latex import latex
from sage.modules.with_basis.indexed_element import IndexedFreeModuleElement
from .normal_ordering_algebra_element import NOAWithGeneratorsElement
from sage.rings.integer import Integer

from sage.arith.misc import binomial
from sage.sets.family import Family
from sage.structure.parent import Parent
from sage.structure.element import Element
from .finitely_freely_generated_noa import FinitelyFreelyGeneratedNOA
from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
from sage.structure.indexed_generators import (IndexedGenerators,
                                               standardize_names_index_set)



class VAWithOPECoefficientsElement(NOAWithGeneratorsElement):
    """
    An element of a Vertex algebra with specified OPEs on generators.
    """


    def no_product(self, x):
        elt = self.parent().from_dict

        def no_term(t1,t2):
            s1,s2 = t1.leading_support(), t2.leading_support()
            c1,c2 = t1.monomial_coefficients()[s1], t2.monomial_coefficients()[s2]
            sc = self.parent().structure_coefficients()
            if not s1.is_NO() and not s2.is_NO() and not s1 == s1.parent().one() and not s2 == s2.parent().one():
                a,k = s1.value[0]
                b,m = s2.value[0]
                if (a,b) in sc.keys() and m == 0:
                    if k >= 0 and -k-1 in sc[(a,b)].keys():
                        return c1 * c2 * elt(sc[(a,b)][-k-1])
                if (a, (b,m)) in sc.keys() and k == 0:
                    if m >= 0 and -1 in sc[(a,b)].keys():
                        return c1 * c2 * elt(sc[(a,(b,m))][-1])
            return c1 * c2 * self.parent().monomial( s1.no_product(s2) )
        return sum ( no_term(a,b) for a in self.terms() for b in x.terms())

    def T(self,n = 1):
        r"""
        The derivative of this element.

        INPUT:

        We use the *divided powers* notation
        `T^{(j)} = \frac{T^j}{j!}`.

        EXAMPLES::

            sage: betagamma_dict = {('β','γ'):{0:{('K',0):1}}, ('β', 'β'): {},('γ', 'γ'): {} }
            sage: V = VertexAlgebra(QQ, betagamma_dict, names=('β','γ'), central_elements=('K',))
            sage: β = V.gen('β')
            sage: γ = V.gen('γ')
            sage: β.T()
            T^(1)β
            sage: x = β.n_product(γ, -1); x
            :βγ:
            sage: x.T()
            :T^(1)βγ: + :βT^(1)γ:
            sage: γ.T(4)
            24*T^(4)γ


        """
        if n <0:
            raise ValueError("No negative powers of derivatives")
        elif n == 0:
            return self
        elif n == 1:
            elt = self.parent().from_dict

            if self == self.parent().zero():
                return self.parent().zero()

            if self.is_monomial():
                p = self.parent()
                s = self.leading_support()
                if p.monomial(s) in p.central_elements():
                    return p.zero()
                coef = self._monomial_coefficients[s]
                t = s.value
                if len(t) == 0:
                    return p.zero()
                elif len(t) == 1:
                    sc = self.parent().structure_coefficients()
                    if t[0][0] in self.parent()._central_elements:
                        return p.zero()
                    if (t[0][0], '1') in sc.keys(): 
                        if -1 in sc[(t[0][0], '1')].keys():
                            return coef * elt(sc[(t[0][0], '1')][-1])
                    ts = s.parent().gen(t[0][0], t[0][1] + 1 )
                    return coef * (t[0][1] + 1) * p.monomial(s.parent().gen(t[0][0], t[0][1] + 1))
                else: 
                    l = t[0]
                    r = t[1] 
                    return p(coef * ( p.monomial(l).T().no_product(p.monomial(r)) + p.monomial(l).no_product(p.monomial(r).T()) ))
            return sum(mon.T() for mon in self.terms())
        else:
            return (self.T()).T(n -1)

    def n_product(self, other, n):
        r"""
        Returns the n-th product of self and other. 

        This calculates ``a_{(n)}b``, the nth products of fields using
        strucutral properties of vertex algebras and the noncommutative Wick formula. 

        INPUT:

        - ``other`` - an element of a vertex algebra. The term b to find the product with 

        - ``n`` - an Integer; determines which product to take. 

        EXAMPLES::

            sage: betagamma_dict = {('β','γ'):{0:{('K',0):1}}, ('β', 'β'): {},('γ', 'γ'): {} }
            sage: V = VertexAlgebra(QQ, betagamma_dict, names=('β','γ'), central_elements=('K',))
            sage: β = V.gen('β')
            sage: γ = V.gen('γ')
            sage: β.n_product(γ,0)
            K
            sage: γ.n_product(β,0)
            -K

        We also see the first steps of Wick's theorem in the commutative case. 

            sage: x = β.n_product(γ, -1); x
            :βγ:
            sage: β.n_product(x, 0)
            :βK:
            sage: x.n_product(β, 0)
            -:Kβ:
        """
        elt = self.parent().from_dict

        if n == -1:
            return self.no_product(other)
        elif n < -1:
            raise NotImplementedError
        else:
            p = self.parent()
            if self.is_monomial() and other.is_monomial():
                if self.is_zero() or other.is_zero():
                    return elt({})
                s_coeff = p._s_coeff

                s1,s2 = self.leading_support(), other.leading_support()
                c1,c2 = self.monomial_coefficients()[s1], other.monomial_coefficients()[s2]
                sc = self.parent().structure_coefficients()

                if not s1.is_NO() and not s2.is_NO():
                    if s1 == p._NOPS.one() or s2 == p._NOPS.one():
                        return p.zero()
                    a, k = s1.value[0]
                    b, m = s2.value[0]

                    if m == 0 and k == 0: 
                        if p.monomial(s1) in p.central_elements() or p.monomial(s2) in p.central_elements():
                            return p.zero()
                        if (a,b) in sc.keys():
                            return p.base_ring()(c1 * c2) * p.from_dict(sc[(a,b)].get(n, {}))._normalize_central()
                        elif a in p.central_elements() or b in p.central_elements():
                            return p.zero()
                        else:
                            if not (b,a) in sc.keys():
                                raise KeyError(f"OPE {a}(z){b}(w) not defined")
                            ba_OPE = sc[(b,a)]
                            if ba_OPE == {}:
                                return p.zero()
                            pole = max(ba_OPE.keys())
                            return p(sum ( c1 * c2 * (-1)**(1 + p._index_parity[a]*p._index_parity[b] + j + n) * ( p.monomial(s2).n_product(p.monomial(s1),n + j )  ).T(j) / p.base_ring()(factorial(j))  for j in range(pole + 2)))._normalize_central()
                    elif m == 0:
                        return c1 * (-n) * p.base_ring()(1/k) * p.gen(a,k-1).n_product(other, n - 1)
                    else: 
                        return c1 * c2 * p.base_ring()(1/m) * (p.monomial(s1)).n_product(p.gen(b,m-1), n ).T()._normalize_central() + c1 * c2 * p.base_ring()(1/m) * n * (p.monomial(s1)).n_product(p.gen(b,m-1), n-1 )._normalize_central() 
                elif s2.is_NO():
                    s2l = s2.value[0]
                    s2r = s2.value[1]
                    b = p.monomial(s2l)
                    c = p.monomial(s2r)
                    t1 = p(c2 * ( self.n_product(p.monomial(s2l), n) ).no_product(p.monomial(s2r)))
                    t2 = p(c2 * (-1)**(p.monomial_parity(s1)*p.monomial_parity(s2l))* b.no_product( self.n_product(c , n)))
                    t3 = p(c2 * sum ( binomial(n,j) * (self.n_product(b, j).n_product(c, n-1-j)) for j in range(n) ))
                    return (t1 + t2 + t3)._normalize_central()
                else: 
                    def max_pole(m1):
                        if not m1.is_NO():
                            a,k = m1.value[0]
                            b,m = s2.value[0]
                            return max(list(sc.get((a,b),{}).keys()) + list(sc.get((b,a),{}).keys()), default = 1 ) + k + m
                        else:
                            return max_pole(m1.value[0]) + max_pole(m1.value[1])
                    max_pole_order = max_pole(s1)
                    const =  c2 * (-1) * (-1)**( p.monomial_parity(s1)*p.monomial_parity(s2))
                    out = p.zero()
                    for j in range(max_pole_order + 2):
                        out += p((-1)**(j + n) *p.base_ring()(1/factorial(j)) * (p.monomial(s2).n_product(self, n + j )).T(j))
                    return const * out._normalize_central()
            outlist = [i.n_product(j, n) for i in self.terms()
                        for j in other.terms()]

            return p(sum(outlist))._normalize_central()

    def OPE(self, other, cc = None): 
        r"""
        Returns the singular part of the OPE of self with other. 

        INPUT: 

        --``other`` - a field of the VOA

        --``cc``- a tuple of central charges. (Default: None)

        OUTPUT: The Operator Product Expansion of the fields

        EXAMPLES::
        
        The OPE of composite fields can be calculated. In the free case this is Wick's formula. 

            sage: betagamma_dict = {('β','γ'):{0:{('K',0):1}}, ('β', 'β'): {},('γ', 'γ'): {} }
            sage: V = VertexAlgebra(QQ, betagamma_dict, names=('β','γ'), central_elements=('K',))
            sage: β = V.gen('β')
            sage: γ = V.gen('γ')
            sage: x = β.n_product(γ, -1)
            sage: x.OPE(β)
            -:Kβ:(w)/(z-w)

        Let's verify the OPE of the background stress tensor in the rank 1 free boson. 

            sage: freeboson_dict = {('α','α'):{1:{('C',0):1}}}
            sage: V = VertexAlgebra(QQ, freeboson_dict, names=('α'), central_elements=('C',))
            sage: V.inject_variables()
            Defining α
            sage: T = 1/2 * α.no_product(α); T
            1/2*:αα:
            sage: T.OPE(T,cc = (1,))
            (1/2*:Tαα:(w) + 1/2*:αTα:(w))/(z-w) + :αα:(w)/(z-w)^2 + 1/2/(z-w)^4

        """
        sc = self.parent().structure_coefficients()
        def max_pole(s1, s2):
            if not s1.is_NO():
                if not s2.is_NO():
                    a,k = s1.value[0]
                    b,m = s2.value[0]
                    return max(list(sc.get((a,b),{}).keys()) + list(sc.get((b,a),{}).keys()), default = 1 ) + k + m
                else:
                    return max_pole(s1, s2.value[0]) + max_pole(s1,s2.value[1])
                max_pole_order = max_pole(s1)
            else:
                return max_pole(s1.value[0], s2) + max_pole(s1.value[0],s2)
                max_pole_order = max_pole(s1)
        pole_order = max( [max_pole(s1,s2) for s1 in self.support() for s2 in other.support()], default = 0)
        if cc is not None: 
            out_dict = { i: self.n_product(other,i).eval_cc(cc) for i in range(pole_order + 1) }
            out_dict_nozero = {i : out_dict[i] for i in out_dict.keys() if out_dict[i] != self.parent().zero()}
            return OperatorProductExpansion(self, other, out_dict_nozero)
        
        out_dict = { i: self.n_product(other,i) for i in range(pole_order + 1) }
        out_dict_nozero = {i : out_dict[i] for i in out_dict.keys() if out_dict[i] != self.parent().zero()}
        return OperatorProductExpansion(self, other, out_dict_nozero)
        
    def is_central(self):
        r"""
        Returns whether self is central. 
        """
        sup_central = lambda s : s.value == () or self.parent().monomial(s) in self.parent().central_elements() if not s.is_NO() else sup_central(s.value[0]) and sup_central(s.value[1])
        return all(sup_central(s) for s in self.support())


class OperatorProductExpansion(Element):
    r"""
    Base class for an approximation to an operator product expansion.

    These arise as outputs of an OPE calculated from fields in a vertex algebra. 

    This will almost always only encode the singular part of an OPE but it is a priori more general. In particular, it will sometimes be used to encode the fact that normally ordered products of some fields are other generating fields. 

    """
    def __init__(self, F1, F2, ope_coeffs):
        r"""
        Specifies the OPE of fields F1 and F2 to be the 

        INPUT:

        - ``F1`` -- integer (default: `1`); the description of the
        argument ``x`` goes here. If it contains multiple lines, all
        the lines after the first need to begin at the same indentation
        as the backtick.

        - ``F2`` -- integer (default: `2`); the description of the
        argument ``y``

        - ``ope_coeffs`` -- A dictionary {i:c_i} whose indices are integers i and whose ith value is the field formed by the ith product of the two fields. 

        OUTPUT: An approximation to an Operator Product Expansion specified by this data. 

        EXAMPLES::

        This example illustrates ... ::

            sage: 2+2
            4
        """
        self.L = F1
        self.R = F2
        self.ope_coeffs = ope_coeffs
        Element.__init__(self, OperatorProductExpansions(F1.parent()))


    def vertex_algebra(self):
        r"""
        Returns the underling vertex algebra in which `self` is an OPE. 
        """
        return self.L.parent()

    def _repr_(self):
        if self.ope_coeffs == {}:
            return repr(self.L.parent().zero())
        def term_w(t):
            if t.is_central():
                return repr(t)
            else: 
                return repr(t) + '(w)'
        def coeff(c):
            if len(c.terms()) > 1:
                return '(' + ' + '.join(term_w(t) for t in c.terms()) + ')'
            else: 
                return ''.join(term_w(t) for t in c.terms()) 
        return ' + '.join( coeff(self.ope_coeffs[i])+ '/(z-w)^'+str(i+1)  if i > 0 else coeff(self.ope_coeffs[i])+ '/(z-w)' for i in reversed(self.ope_coeffs.keys()))

    def _latex_(self):
        if self.ope_coeffs == {}:
            return latex(self.L.parent().zero())
        def term_w(t):
            if t.is_central():
                return latex(t)
            else: 
                return latex(t) + '(w)'
        def coeff(c):
            if len(c.terms()) > 1:
                return '(w) + '.join(latex(t) for t in c.terms()) + '(w)'
            else: 
                return ''.join(term_w(t) for t in c.terms()) 
        return ' + '.join('\\frac{{' + coeff(self.ope_coeffs[i])+ '}}{{(z-w)^{{'+str(i+1) + '}}}}' if i > 0 else '\\frac{{' + coeff(self.ope_coeffs[i])+ '}}{{z-w}}'  for i in reversed(self.ope_coeffs.keys()) )


class OperatorProductExpansions(Parent):
    r"""
    Base class for an operator product expansion in a vertex algebra V. 
    """
    Element = OperatorProductExpansion
    def __init__(self,V):
        self._VOA = V
        Parent.__init__(self)

    def _repr(self):
        return "Operator Product Expansions of fields in " + repr(self._VOA)
