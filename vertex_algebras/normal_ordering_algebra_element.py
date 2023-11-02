"""
Normal Ordering Algebra Element

AUTHORS:

- Samuel DeHority (2023-10-20): Initial implementation.


Derived from the Lie conformal algebras module of SageMath 9.5 originally contirbuted by Reimundo Heluani.
"""
# *****************************************************************************
#       Copyright (C) 2023 Samuel DeHority <spd2133@columbia.edu>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************
from sage.arith.misc import factorial
from sage.misc.misc_c import prod
from sage.misc.repr import repr_lincomb
from sage.misc.latex import latex
from sage.modules.with_basis.indexed_element import IndexedFreeModuleElement


class NOAWithGeneratorsElement(IndexedFreeModuleElement):
    """
    The element class of a Normal ordering algebra with a
  set of generating fields.
    """

    def no_product(self, x):
        r"""
        The normal ordered product of self and `x`. 

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C', ))
            sage: y = 4*V.gen('A',2 ) + V.gen('B'); y
            4*T^(2)A + B
            sage: y.no_product(V.gen('A'))
            4*:T^(2)AA: + :BA:
        """
        def no_term(t1,t2):
            s1,s2 = t1.leading_support(), t2.leading_support()
            c1,c2 = t1.monomial_coefficients()[s1], t2.monomial_coefficients()[s2]
            return c1 * c2 * self.parent().monomial( s1.no_product(s2) )
        return sum ( no_term(a,b) for a in self.terms() for b in x.terms())

    def T(self):
        r"""
        The derivative of this element.

        We use the *divided powers* notation
        `T^{(j)} = \frac{T^j}{j!}`.

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C', ))
            sage: y = 4*V.gen('A',2 ) + V.gen('B'); y
            4*T^(2)A + B
            sage: y.T()
            12*T^(3)A + T^(1)B
            sage: V.gen('A').T().T().T()
            6*T^(3)A
            sage: V.gen('C').T()
            0
        """
        if self.is_monomial():
            p = self.parent()
            s = self.leading_support()
            coef = self._monomial_coefficients[s]
            t = s.value
            if len(t) == 0:
                return p.zero()
            elif len(t) == 1:
                if t[0][0] in self.parent()._central_elements:
                     return p.zero()
                else:
                    ts = s.parent().gen(t[0][0], t[0][1] + 1 )
                    return coef * (t[0][1] + 1 ) * p.monomial(ts)
            else: 
                l = t[0]
                r = t[1] 
                return coef * ( p.monomial(l).T().no_product(p.monomial(r)) + p.monomial(l).no_product(p.monomial(r).T()) )
        return sum(mon.T() for mon in self.terms())

    def is_monomial(self):
        """
        Whether this element is a monomial.

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C', ))
            sage: y = 4*V.gen('A',2 ) + V.gen('B'); y
            4*T^(2)A + B
            sage: y.is_monomial()
            False
            sage: x = 9*V.gen('A', 7).no_product(V.gen('B'))
            9*:T^(7)AB:
            sage: x.is_monomial()
            True
        """
        return len(self._monomial_coefficients) == 1 or self.is_zero()

    def _normalize_central(self):
        r"""
        Returns the same element with central terms normalized. 
        """

        out = self.parent().zero()
        central_elements = self.parent().central_elements()
        central_names = [c.leading_support().value[0][0] for c in central_elements]
        out = self.parent().zero()
        for t in self.support():
            coeff = self.monomial_coefficients()[t]
            tnorm = t.normalize_central(central_names)
            out +=  coeff * self.parent().monomial(tnorm)
        return self.parent()(out)


    def eval_cc(self, k):
        r"""
        Evaluates the central elements at elements of base ring. 

        INPUT:

            -- ``k``- tuple of elements of base ring

        OUTPUT: The element with central terms evaluated. 

        EXAMPLES::

            sage: freeboson_dict = {('α','α'):{1:{('C',0):1}}}
            sage: V = VertexAlgebra(QQ, freeboson_dict, names=('α'), central_elements=('C',))
            sage: V.inject_variables()
            Defining α
            sage: T = 1/2 * α.no_product(α); T
            sage: cterm = T.OPE(T).ope_coeffs[3]; cterm
            1/2*:CC:
            sage: cterm.eval_cc((1,))
            1/2
        """
        central_elements = self.parent().central_elements()
        central_names = [c.leading_support().value[0][0] for c in central_elements]
        out = self.parent().zero()
        eval_list = lambda l : self.parent().base_ring()(prod( k[ central_names.index(n)] for n in l  ))
        for t in self.support():
            coeff = self.monomial_coefficients()[t]
            clist, pruned = t.collect_central(central_names)
            out += eval_list(clist) * coeff * self.parent().monomial(pruned)
        return self.parent()(out)