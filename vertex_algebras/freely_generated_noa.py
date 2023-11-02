"""
Freely Generated Normal Ordering Algebras

AUTHORS:

- Samuel DeHority (2019-08-09): Initial implementation
"""

#******************************************************************************
#       Copyright (C) 2019 Samuel DeHority <spd2133@columbia.edu>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from .normal_ordering_algebra_with_basis import NormalOrderingAlgebraWithBasis
from .normal_ordering_algebra_element import NOAWithGeneratorsElement
from sage.sets.non_negative_integers import NonNegativeIntegers
from sage.categories.cartesian_product import cartesian_product
from sage.rings.integer import Integer
from sage.sets.family import Family
from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
from sage.structure.indexed_generators import IndexedGenerators
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.misc.latex import latex
from sage.structure.element_wrapper import ElementWrapper
from sage.structure.unique_representation import UniqueRepresentation

from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
from sage.structure.indexed_generators import (IndexedGenerators,
                                               standardize_names_index_set)

class NormalOrderedProduct(ElementWrapper):
    """
    A normally ordered product. 
    """
    wrapped_class = tuple

    def no_product(self, x):
        r"""
        The normally ordered product of this element with another monomial. 

        INPUT: 

        - ``x``: A NormalOrderedProduct, the other field monomial. 

        OUTPUT: The normally ordered product of this field with ``x``. 

        EXAMPLES::

            sage: NOPS = NormalOrderedProducts(('A', 'B', 'C'))
            sage: a = (NOPS.gen('A',2)).no_product(NOPS.gen('B'));a
            :T^(2)AB:
        """
        ls = len(self.value)
        lx = len(x.value)
        if ls == 0:
            return x
        elif lx == 0:
            return self
        else:
            return NormalOrderedProduct(self.parent(), (self, x))

    def is_NO(self):
        r"""
        Returns true if self is a non-trivial normal-ordered product and not a generator. 

        EXAMPLES::

            sage: NOPS = NormalOrderedProducts(('A', 'B', 'C'))
            sage: a = (NOPS.gen('A',2)).no_product(NOPS.gen('B'))
            sage: a.is_NO()
            True
            sage: NOPS.gen('A', 4).is_NO()
            False

        """
        return len(self.value) >= 2
        # return isinstance( self.value[0], NormalOrderedProduct)

    def _repr_(self):
        ls = len(self.value)
        if ls == 0:
            return '1'
        elif ls == 1:
            m = self.value[0][1]
            return f'T^({m})'+str(self.value[0][0]) if m > 1 else ('T'+str(self.value[0][0]) if m == 1 else str(self.value[0][0]))
        else:
            return f":{self.value[0]}{self.value[1]}:"

    def _latex_(self):
        ls = len(self.value)
        if ls == 0:
            return '1'
        elif ls == 1:
            m = self.value[0][1]
            return f'\\partial^{{({m})}}'+str(self.value[0][0]) if m > 1 else ('\\partial^{{}} '+str(self.value[0][0]) if m ==1 else  str(self.value[0][0]))
        else:
            return f":{latex(self.value[0])}{latex(self.value[1])}:"

    def collect_central(self, centrals):
        r"""
        Collects central elements. 

        INPUT: 

        -- ``centrals`` - Tuple, of central elements 

        OUTPUT: 2-tule (l, s) consisiting of list l of central elements and s, which is normal-ordered product with central fields removed. 
        EXAMPLES::

            sage: x = NormalOrderedProducts(('A', 'B', 'C')).l_branch_from_list(['A','C', 'C', 'B', 'B', 'C']);x
            :A:C:C:B:BC:::::
            sage: x.collect_central(['C'])
            (['C', 'C', 'C'], :A:BB::)
        """
        t = self.value
        if len(t) == 1:
            return ([], self) if t[0][0] not in centrals else ([t[0][0]], self.parent().one())
        else: 
            r1 = t[0].collect_central(centrals)
            r2 = t[1].collect_central(centrals)
            return (r1[0] + r2[0], r1[1].no_product(r2[1]))
        
    def normalize_central(self, centrals): 
        r"""
        Returns a normalized form of self. 

        INPUT: 

        -- ``centrals`` - Tuple, of central elements 

        OUTPUT: Normal form of self with all central elements in the front ordered with respect to the ordering on centrals

        EXAMPLES::

            sage: x = NormalOrderedProducts(('A', 'B', 'C')).l_branch_from_list(['A','C', 'C', 'B', 'B', 'C']);x
            :A:C:C:B:BC:::::
            sage: x.normalize_central(['C'])
            ::C:CC:::A:BB:::
        """
        cs, pruned = self.collect_central(centrals)
        cs.sort(key = centrals.index)
        return self.parent().l_branch_from_list(cs).no_product(pruned)


class NormalOrderedProducts(Parent):
    r"""
    Parent class for the normal ordering magma. This class should not be used directly but only be called from FreelyGeneratedVertexAlgebra. 
    """
    Element = NormalOrderedProduct

    def __init__(self, index_set, **kwds):
        """
        Initialize self.
        """
        self._index_set = index_set
        self._gens = Family(index_set)
        self._gen_indices = cartesian_product([index_set, NonNegativeIntegers()])
        Parent.__init__(self)
    
    def one(self):
        r"""
        Returns the identity field, labelled by 1. 

        EXAMPLES::

            sage: NOPS = NormalOrderedProducts(('A', 'B', 'C'))
            sage: NOPS.one()
            1

        """
        return self.element_class(self, ())


    def _element_constructor_(self, x=None):
        """
        Create an normally ordered field from ``x``.

        EXAMPLES::

            sage: NOPS = NormalOrderedProducts(('A', 'B', 'C'))
            sage: NOPS(NOPS.gen('B', 3))
            T^(3)B
        """
        if x is None:
            return self.one()
        if x in self._index_set:
            raise TypeError("unable to convert {!r}, use gen() instead".format(x))
        return self.element_class(self, x)

    def cardinality(self):
        if self._indices.cardinality() == 0:
            return ZZ.one()
        return infinity

    def _repr_(self):
        return f"Normally ordered products in fields {self._index_set} and their derivatives"

    def gen(self,x, m = 0):
        if x  not in self._gens:
            raise IndexError("{} is not in the index set".format(x))
        return self.element_class(self, ((x,m), ))
    
    def from_tuple(self, t):
        r"""
        Returns a normally ordered product from a binary tree represented using 2-tuples 
        ((('a_1', m_1), ('a_2', m_2)), ('a_3', m_3))
        so that the lowest-order tuples give generators. 

        EXAMPLES::

            sage: NOPS = NormalOrderedProducts(('A', 'B', 'C'))
            sage: NOPS.from_tuple((('A',2), (('B' ,0), ('B', 0))))
            :T^(2)A:BB::
        """
        if t[0] in self._index_set:
            return(self.gen(t[0], t[1]))
        else: 
            return self.element_class(self, ( self.from_tuple(t[0]), self.from_tuple(t[1])  ) )

    def l_branch_from_list(self, l ):
        r"""
        A left branching NO product from list l of names

        INPUT: 

        -- ``l``- a list. Contains elements [l1,...,lk] for form normal ordered product 

        OUTPUT: Element :l_1:l_2:...:l_{k-1}l_k::..:

        EXAMPLES::

            sage: NormalOrderedProducts(('A', 'B', 'C')).l_branch_from_list(['A', 'B', 'B', 'C'])
            :A:B:BC:::
        """
        if len(l) == 0:
            return self.one()
        return self.gen(l[0]).no_product(self.l_branch_from_list(l[1:]))



class FreelyGeneratedNormalOrderingAlgebra(NormalOrderingAlgebraWithBasis):
    """
    Base class for a central extension of a freely generated Lie
    conformal algebra.

    This class provides minimal functionality, it sets up the
    family of Lie conformal algebra generators.
    """

    Element = NOAWithGeneratorsElement

    def __init__(self, R, names = None, central_elements=None, category=None,
                 element_class=None, prefix=None, **kwds):
        """
        Initialize self.
        """

        names, index_set = standardize_names_index_set(names)
        if central_elements is None:
            central_elements = tuple()
    
        if names is not None and names != tuple(index_set):
            names2 = names + tuple(central_elements)
            index_set2 = DisjointUnionEnumeratedSets((index_set,
                Family(tuple(central_elements))))
            d = {x:index_set2[i] for i,x in enumerate(names2)}
            try:
                #If we are given a dictionary with names as keys,
                #convert to index_set as keys
                s_coeff = {(d[k[0]],d[k[1]]):{a:{(d[x[1]],x[2]):
                    s_coeff[k][a][x] for x in
                    s_coeff[k][a]} for a in s_coeff[k]} for k in s_coeff.keys()}

            except KeyError:
                # We assume the dictionary was given with keys in the
                # index_set
                pass

        if names is not None and central_elements is not None:
            all_names = names + tuple(central_elements)

        self._generators = Family(index_set)
        E = cartesian_product([index_set, NonNegativeIntegers()])

        if central_elements is not None:
            self._central_elements = Family(central_elements)
        else:
            self._central_elements = tuple()
        full_index_set = index_set  if central_elements is None else DisjointUnionEnumeratedSets( (index_set, Family(central_elements)))
        self.full_index_set = full_index_set

        self._all_generators = Family(full_index_set)

        NOPS = NormalOrderedProducts(full_index_set)

        self._NOPS = NOPS

        super().__init__(R, basis_keys=NOPS, element_class=element_class,
                         category=category, prefix=prefix, **kwds)

    def normal_ordering_algebra_generators(self):
        """
        The generators of this Lie conformal algebra.

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C', ))
            sage: V.gens()['A']
            A
            sage: V.gens()['C']
            C
        """
        F = Family(self._all_generators,
                      lambda i: self.monomial(self._NOPS.gen(i, 0)),
                      name="generator map")
        # from sage.categories.sets_cat import Sets
        # if F in Sets().Finite():
        #     return tuple(F)
        return F

    def central_elements(self):
        """
        The central generators of this Normal ordering algebra.

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C1','C2' ))
            sage: V.central_elements()
            (C1,C2)
        """
        return Family(self._central_elements,
                      lambda i: self.monomial(self._NOPS.gen(i)),
                      name="central_element map")

    def _repr_(self):
        """
        The name of this vertex algebra
        """
        return f"Normal ordering algebra generated by {NormalOrderedProducts(self.full_index_set)} over {self.base_ring()}"