"""
Finitely and Freely Generated Normal Ordering Algebras.

AUTHORS:

- .
"""

#******************************************************************************
#       Copyright (C)
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.misc.cachefunc import cached_method
# from sage.categories.vertex_algebras import LieConformalAlgebras
from .freely_generated_noa import \
                                            FreelyGeneratedNormalOrderingAlgebra

from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
from sage.structure.indexed_generators import (IndexedGenerators,
                                               standardize_names_index_set)

class FinitelyFreelyGeneratedNOA(FreelyGeneratedNormalOrderingAlgebra):
    """
    Abstract base class for finitely generated Lie conformal
    algebras.

    This class provides minimal functionality, simply sets the
    number of generators.
    """
    def __init__(self, R, central_elements=None, category=None,
                 element_class=None, prefix=None, names=None, latex_names=None,
                 **kwds):
        """
        Initialize self.
        """
        # default_category = LieConformalAlgebras(R).FinitelyGenerated()
        # try:
        #     category = default_category.or_subcategory(category)
        # except ValueError:
        #     category = default_category.Super().or_subcategory(category)

        # from sage.categories.sets_cat import Sets
        # if index_set not in Sets().Finite():
        #     raise TypeError("index_set must be a finite set")

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


        super().__init__(R, names=names,central_elements=central_elements,
                         category=category, element_class=element_class,
                         prefix=prefix, **kwds)
        self._ngens = len(self._generators)
        self._names = names
        self._latex_names = latex_names

    def _an_element_(self):
        """
        An element of this Lie conformal algebra.

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C1','C2' ))
            sage: V.an_element()
            A + B + C1 + C2
        """
        return self.sum(self.gens())

    def ngens(self):
        """
        The number of generators of this Lie conformal algebra. Only counts the non-central generators. 

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C', ))
            sage: V.ngens()
            2
        """
        return self._ngens

    @cached_method
    def gens(self):
        """
        The generators for this normal ordering algebra.

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C', ))
            sage: V.gens()['A']
            A
            sage: V.gens()['C']
            C
        """
        return self.normal_ordering_algebra_generators()

    @cached_method
    def central_elements(self):
        """
        The central elements of this normal ordering algebra as a tuple.

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C1','C2' ))
            sage: V.central_elements()
            (C1,C2)
        """
        return tuple(FreelyGeneratedNormalOrderingAlgebra.central_elements(self))

    def gen(self, x, n = 0):
        r"""
        Returns the nth divided power of the of the NOA generator with label X. 

        INPUT:

        - ``x`` -- The index of the field

        - ``n`` -- An integer (Default: 0), which divided power. 

        EXAMPLES::

            sage: V = FinitelyFreelyGeneratedNOA(QQ, names = ('A','B'), central_elements=('C', ))
            sage: V.gen('B')
            B
            sage: V.gen('A', 6)
            T^(6)A
            sage V.gen('A', 6).T()
            7*T^(7)A
        """
        if n == 0:
            return self.gens()[x]
        elif n < 0:
            return self.zero()
        else: 
            return self.gen(x, n-1).T() / self.base_ring()(n)
