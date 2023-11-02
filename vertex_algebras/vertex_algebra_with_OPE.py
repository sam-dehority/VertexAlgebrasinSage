"""
Vertex Algebra specified by Operator Product Expansion

AUTHORS:

- Samuel DeHority (2023-10-??): Initial implementation.

Derived from the Lie conformal algebras module of SageMath 9.5 originally contirbuted by Reimundo Heluani.
"""

# *****************************************************************************
#       Copyright (C) 
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************
#
#
#
#
#
#


from sage.arith.misc import binomial
from sage.sets.family import Family
from .vertex_algebra_element import (VAWithOPECoefficientsElement,          OperatorProductExpansion, OperatorProductExpansions)
# from vertex_algebras import VertexAlgebra
from .finitely_freely_generated_noa import FinitelyFreelyGeneratedNOA
from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
from sage.structure.indexed_generators import (IndexedGenerators,
                                               standardize_names_index_set)
from sage.rings.integer import Integer


class VertexAlgebraWithOPE(FinitelyFreelyGeneratedNOA):
    r"""
    A vertex algebra with a set of specified OPEs.

    INPUT:

    - ``R`` -- a ring (Default: ``None``); The base ring of this Lie
      conformal algebra. Behavior is undefined if it is not a field
      of characteristic zero.

    - ``s_coeff`` -- Dictionary (Default: ``None``);
      a dictionary containing the specified OPEs of the
      generators of this vertex algebra. The family encodes a
      dictionary whose keys
      are pairs of either names or indices of the generators
      and the values are themselves dictionaries. For a pair of
      generators `a` and `b`, the value of ``s_coeff[('a','b')]`` is
      a dictionary whose keys integers and the
      corresponding value for the key `j` is a dictionary itself
      representing the j-th product `a_{(j)}b`.
      If the singular ope coefficients are generators of the vertex 
      algebra and not normally ordered products of generators, for a 
      positive integer number `j`, the value of
      ``s_coeff[('a','b')][j]`` is a dictionary whose entries are
      pairs ``('c',n)`` where ``'c'`` is the name of a generator
      and `n` is a positive number. The value for this key is the
      coefficient of `\frac{T^{n}}{n!} c` in `a_{(j)}b`. For example
      the ``s_coeff`` for the *Virasoro* algebra is::

            {('L','L'):{0:{('L',1):1}, 1:{('L',0):2}, 3:{('C',0):1/2}}}


      If the key ``('a','b')`` is present, there is no need to include
      ``('b','a')`` as it is defined by skew-symmetry.

      If an OPE coefficient (especially for negative index) is itself a normally ordered product, the normal ordering on the OPE coefficient is represented as a tuple. For example, the Lattice VOA associated to `\ZZ` spanned by v with the `(0)` pairing has an OPE specified by 

            {('Γ_m', 'Γ_n') : {-1 : {('Γ_{m+n}',0):1}}}

      Do not include central elements in this dictionary. Also, if
      the key ``('a','b')`` is present, there is no need to include
      ``('b','a')`` as it is defined by skew-symmetry. 
      
      The OPE with the string '1' specifies relations between derivatives 
      of a generator and other generators in the vertex algebra, because of Taylor's theorem.   

      If the second part of a key it itself a tuple ('A', k) we specify that a normal ordered product of derivatives is the correpsonding item. E.g. 

        {('A', ('B', 3)): {-1 : {('D',0): 8 }}}

      corresponds to :A\partial^{(3)}B: = 8D. Only the -1 index of the structure constants are read for these inputs. 

    - ``names`` -- tuple of ``str`` (Default: ``None``); The list of
      names for generators of this vertex algebra. Do not
      include central elements in this list.

    - ``central_elements`` -- tuple of ``str`` (Default: ``None``);
      A list of names for central
      elements of this vertex algebra.

    - ``index_set`` -- enumerated set (Default: ``None``);
      an indexing set for the generators of this Lie
      conformal algebra. Do not include central elements in this
      list.

    - ``parity`` -- tuple of `0` or `1` (Default: tuple of `0`);
       a tuple specifying the parity of each non-central generator.

    EXAMPLES:

    - We construct a free boson system by directly giving the
      OPE of the generators::

            sage: freeboson_dict = {('α','α'):{1:{('C',0):1}}}
            sage: V = VertexAlgebra(QQ, freeboson_dict, names=('α'), central_elements=('C',))
            sage: V.inject_variables()
            Defining α
            sage: T = 1/2 * α.no_product(α); T
            1/2*:αα:
            sage: T.OPE(T,cc = (1,))
            (1/2*:Tαα:(w) + 1/2*:αTα:(w))/(z-w) + :αα:(w)/(z-w)^2 + 1/2/(z-w)^4
    """

    def __init__(self, R, s_coeff, central_elements=None,
                 category=None, element_class=None, prefix=None, names=None,
                 latex_names=None, parity=None, **kwds):
        """
        Initialize self.

        TESTS::

            sage: V = lie_conformal_algebras.NeveuSchwarz(QQ)
            sage: TestSuite(V).run()
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

        issuper = kwds.pop('super', False)
        if parity is None:
            parity = (0,) * index_set.cardinality()
        else:
            issuper = True

        try:
            assert len(parity) == index_set.cardinality()
        except AssertionError:
            raise ValueError("parity should have the same length as the "
                             f"number of generators, got {parity}")

        if names is not None and central_elements is not None:
            all_names = names +  tuple(central_elements)
        else:
            all_names = names

        self._index_to_pos = {k: i for i, k in enumerate(index_set)}
        # Add central parameters to index_to_pos so that we can
        # represent names
        if central_elements is not None:
            for i, ce in enumerate(central_elements):
                self._index_to_pos[ce] = len(index_set) + i

        # default_category = VertexAlgebras(R).WithBasis().FinitelyGenerated()
        # if issuper:
        #     category = default_category.Super().or_subcategory(category)
        # else:
        #     category = default_category.or_subcategory(category)

        if element_class is None:
            element_class = VAWithOPECoefficientsElement

        FinitelyFreelyGeneratedNOA.__init__(
            self, R, central_elements=central_elements,
            category=category, element_class=element_class,
            prefix=prefix, names=names, latex_names=latex_names, **kwds)

        s_coeff = dict(s_coeff)
        # self._s_coeff = Family({k: tuple((j, sum(c*self.monomial(i)
                # for i,c in v )) for j,v in s_coeff[k]) for k in s_coeff})
        self._s_coeff = s_coeff
        self._parity = dict(zip(self.gens(),parity+(0,)*len(central_elements)))
        self._index_parity = dict(zip (all_names,parity+(0,)*len(central_elements) )  )


    def structure_coefficients(self):
        """
        The structure coefficients of this vertex algebra.

        EXAMPLES::

            sage: Vir = lie_conformal_algebras.Virasoro(AA)
            sage: Vir.structure_coefficients()
            Finite family {('L', 'L'): ((0, TL), (1, 2*L), (3, 1/2*C))}

            sage: lie_conformal_algebras.NeveuSchwarz(QQ).structure_coefficients()
            Finite family {('G', 'G'): ((0, 2*L), (2, 2/3*C)),  ('G', 'L'): ((0, 1/2*TG), (1, 3/2*G)),  ('L', 'G'): ((0, TG), (1, 3/2*G)),  ('L', 'L'): ((0, TL), (1, 2*L), (3, 1/2*C))}
        """
        return self._s_coeff

    def _repr_generator(self, x):
        """
        String representation of the generator ``x``.

        INPUT:

        - ``x`` -- an index parametrizing a generator or a generator of
          this vertex algebra

        EXAMPLES::

            sage: Vir = lie_conformal_algebras.Virasoro(QQbar)
            sage: Vir._repr_generator(Vir.0)
            'L'
            sage: R = lie_conformal_algebras.Affine(QQ, 'A1')
            sage: R._repr_generator(R.0)
            'B[alpha[1]]'
            sage: R = lie_conformal_algebras.Affine(QQ, 'A1', names=('e','h','f'))
            sage: R._repr_generator(R.0)
            'e'
        """
        if x in self:
            return repr(x)
        return IndexedGenerators._repr_generator(self,x)

    def one(self):
        r"""
        Returns the identity field in self. 

        EXAMPLES::

            sage: betagamma_dict = {('β','γ'):{0:{('K',0):1}}, ('β', 'β'): {},('γ', 'γ'): {} }
            sage: V = VertexAlgebra(QQ, betagamma_dict, names=('β','γ'), central_elements=('K',))
            sage: V.one()
            1
        """
        return self.monomial(self._NOPS.one())

    def from_dict(self, d):
        r"""
        Returns an element of the vertex algebra from an OPE dictionary

        EXAMPLE :: 
        
            sage: V.from_dict({(('a',0), (Γ_m, 0))  : m})
            m:aΓ_m:
        """
        out =  sum( d[k]*self.monomial(self._NOPS.from_tuple(k)) for k in d.keys() )
        return self.zero() if isinstance(out, int) else out

    def monomial_parity(self, m):
        r"""
        Returns the parity of m. 

        INPUT:
        
        -- ``m`` - monomial index. m is a NormallyOrderedProduct in the generators of the VOA

        OUTPUT: the parity of m as 1 or 0

        EXAMPLES::

            sage:
        """
        if not m.is_NO():
            return self._index_parity[m.value[0][0]]
        else: 
            return (self.monomial_parity(m.value[0]) + self.monomial_parity(m.value[1])) % 2

    # def _n_product_on_indices(self, x, y, n):
    #     r"""
    #     Returns the n-th product on indices of generators

    #     INPUT:

    #     - ``x`` -- an index parametrizing a generator or a generator of
    #       this Vertex algebra, given by a tuple of the form ('A', n) where 'A' is a label of a generating field and 
    #     """