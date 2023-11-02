r"""
Vertex Algebra

AUTHORS:

- Samuel DeHority (2019-10-??): Initial implementation.
"""


#******************************************************************************
#       Copyright (C) 2023 Samuel DeHority <spd2133@columbia.edu>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.structure.unique_representation import UniqueRepresentation
from sage.sets.family import Family
from sage.categories.commutative_rings import CommutativeRings
from sage.structure.parent import Parent

from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
from sage.structure.indexed_generators import (IndexedGenerators,
                                               standardize_names_index_set)

class VertexAlgebra(UniqueRepresentation, Parent):
    r"""
    Vertex Algebras base class and factory.

    INPUT:

    - ``R`` -- a commutative ring (default: ``None``); the base
      ring of this Vertex algebra. Behaviour is undefined
      if it is not a field of characteristic zero.

    - ``arg0`` -- a dictionary (default: ``None``);
      a dictionary containing the `\lambda` brackets of the
      generators of this vertex algebra. The keys of this
      dictionary are pairs of either names or indices of the
      generators and the values are themselves dictionaries. For a
      pair of generators ``'a'`` and ``'b'``, the value of
      ``arg0[('a','b')]`` is a dictionary whose keys are positive
      integer numbers and the corresponding value for the
      key ``j`` is a dictionary itself representing the j-th product
      `a_{(j)}b`. Thus, for a positive integer number `j`, the
      value of ``arg0[('a','b')][j]`` is a dictionary whose entries
      are pairs ``('c',n)`` where ``'c'`` is the name of a generator
      and ``n`` is a positive number. The value for this key is the
      coefficient of `\frac{T^{n}}{n!} c` in `a_{(j)}b`. For
      example the ``arg0`` for the *Virasoro* algebra
      is::

            {('L','L'):{0:{('L',1):1}, 1:{('L',0):2}, 3:{('C',0):1/2}}}


      Do not include central elements as keys in this dictionary. Also,
      if the key ``('a','b')`` is present, there is no need to include
      ``('b','a')`` as it is defined by skew-symmetry. 

    - ``names`` -- tuple of ``str`` (default: ``None``); the list of
      names for generators of this vertex algebra. Do not
      include central elements in this list.

    - ``central_elements`` -- tuple of ``str`` (default: ``None``);
      A list of names for central elements of this vertex
      algebra.

    - ``index_set`` -- enumerated set (default: ``None``); an
      indexing set for the generators of this vertex algebra.
      Do not include central elements in this list.

    - ``parity`` -- tuple of `0` or `1` (default: tuple of `0`);
      if this is a super vertex algebra, this tuple
      specifies the parity of each of the non-central generators of
      this vertex algebra. Central elements are assumed to
      be even. Notice that if this tuple is present, the category
      of this vertex algebra is set to be a subcategory of
      ``LieConformalAlgebras(R).Super()``, even if all generators
      are even.

    - ``category`` The category that this vertex algebra
      belongs to.


    """
    @staticmethod
    def __classcall_private__(cls, R=None, arg0=None, index_set=None,
        central_elements=None, category=None, prefix=None,
        names=None, latex_names=None, parity=None, weights=None, **kwds):
        """
        Vertex algebra factory.

        EXAMPLES::

            sage: bc_dict = {('b','c'):{0:{('K',0):1}}, ('b','b'): {}, ('c','c'): {}}
            sage: V_bc = VertexAlgebra(QQ, bc_dict, names=('b,c'), central_elements=('K',),parity = (1,1))
            sage: V_bc.inject_variables()
            sage: ω = c.T().no_product(b); ω
            sage: ω.OPE(ω, cc=(1,))
            -1/(z-w)^4 + 2*:Tcb:(w)/(z-w)^2 + (2*:T^(2)cb:(w) + :TcTb:(w))/(z-w)
        """
        if R not in CommutativeRings():
            raise ValueError(f"arg0 must be a commutative ring got {R}")

        # This is the only exposed class so we clean keywords here
        known_keywords = ['category', 'prefix', 'bracket', 'latex_bracket',
                          'string_quotes', 'sorting_key', 'graded', 'super']
        for key in kwds:
            if key not in known_keywords:
                raise ValueError("got an unexpected keyword argument '%s'" % key)

        if isinstance(arg0,dict) and arg0:
            graded = kwds.pop("graded", False)
            if weights is not None or graded:
                from .graded_vertex_algebra import \
                                                    GradedVertexAlgebra
                return GradedVertexAlgebra(R, Family(arg0),
                    central_elements=central_elements,
                    category=category, prefix=prefix, names=names,
                    latex_names=latex_names, parity=parity, weights=weights,
                    **kwds)
            else:
                from .vertex_algebra_with_OPE import \
                        VertexAlgebraWithOPE
                return VertexAlgebraWithOPE(R,
                       Family(arg0), 
                       central_elements=central_elements, category=category,
                       prefix=prefix, names=names, latex_names=latex_names,
                       parity=parity, **kwds)
        raise NotImplementedError("not implemented")
