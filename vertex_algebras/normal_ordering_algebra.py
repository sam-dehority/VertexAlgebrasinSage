r"""
Normal Ordering Algebra
AUTHORS:

- Samuel DeHority (2023-10-??): Initial implementation.


Derived from the Lie conformal algebras module of SageMath 9.5 originally contirbuted by Reimundo Heluani.

"""

#******************************************************************************
#       Copyright (C) 2023 Samuel DeHority
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

class NormalOrderingAlgebra(UniqueRepresentation, Parent):
    r"""
    Normal Ordering Algebras base class and factory.

    INPUT:

    - ``R`` -- a commutative ring (default: ``None``); the base
      ring of this vertex algebra. Behaviour is undefined
      if it is not a field of characteristic zero.

    - ``names`` -- tuple of ``str`` (default: ``None``); the list of
      names for generators of this vertex algebra. Do not
      include central elements in this list.

    - ``central_elements`` -- tuple of ``str`` (default: ``None``);
      A list of names for central elements of this vertex
      algebra.

    - ``index_set`` -- enumerated set (default: ``None``); an
      indexing set for the generators of this vertex algebra.
      Do not include central elements in this list.

    - ``weights`` -- tuple of non-negative rational numbers
      (default: ``None``); a list of degrees for this Lie
      conformal algebra.
      The returned vertex algebra is H-Graded. This tuple
      needs to have the same cardinality as ``index_set`` or
      ``names``. Central elements are assumed to have weight `0`.

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

    In addition we accept the following keywords:

    - ``graded`` -- a boolean (default: ``False``);
      if ``True``, the returned algebra is H-Graded.
      If ``weights`` is not specified, all non-central generators
      are assigned degree `1`. This keyword is ignored if
      ``weights`` is specified

    - ``super`` -- a boolean (default: ``False``);
      if ``True``, the returned algebra is a super
      vertex algebra even if all generators are even.
      If ``parity`` is not specified, all generators are
      assigned even parity. This keyword is ignored if
      ``parity`` is specified.

    .. Note::

        Any remaining keyword is currently passed to
        :class:`CombinatorialFreeModule<sage.combinat.free_module.CombinatorialFreeModule>`.

    """
    @staticmethod
    def __classcall_private__(cls, R=None, arg0=None, index_set=None,
        central_elements=None, category=None, prefix=None,
        names=None, latex_names=None, parity=None, weights=None, **kwds):
        """
        Normal ordering algebra factory.
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
                from .graded_normal_ordering_algebra import \
                                                    GradedNormalOrderingAlgebra
                return GradedNormalOrderingAlgebra(R, 
                    index_set=index_set, central_elements=central_elements,
                    category=category, prefix=prefix, names=names,
                    latex_names=latex_names, parity=parity, weights=weights,
                    **kwds)
            else:
                from .finitely_freely_generated_noa import \
                        FinitelyFreelyGeneratedNOA
                return FinitelyFreelyGeneratedNOA(R,
                     index_set=index_set,
                       central_elements=central_elements, category=category,
                       prefix=prefix, names=names, latex_names=latex_names,
                       parity=parity, **kwds)
        raise NotImplementedError("not implemented")
