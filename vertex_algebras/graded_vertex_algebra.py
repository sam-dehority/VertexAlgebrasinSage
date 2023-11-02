r"""
Graded Vertex Algebras


AUTHORS:

- Samuel DeHority (2023-????): Initial implementation.

Derived from the Lie conformal algebras module of SageMath 9.5 originally contirbuted by Reimundo Heluani.
"""


#******************************************************************************
#       Copyright (C) 2023
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************


from sage.categories.lie_conformal_algebras import LieConformalAlgebras
from .lie_conformal_algebra_with_structure_coefs import \
                                LieConformalAlgebraWithStructureCoefficients

class GradedVertexAlgebra(VertexAlgebraWithStructureCoefficients):
    r"""
    """
    def __init__(self, R, s_coeff, index_set=None, central_elements=None,
                 category=None, prefix=None, names=None, latex_names=None,
                 parity=None, weights=None, **kwds):
        """
        Initialize self.

        TESTS::

            sage: V = lie_conformal_algebras.Virasoro(QQ)
            sage: TestSuite(V).run()
        """
        is_super = kwds.get('super', None)
        default_category = VertexAlgebras(R).WithBasis().FinitelyGenerated().Graded()
        if is_super or parity:
            category = default_category.Super().or_subcategory(category)
        else:
            category = default_category.or_subcategory(category)

        VertexAlgebraWithStructureCoefficients.__init__(self, R,
            s_coeff, index_set=index_set, central_elements=central_elements,
            category=category, prefix=prefix,
            names=names, latex_names=latex_names, parity=parity, **kwds)

        if weights is None:
            weights = (1,) * (len(self._generators) -
                              len(self.central_elements()))
        if len(weights) != (len(self._generators) -
                            len(self.central_elements())):
            raise ValueError("weights and (non-central) generator lists "
                             "must be of same length")
        self._weights = weights
