"""
Normal Ordering Algebras With Basis

AUTHORS:

- Samuel DeHority (2023-10-??): Initial implementation


Derived from the Lie conformal algebras module of SageMath 9.5 originally contirbuted by Reimundo Heluani.
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

# from sage.categories.lie_conformal_algebras import LieConformalAlgebras
from sage.combinat.free_module import CombinatorialFreeModule

class NormalOrderingAlgebraWithBasis(CombinatorialFreeModule):
    """
    Abstract base class for a Lie conformal algebra with a
    preferred basis.

    This class provides no functionality, it simply passes the
    arguments to :class:`CombinatorialFreeModule`.

    """
    def __init__(self, R, basis_keys=None, element_class=None, category=None,
                 prefix=None, **kwds):
        """
        Initialize self.

        """
        if prefix is None:
            prefix = ''
            kwds['bracket'] = ''
            kwds['string_quotes'] = False

        # default_category = VertexAlgebras(R).WithBasis()
        # try:
        #     category = default_category.or_subcategory(category)
        # except ValueError:
        #     category = default_category.Super().or_subcategory(category)

        super().__init__(R, basis_keys=basis_keys, element_class=element_class,
                        #  category=category, 
                         prefix=prefix, names=None, **kwds)
