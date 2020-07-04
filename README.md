# kunzpolyhedron
Written by Christopher O'Neill, Christopher Preuss, and Eduardo Torres Davila.  

Provides functions for working with the [Kunz posets](https://arxiv.org/abs/1912.03741), which index faces of the Kunz polyhedron, in the computer algebra system [Sage](http://sagemath.org/).  Internally, some functionality uses the [GAP](http://www.gap-system.org/) package [numericalsgps](http://www.gap-system.org/Packages/numericalsgps.html) via the [NumericalSemigroup](https://github.com/coneill-math/numsgps-sage) class.  

Please note that this is an *alpha version* and subject to change without notice.  

## License
numsgpsalg is released under the terms of the [MIT license](https://tldrlegal.com/license/mit-license).  The MIT License is simple and easy to understand and it places almost no restrictions on what you can do with this software.

## Usage
To use all features of this class, you must first install [numsgps-sage](https://github.com/coneill-math/numsgps-sage).  Next, simply place `KunzPosets.sage` in the same directory as `NumericalSemigroup.sage`.  

The following code fragment gives an overview of how to use some of the basic functions, and more complete documentation will be added in the near future.

	load('/PATH_TO_FILES/NumericalSemigroup.sage')
	load('/PATH_TO_FILES/KunzPosets.sage')
	PlotKunzPoset([6,9,20])
	PlotKunzPoset([5,6,9])

