# Documentation for the Idris Language.


This manual has been prepared using ReStructured Text and the [Sphinx Documentation Generator](http://sphinx-doc.org) for future inclusion on [Read The Docs](http://www.readthedocs.org).

## Dependencies

To build the manual the following dependencies must be met. We assume that you have standard build automation tools already install i.e. `make`.

### Sphinx-Doc

Python should be installed by default on most systems.
Sphinx can be installed either through your hosts package manager or using pip/easy_install.

*Note* [ReadTheDocs](http://www.readthedocs.org) works with Sphinx
 `v1.2.2`. If you install a more recent version of sphinx then
 'incorrectly' marked up documentation may get passed the build system
 of readthedocs and be ignored. In the past we had several code-blocks
 disappear because of that.

The ReadTheDocs theme can be installed using pip as follows:

```sh
pip install sphinx_rtd_theme
```

### LaTeX

LaTeX can be install either using your systems package manager or direct from TeXLive.


## Build Instructions

```sh
make html
make latexpdf
```

## Contributing

The documentation for Idris has been published under the Creative
Commons CC0 License. As such to the extent possible under law, /The
Idris Community/ has waived all copyright and related or neighboring
rights to Documentation for Idris.

More information concerning the CC0 can be found online at:

    http://creativecommons.org/publicdomain/zero/1.0/


When contributing material to the manual please bear in mind that the work will be licensed as above.
