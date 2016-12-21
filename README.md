[![Build Status][build_img]][travis]

About
=====

2LS is a verification tool for C programs. It is built upon the
CPROVER framework ([cprover.org](http://www.cprover.org)), which
supports C89, C99, most of C11 and most compiler extensions provided
by gcc and Visual Studio. It allows verifying array bounds (buffer
overflows), pointer safety, exceptions, user-specified assertions, and
termination properties.  The analysis is performed by template-based
predicate synthesis and abstraction refinements techniques.

For more information see [cprover.org](http://www.cprover.org/2LS).

License
=======
4-clause BSD license, see `LICENSE` file.

[build_img]: https://travis-ci.org/diffblue/2ls.svg?branch=master
[travis]: https://travis-ci.org/diffblue/2ls
