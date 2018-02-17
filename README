This is CLWEB, a literate programming system for Common Lisp. This file
describes how to get started with CLWEB; it is not a user manual or an
introduction to literate programming in general. A full user manual is
forthcoming; in the meantime, please see the CWEB user manual by Knuth
and Levy, or Knuth's "Literate Programming" (CSLI: 1992).

In the examples that follow, a dollar sign ($) represents a Unix shell
prompt, and a star (*) represents a Lisp prompt.

The first thing to do is to compile and load the CLWEB system:

    $ lisp
    * (compile-file "clweb")
    ; compiling file "/home/alex/src/clweb/clweb.lisp"
    ; [compilation messages elided]
    #P"/home/alex/src/clweb/clweb.fasl"
    NIL
    NIL
    * (load "clweb")
    T
    * (use-package "CLWEB")
    T

Now suppose you wanted to weave the CLWEB program itself. You might say:

    * (weave "clweb")
    ; weaving WEB from #P"clweb.clw"
    ; 0
    ; *1 2 3
    ; *4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22
    ; *23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41
    ;  42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60
    ;  61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79
    ;  80 81 82 83 84 85 86 87 88
    ; *89 90 91 92 93 94
    ; *95 96 97 98 99 100 101 102 103 104 105 106 107 108 109
    ;  110 111 112 113 114 115 116 117 118 119 120 121 122 123
    ;  124 125 
    #P"/home/alex/src/clweb/clweb.tex"
    * ^Z
    $ tex clweb
    This is TeX, Version 3.141592 (Web2C 7.5.4)
    (./clweb.tex (./clwebmac.tex
    (/usr/pkg/share/texmf-dist/tex/plain/base/cwebmac.tex)) *1 [1] *4 [2] [3]
    [4] [5] [6] [7] *23 [8] [9] [10] [11] [12] [13] [14] [15] [16] [17] [18]
    [19] [20] [21] [22] [23] [24] [25] [26] [27] [28] [29] *89 [30] [31] [32]
    *95 [33] [34] [35] [36] [37] [38] [39] [40] [41] [42] )
    Output written on clweb.dvi (42 pages, 137808 bytes).
    Transcript written on clweb.log.
    $

The numbers that WEAVE prints are the section numbers the weaver sees; the
ones preceded by stars are the `starred', or major, sections. TeX also
prints the starred section numbers along with the page numbers in square
brackets.

To use CLWEB for your own projects, you need to have the file `clwebmac.tex'
somewhere in TeX's search path. One way to do this (on the author's system,
anyway) is to install a copy of or a symlink to the version included in the
distribution in a directory like `~/texmf/tex/plain'; see the documentation
for your TeX distribution for more information, esp. the Kpathsea library.

The CLWEB tangler can be used in two different ways: to produce a compiled
file that can be used with LOAD, or to load the contents of a CLWEB file
directly into a running Lisp image. In the first case, you would use
TANGLE-FILE:

    * (compile-file "clweb")
    ; tangling WEB from #P"clweb.clw"
    ; compiling file "/home/alex/src/clweb/clweb.lisp":
    ; [compilation messages elided]
    #P"/home/alex/src/clweb/clweb.fasl"
    NIL
    NIL
    *

You should now have a fresh copy of `clweb.lisp' and `clweb.fasl'. You
shouldn't ever edit the former directly; it's only an intermediate file.

During development, the other mode of tangling is often more useful:

    * (load-web "clweb")
    T
    * 

The tangled contents of `clweb.clw' have now been loaded directly into the
Lisp environment.

Currently, CLWEB runs under SBCL, Allegro Common Lisp, and Clozure Common
Lisp. Reports of the experience of attempting to run the system under other
Common Lisp implementations would be welcome, along with any other
questions, bug-reports, patches, comments, or suggestions; please email
them to Alex Plotnick <plotnick@cs.brandeis.edu>.

The author gratefully acknowledges the encouragement and support of Ross
Shaull, who made him believe that at least one other person in the world
thought this might be a good idea, and of Richard Kreuter, for his many
suggestions for improving both the commentary and code of the system, as
well as for his work on SBCL.
