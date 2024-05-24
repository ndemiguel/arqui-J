readfile =: 1!:1
writefile =: 1!:2
closefile =: 1!:22
openfile =: 1!:21
openfiles =: 1!:20
appendfile =: 1!:3
debug=: 13!:0
setstop=: 13!:3               NB.'f 0' 	f monadic line 0
stepover=: 13!:20
stepinto=: 13!:20
stepout=: 13!:20
reset =: 13!:0
displaystack =: 13!:1
querystops =: 13!:2  
continue =: 13!:7

   cop=:       0&o.   NB. sqrt (1-(y^2))
   sin=:       1&o.   NB. sine of y
   cos=:       2&o.   NB. cosine of y
   tan=:       3&o.   NB. tangent of y
   coh=:       4&o.   NB. sqrt (1+(y^2))
   sinh=:      5&o.   NB. hyperbolic sine of y
   cosh=:      6&o.   NB. hyperbolic cosine of y
   tanh=:      7&o.   NB. hyperbolic tangent of y
   conh=:      8&o.   NB. sqrt -(1+(y^2))
   real=:      9&o.   NB. Real part of y
   magn=:     10&o.   NB. Magnitude of y
   imag=:     11&o.   NB. Imaginary part of y
   angle=:    12&o.   NB. Angle of y

   arcsin=:   _1&o.   NB. inverse sine
   arccos=:   _2&o.   NB. inverse cosine
   arctan=:   _3&o.   NB. inverse tangent
   cohn=:     _4&o.   NB. sqrt (_1+(y^2))
   arcsinh=:  _5&o.   NB. inverse hyperbolic sine
   arccosh=:  _6&o.   NB. inverse hyperbolic cosine
   arctanh=:  _7&o.   NB. inverse hyperbolic tangent
   nconh=:    _8&o.   NB. -sqrt -(1+(y^2))
   same=:     _9&o.   NB. y
   conj=:    _10&o.   NB. complex conjugate of y
   jdot=:    _11&o.   NB. j. y
   expj=:    _12&o.   NB. ^ j. y
   log=:	    ^.      NB. logritmo_n=x

mp=: +/ . *

delay =: 6!:3

load 'plot'
load '/home/agrosso/j64-807/addons/format/printf/printf.ijs'

print=: monad define
   (": y) (1!:2) 2
   (13{a.) (1!:2) 2
)

