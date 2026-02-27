# SU(2) utilities: Haar sampler, multiplication, trace
import math, random
from dataclasses import dataclass

@dataclass(frozen=True)
class SU2:
    a: float; b: float; c: float; d: float

    def as_tuple(self):
        return (self.a, self.b, self.c, self.d)

def _norm4(x):
    return math.sqrt(sum(t*t for t in x))

def haar_su2(rng):
    x=[rng.gauss(0,1) for _ in range(4)]
    n=_norm4(x)
    return SU2(*(t/n for t in x))

def mul(g,h):
    a,b,c,d=g.as_tuple(); e,f,g2,h2=h.as_tuple()
    return SU2(
      a*e - b*f - c*g2 - d*h2,
      a*f + b*e + c*h2 - d*g2,
      a*g2 - b*h2 + c*e + d*f,
      a*h2 + b*g2 - c*f + d*e)

def trace(u):
    return 2.0*u.a
