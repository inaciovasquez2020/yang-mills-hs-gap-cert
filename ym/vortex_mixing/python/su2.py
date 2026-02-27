import math
import random
from dataclasses import dataclass
from typing import Tuple

@dataclass(frozen=True)
class SU2:
    a: float
    b: float
    c: float
    d: float

    def as_tuple(self) -> Tuple[float,float,float,float]:
        return (self.a, self.b, self.c, self.d)

def _norm4(x):
    return math.sqrt(sum(t*t for t in x))

def haar_su2(rng: random.Random) -> SU2:
    x = [rng.gauss(0.0, 1.0) for _ in range(4)]
    n = _norm4(x)
    a,b,c,d = (t/n for t in x)
    return SU2(a,b,c,d)

def mul(g: SU2, h: SU2) -> SU2:
    a,b,c,d = g.as_tuple()
    e,f,g2,h2 = h.as_tuple()
    return SU2(
        a*e - b*f - c*g2 - d*h2,
        a*f + b*e + c*h2 - d*g2,
        a*g2 - b*h2 + c*e + d*f,
        a*h2 + b*g2 - c*f + d*e
    )

def conj(u: SU2) -> SU2:
    return SU2(u.a, -u.b, -u.c, -u.d)

def inv(u: SU2) -> SU2:
    return conj(u)

def trace(u: SU2) -> float:
    return 2.0*u.a

def rotate_by_angle(axis, theta: float) -> SU2:
    ax, ay, az = axis
    n = math.sqrt(ax*ax + ay*ay + az*az)
    ax, ay, az = ax/n, ay/n, az/n
    s = math.sin(theta/2.0)
    return SU2(math.cos(theta/2.0), ax*s, ay*s, az*s)

def random_axis(rng: random.Random):
    x = [rng.gauss(0.0,1.0) for _ in range(3)]
    n = math.sqrt(sum(t*t for t in x))
    return (x[0]/n, x[1]/n, x[2]/n)
