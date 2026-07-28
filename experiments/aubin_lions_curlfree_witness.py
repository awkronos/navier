"""STEP 0 -- reproduce the curl-free falsification witness for
aubin_lions_l2loc_compactness AS STATED, and check that Riesz-Kolmogorov
spatial-translation equicontinuity (H-space) EXCLUDES it.

Witness family (commit 01b6561):  u_m = grad( m^{-1} cos(m x_0) chi ),  chi = exp(-|x|^2).
Curl-free by Clairaut => enstrophy identically 0 => UniformEnstrophyBound C = 0.
Time-independent   => TimeEquicontinuous trivially.
L^2-bounded        => UniformKineticBound.
"""
import numpy as np

# 1-D profile (the x_0 direction carries all the oscillation; chi = exp(-x^2)).
L, N = 12.0, 2_000_001
x = np.linspace(-L, L, N); dx = x[1] - x[0]
chi  = np.exp(-x**2)
dchi = -2.0*x*np.exp(-x**2)

def u(m):                       # d/dx [ m^-1 cos(m x) chi ]
    return -np.sin(m*x)*chi + np.cos(m*x)*dchi/m

def l2sq(f): return np.trapezoid(f*f, dx=dx)

print("== (1) L2-bounded, and NOT L2loc-Cauchy ==")
print("  limit of ||u_m||^2 = (1/2)*int chi^2 =", 0.5*np.sqrt(np.pi/2))
for m in (4, 8, 16, 32, 64, 128):
    um, u2m = u(m), u(2*m)
    print(f"  m={m:4d}   ||u_m||^2 = {l2sq(um):.4f}   ||u_m - u_2m||^2 = {l2sq(um-u2m):.4f}")

print("\n== (2) curl-free: enstrophy EXACTLY 0 (Clairaut), checked in 3-D ==")
h = 1e-4
def psi(m, X):  return np.cos(m*X[0])/m*np.exp(-(X[0]**2+X[1]**2+X[2]**2))
def grad(m, X):
    g = []
    for i in range(3):
        Xp = [c.copy() for c in X]; Xm = [c.copy() for c in X]
        Xp[i] = Xp[i]+h; Xm[i] = Xm[i]-h
        g.append((psi(m,Xp)-psi(m,Xm))/(2*h))
    return g
rng = np.random.default_rng(0); worst = 0.0
for _ in range(200):
    P = [np.array([float(v)]) for v in rng.uniform(-2, 2, size=3)]
    for i,(a,b) in enumerate(((1,2),(2,0),(0,1))):          # curl component i
        Pp=[c.copy() for c in P]; Pm=[c.copy() for c in P]; Pp[a]+=h; Pm[a]-=h
        d1=(grad(8,Pp)[b]-grad(8,Pm)[b])/(2*h)
        Pp=[c.copy() for c in P]; Pm=[c.copy() for c in P]; Pp[b]+=h; Pm[b]-=h
        d2=(grad(8,Pp)[a]-grad(8,Pm)[a])/(2*h)
        worst = max(worst, float(abs(d1-d2)[0]))
print(f"  sup |curl(grad psi)| over 200 random points, m=8 : {worst:.3e}   (0 up to FD error)")

print("\n== (3) (H-space) Riesz-Kolmogorov spatial equicontinuity FAILS on the witness ==")
print("   sup_m  int |u_m(.+s) - u_m|^2   must -> 0 as s -> 0 for (H-space) to hold.")
for m in (8, 16, 32, 64, 128, 256):
    s = np.pi/m                              # shift -> 0, but phase flips by pi
    k = int(round(s/dx)); us = np.roll(u(m), -k)
    lo, hi = 2*k+10, N-2*k-10
    err = np.trapezoid((us-u(m))[lo:hi]**2, dx=dx)
    print(f"  m={m:4d}  |s|={s:.5f}   int|u_m(.+s)-u_m|^2 = {err:.4f}")
print("   -> shift size -> 0 while the error stays ~2*int chi^2 = %.3f : (H-space) is VIOLATED."
      % (2*np.sqrt(np.pi/2)))

print("\n== (4) control: a genuinely (H-space)-equicontinuous family is fine ==")
v = lambda m: np.exp(-x**2)*(1.0+1.0/(m+1))     # no oscillation
for m in (8, 64, 256):
    s = np.pi/m; k = int(round(s/dx)); vs = np.roll(v(m), -k)
    lo, hi = 2*k+10, N-2*k-10
    print(f"  m={m:4d}  |s|={s:.5f}   int|v_m(.+s)-v_m|^2 = {np.trapezoid((vs-v(m))[lo:hi]**2, dx=dx):.3e}")
