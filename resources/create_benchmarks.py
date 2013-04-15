#!/usr/bin/env python

import sys

def fopen(dirname, suffix):
  filename = "bench_%s/vpda_%s" % (dirname, suffix)
  return open(filename, 'w')

def write_header(f):
  f.write("mprs vpda [\n")

def write_footer(f):
  f.write("]\n")
  f.close()

def wide_flat(n, r):
  f = fopen("wide_flat", "%i_%i" % (r, n))
  write_header(f)
  f.write("p0.s0 <= q0.s0\n")
  f.write("p0.s0 c? p1.s0.s0\n")
  for i in range(n):
    f.write("q0.s0 c? q1.s0.s%i\n" % (i))
  f.write("p1.s0 r? p2\n")
  f.write("q1.s0 r? q2\n")
  f.write("p2.s0 c? p3.s0.s0\n")
  for i in range(n):
    f.write("q2.s%i c? q3.s0.s%i\n" % (i, i))
  f.write("p3.s0 i? p4.s0\n")
  for i in range(n + 1):
    f.write("q3.s0 i? q4.s%i\n" % (i))
  if r == 0:
    f.write("p4.s0 r? p5\n")
  write_footer(f)

def wide_deep(n, r):
  f = fopen("wide_deep", "%i_%i" % (r, n))
  write_header(f)
  f.write("p1r0.s0 <= q1r0.s0\n")
  for i in range(n):
    f.write("p1r%i.s0 c? p1r%i.s0.s0\n" % (i, i + 1))
  for i in range(n):
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i))
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i + 1))
  f.write("p1r%i.s0 i? p2r%i.s0\n" % (n, n))
  for i in range(n):
    f.write("q1r%i.s0 i? q2r%i.s0\n" % (i, i))
  for i in range(n):
    f.write("p2r%i.s0 r? p2r%i\n" % (i + 1, i))
  for i in range(n):
    f.write("q2r%i.s0 r? q2r%i\n" % (i, i))
  if r == 0:
    f.write("p2r0.s0 i? p3r0.s0\n")
  write_footer(f)

def const_deep(n, k, r):
  f = fopen("const_deep", "%i_%i_%i" % (r, k, n))
  write_header(f)
  f.write("p1r0.s0 <= q1r0.s0\n")
  for i in range(n):
    f.write("p1r%i.s0 c? p1r%i.s0.s0\n" % (i, i + 1))
  for i in range(k):
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i))
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i + 1))
  f.write("p1r%i.s0 i? p2r%i.s0\n" % (n, n))
  for i in range(k):
    f.write("q1r%i.s0 i? q2r%i.s0\n" % (i, i))
  for i in range(n):
    f.write("p2r%i.s0 r? p2r%i\n" % (i + 1, i))
  for i in range(k):
    f.write("q2r%i.s0 r? q2r%i\n" % (i, i))
  if r == 0:
    f.write("p2r0.s1 i? p3r0.s0\n")
  write_footer(f)

def const_branch(n, k, r):
  f = fopen("const_branch", "%i_%i_%i" % (r, k, n))
  write_header(f)
  f.write("p1r0.s0 <= q1r0.s0\n")
  for i in range(n):
    f.write("p1r%i.s0 c? p1r%i.s0.s0\n" % (i, i))
    f.write("p1r%i.s0 c? p1r%i.s0.s0\n" % (i, i + 1))
  for i in range(k):
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i))
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i + 1))
  f.write("p1r%i.s0 i? p2r%i.s0\n" % (n, n))
  for i in range(k):
    f.write("q1r%i.s0 i? q2r%i.s0\n" % (i, i))
  for i in range(n):
    f.write("p2r%i.s0 r? p2r%i\n" % (i + 1, i))
  for i in range(k):
    f.write("q2r%i.s0 r? q2r%i\n" % (i, i))
  if r == 0:
    f.write("p2r0.s1 i? p3r0.s0\n")
  write_footer(f)

for n in range(1,17):
  for r in [0, 1]:
    wide_flat(n, r)
    wide_deep(n, r)
for n in range(1,51):
  for r in [0, 1]:
    for k in range(1,11):
      const_deep(n, k, r)
      const_branch(n, k, r)

sys.exit(0)

