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
  f = fopen("wide_flat_%i" % r, "%i" % n)
  write_header(f)
  f.write("p0.s0 <= q0.s0\n")
  f.write("p0.s0 c? p1.s0.s0\n")
  f.write("p1.s0 r? p2\n")
  f.write("p2.s0 c? p3.s0.s0\n")
  f.write("p3.s0 i? p4.s0\n")
  for i in range(n):
    f.write("q0.s0 c? q1.s0.s%i\n" % (i))
    f.write("q2.s%i c? q3.s0.s%i\n" % (i, i))
  f.write("q1.s0 r? q2\n")
  for i in range(n + 1):
    f.write("q3.s0 i? q4.s%i\n" % (i))
  if r == 0:
    f.write("p4.s0 r? p5\n")
  write_footer(f)

def wide_deep(n, r):
  f = fopen("wide_deep_%i" % r, "%i" % n)
  write_header(f)
  f.write("p0.s0 <= q0.s0\n")
  f.write("p0.s0 c? p1r0.s0.s0\n")
  f.write("q0.s0 c? q1r0.s0.s0\n")
  for i in range(n):
    f.write("q1r%i.s0 i? q2r%i.s0\n" % (i, i))
    f.write("p1r%i.s0 c? p1r%i.s0.s0\n" % (i, i + 1))
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i))
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i + 1))
    f.write("p2r%i.s0 r? p2r%i\n" % (i + 1, i))
  f.write("p1r%i.s0 i? p2r%i.s0\n" % (n, n))
  f.write("p2r0.s0 r? p3r0\n")
  for i in range(n):
    f.write("q2r%i.s0 r? q2r%i\n" % (i, i))
    f.write("q2r%i.s0 r? q3r0\n" % (i))
  if r == 0:
    f.write("p3r0.s0 r? p4r0\n")
  write_footer(f)

def alternating(n, r):
  f = fopen("alternating", "%i_%i" % (r, n))
  write_header(f)
  f.write("p0.ss <= q0.ss\n")
  f.write("p0.ss c0? p1.s0.ss\n")
  f.write("p0.ss c1? p1.s1.ss\n")
  f.write("q0.ss c0? q0.s0.ss\n")
  f.write("q0.ss c1? q1.s0.ss\n")
  for i in range(n):
    f.write("p%i.s0 c? p%i.s0.s0\n" % (i, i + 1))
    f.write("p%i.s0 c? p%i.s1.s0\n" % (i, i + 1))
    f.write("p%i.s1 c? p%i.s0.s1\n" % (i, i + 1))
    f.write("p%i.s1 c? p%i.s1.s1\n" % (i, i + 1))

    f.write("q%i.s0 c? q%i.s0.s0\n" % (i, i))
    f.write("q%i.s0 c? q%i.s0.s0\n" % (i, i + 1))
  for i in range(n + 1):
    f.write("q%i.s0 i? qq%i.s0\n" % (i, i))
  f.write("p%i.s0 i? pp0.s0\n" % (n))
  f.write("p%i.s1 i? pp0.s1\n" % (n))
  for i in range(n):
    f.write("pp%i.s0 r? pp%i\n" % (i, i))
    f.write("pp%i.s1 r? pp%i\n" % (i, i + 1))
    f.write("qq%i.s0 r? qq%i\n" % (i, i))
  f.write("qq%i.s0 r? qq%i\n" % (n, n))
  if r == 0:
    for i in range(n + 1):
      f.write("pp%i.ss i%i? pf.ss\n" % (i, i))
  write_footer(f)

def const_deep(n, k, r):
  f = fopen("const_deep_%i" % r, "%i_%i" % (k, n))
  write_header(f)
  f.write("p0.s0 <= q0.s0\n")
  f.write("p0.s0 c? p1r0.s0.s0\n")
  f.write("q0.s0 c? q1r0.s0.s0\n")
  for i in range(n):
    f.write("p1r%i.s0 c? p1r%i.s0.s0\n" % (i, i))
    f.write("p1r%i.s0 c? p1r%i.s0.s0\n" % (i, i + 1))
    f.write("p2r%i.s0 r? p2r%i\n" % (i + 1, i))
  for i in range(k):
    f.write("q1r%i.s0 i? q2r%i.s0\n" % (i, i))
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i))
    f.write("q1r%i.s0 c? q1r%i.s0.s0\n" % (i, i + 1))
  f.write("p1r%i.s0 i? p2r%i.s0\n" % (n, n))
  f.write("p2r0.s0 r? p3r0\n")
  for i in range(k):
    f.write("q2r%i.s0 r? q2r%i\n" % (i, i))
    f.write("q2r%i.s0 r? q2r%i\n" % (i, i + 1))
    f.write("q2r%i.s0 r? q3r0\n" % (i))
  if r == 0:
    f.write("p3r0.s0 r? p4r0\n")
  write_footer(f)

#size = int(sys.argv[1])
#ref = int(sys.argv[2])

for n in range(1,51):
  for r in [0, 1]:
    #alternating(n, r)
    #wide_flat(n, r)
    wide_deep(n, r)
    for k in range(1,26):
      const_deep(n, k, r)

sys.exit(0)

def make_refine_bench(n, r):
  filename = "bench_%s/vpda_%s_%i" % (r, r, n)
  f = open(filename, 'w')
  # header
  f.write("mprs vpda [\n")
  f.write("p1.s0 <= q1.s0\n")

  # rules
  for i in range(n):
    f.write("p1.s%i c? p1.s%i.s%i\n" % (i, i + 1, i))
    f.write("q1.s%i c? q1.s%i.s%i\n" % (i, i + 1, i))
    f.write("q1.s%i c? q1.s%i.t%i\n" % (i, i + 1, i))

  f.write("p1.s%i i? p2.s%i\n" % (n, n))
  f.write("q1.s%i i? q2.s%i\n" % (n, n))

  for i in range(n):
    f.write("p2.s%i r? p2\n" % (i + 1))
    f.write("q2.s%i r? q2\n" % (i + 1))
    f.write("q2.t%i r? q2\n" % (i + 1))

  f.write("p2.s0 i? p1.s0\n")
  if r == "y":
    f.write("q2.s0 i? q1.s0\n")

  # footer
  f.write("]\n")
  f.close()

def add_trans(f, s, i, j):
  f.write("%s%i.s0 c? %s%i.s0.s0\n" % (s, i, j))

def make_circle(n):
  filename = "vpda_circle_%i" % (n)
  f = open(filename, 'w')
  # header
  f.write("mprs vpda [\n")
  f.write("p0.s0 <= q0.s0\n")

  # rules
  f.write("p0.s0 c? p1.s1.s0\n")
  f.write("p1.s1 r? p1\n")
  for i in range(n):
    f.write("q0.s0 c? q%i.s%i.s%i\n" % (i, i, i))
    f.write("q%i.s%i r? r%i\n" % (i, i, i))
  
  # footer
  f.write("]\n")
  f.close()

def make_complete_refine(num_constants, num_rules):
  if num_rules == 0:
    filename = "vpda_complete_n%i" % (num_constants)
  else:
    filename = "vpda_complete_n%i_r%i" % (num_constants, num_rules)
  f = open(filename, 'w')
  # header
  f.write("mprs vpda [\n")
  f.write("s0.s0 <= s0.s0\n")
  cur_rules = 0
  # return rules
  for i1 in range(num_constants):
    for i2 in range(num_constants):
      for i3 in range(num_constants):
        if num_rules == 0 or cur_rules < num_rules:
          f.write("s%i.s%i r! s%i\n" % (i1, i2, i3))
          cur_rules += 1
  # internal rules
  for i1 in range(num_constants):
    for i2 in range(num_constants):
      for i3 in range(num_constants):
        for i4 in range(num_constants):
          if num_rules == 0 or cur_rules < num_rules:
            f.write("s%i.s%i i! s%i.s%i\n" % (i1, i2, i3, i4))
            cur_rules += 1
  # call rules
  for i1 in range(num_constants):
    for i2 in range(num_constants):
      for i3 in range(num_constants):
        for i4 in range(num_constants):
          for i5 in range(num_constants):
            if num_rules == 0 or cur_rules < num_rules:
              f.write("s%i.s%i c! s%i.s%i.s%i\n" % (i1, i2, i3, i4, i5))
              cur_rules += 1
  # footer
  f.write("]\n")

def make_complete_norefine(num_constants):
  f = open("vpda_nocomplete_n%i" % (num_constants), 'w')
  # header
  f.write("mprs vpda [\n")
  f.write("p.s0 <= q.s0\n")
  # call rules
  for i in range(num_constants - 1):
    f.write("p.s%i c? p.s%i.s%i\n" % (i, i + 1, i))
  f.write("q.s0 c? q.s0.T\n")
  f.write("q.s0 c? q.s1.T\n")
  for i in range(1, num_constants - 1):
    f.write("q.s%i c? q.s%i.s%i\n" % (i, i, i))
    f.write("q.s%i c? q.s%i.s%i\n" % (i, i + 1, i))
  # internal rules
  last = num_constants - 1
  f.write("p.s%i i? p%i.s%i\n" % (last, last, last))
  for i in range(num_constants):
    f.write("q.s%i i? q.s%i\n" % (i, i))
  # return rules
  f.write("p0.s0 r? p\n")
  for i in range(num_constants - 1):
    f.write("p%i.s%i r? p%i\n" % (i + 1, i + 1, i))
  for i in range(num_constants):
    f.write("q.s%i r? q\n" % (i))
  # footer
  f.write("]\n")

#size = int(sys.argv[1])
#ref = sys.argv[2]
#make_complete_norefine(size)
#make_complete_refine(size, 0)

for r in ["y", "n"]:
  for n in range(1, 100 + 1):
    pass
    #make_refine_bench(n, r)

for n in range(1, 1000 + 1):
  make_circle(n)


