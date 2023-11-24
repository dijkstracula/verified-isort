import random
import sys

from isort import *

# Our "correctness proof": Generate a whole bunch of random lists and verify
# that our sort algorithm behaves identically to Python's built-in sort routine.
# (Does this remind you of a proof technique we saw in a paper this term?)
for _ in range(250):
    l = [random.randrange(-2**64, (2**64) - 1) for _ in range(random.randrange(0, 500))]
    sorted_l = isort(l)
    assert(sorted_l == sorted(l))
    sys.stderr.write("."); sys.stderr.flush()
print("\nrandom tester failed to find a bug!")
