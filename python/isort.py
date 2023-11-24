#!/usr/bin/env python3

# How would you formally convince yourself that this implementation of insertion sort:
# 1) terminates (doesn't loop forever);
# 2) returns the correct output for all input lists?
def isort(l: list[int]) -> list[int]:
    if l == []: return []

    h,t = l[0], l[1:]
    sorted_t = isort(t)
    return insert(h, sorted_t)

def insert(x: int, l: list[int]) -> list[int]:
    if l == []: return [x]

    h,t = l[0], l[1:]
    if x < h:
        return [x, h, *t]
    else:
        return [h, *insert(x, t)]
