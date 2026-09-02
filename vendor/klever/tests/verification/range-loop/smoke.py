def f(n):
    total = 0
    i = 0
    for i in range(n):
        total += i
    return total


assert f(0) == 0
assert f(1) == 0
assert f(4) == 6
assert f(5) == 10
assert f(10) == 45
