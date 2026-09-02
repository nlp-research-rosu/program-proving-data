a = 31337
b = 31338
n = 31339
t = a * b
if t < 0:
    t = 0 - t
res = 0
i = 0
while i < n:
    res = res + t
    i = i + 1
res = res + a
