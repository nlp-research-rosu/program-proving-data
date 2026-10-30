# The module-level assignments below are the inputs: their literal values stand
# for arbitrary integers (symbolic in the claim).
a = 31337
b = 31338
n = 31339
if a <= b:
    m = a
    x = b
else:
    m = b
    x = a
t = x - m
res = 0
i = 0
while i < n:
    res = res + t
    i = i + 1
res = res + m
