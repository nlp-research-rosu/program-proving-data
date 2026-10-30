# The module-level assignments below are the inputs: their literal values stand
# for arbitrary integers (symbolic in the claim).
a = 31337
b = 31338
if a < b:
    t = b - a
else:
    t = a - b
res = 0
while 0 < t:
    res = res + 2
    t = t - 1
