# The module-level assignments below are the inputs: their literal values stand
# for arbitrary integers (symbolic in the claim).
a = 31337
b = 31338
n = 31339
if n < 0:
    n = 0 - n
count = 0
while 0 < n:
    n = n - 1
    count = count + 1
res = count * a + b
