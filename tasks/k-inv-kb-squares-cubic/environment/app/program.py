# The module-level assignments below are the inputs: their literal values stand
# for arbitrary integers (symbolic in the claim).
n = 137
res = 0
i = n
while 0 < i:
    j = i
    while 0 < j:
        res = res + i
        j = j - 1
    i = i - 1
