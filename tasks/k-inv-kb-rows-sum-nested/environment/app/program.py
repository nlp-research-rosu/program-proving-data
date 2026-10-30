# The module-level assignments below are the inputs: their literal values stand
# for arbitrary integers (symbolic in the claim).
a = 137
b = 138
sum = 0
i = a
while 0 < i:
    j = b
    while 0 < j:
        sum = sum + j
        j = j - 1
    i = i - 1
