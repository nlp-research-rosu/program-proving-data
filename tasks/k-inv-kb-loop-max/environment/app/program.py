# The module-level assignments below are the inputs: their literal values stand
# for arbitrary integers (symbolic in the claim).
a = 31337
n = 31338
max = a
i = 0
while i < n:
    if max < i:
        max = i
    i = i + 1
