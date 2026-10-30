# The module-level assignments below are the inputs: their literal values stand
# for arbitrary integers (symbolic in the claim).
n = 31337
count = 0
i = 0
while i < n:
    if i % 2 == 0:
        count = count + 1
    i = i + 1
