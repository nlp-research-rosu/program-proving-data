# The module-level assignments below are the inputs: their literal values stand
# for arbitrary integers (symbolic in the claim).
a = 31337
if a < 0:
    res = 0
else:
    if 10 < a:
        res = 10
    else:
        res = a
