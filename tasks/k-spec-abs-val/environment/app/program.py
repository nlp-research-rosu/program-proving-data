# The module-level assignments below are the inputs: their literal values stand
# for arbitrary integers (symbolic in the claim).
def abs_val(x):
    if x < 0:
        return -x
    return x

result = abs_val(31337)
