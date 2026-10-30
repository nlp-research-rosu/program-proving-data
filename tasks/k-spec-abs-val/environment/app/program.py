# `x` is the program's input: the literal argument of the call below stands
# for an arbitrary integer (a symbolic integer in the claim's call).
def abs_val(x):
    if x < 0:
        return -x
    return x

result = abs_val(31337)
