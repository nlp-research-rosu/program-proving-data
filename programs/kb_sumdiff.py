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
