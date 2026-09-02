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
