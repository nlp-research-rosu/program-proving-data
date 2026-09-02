a = 137
b = 138
res = 0
i = a
while 0 < i:
    if i <= b:
        j = i
        while 0 < j:
            res = res + 1
            j = j - 1
    i = i - 1
