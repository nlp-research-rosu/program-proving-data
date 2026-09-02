def sum_to_n(n):
    acc = 0
    i = 1
    while i <= n:
        acc = acc + i
        i = i + 1
    return acc

result = sum_to_n(5)
