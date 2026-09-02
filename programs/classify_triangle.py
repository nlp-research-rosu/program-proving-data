def classify_triangle(a, b, c):
    equal_pairs = 0
    if a == b:
        equal_pairs = equal_pairs + 1
    if b == c:
        equal_pairs = equal_pairs + 1
    if a == c:
        equal_pairs = equal_pairs + 1
    if equal_pairs == 3:
        return "equilateral"
    if equal_pairs >= 1:
        return "isosceles"
    return "scalene"

result = classify_triangle(31337, 31338, 31339)
