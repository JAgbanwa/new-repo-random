import sys
from math import gcd, isqrt


A = ZZ(44757920541557886090117534052694970)
B = ZZ(41101605718451981985262266514352514)
FIXED_DENOMINATOR = ZZ(7459653423592981015019589008782495)

C = ZZ(14943710739363051807392239500134940340216512331484305017109993121648634954593412761173983605940837745500)
D = ZZ(41168836667217376486392898923226855162406039941508780208736146911477302784935787559470326556977126731300)
E = ZZ(37805717336939093549401509101689288012340233850123507665556436144504449035107266727435086128803992307060)
F = ZZ(11572444750818543658717305816501477829412732700480505677240043411313263379471980801880810394549554462101)


def rhs_original(k):
    k = QQ(k)
    return C*k**3 + D*k**2 + E*k + F


def lhs_original(x, y, k):
    x = QQ(x)
    y = QQ(y)
    k = QQ(k)
    return y*x**2 + 2*y*(y + A*k + B)*x


def rhs_reduced(z):
    z = QQ(z)
    return z**3 / 6 - 23


def lhs_reduced(x, y, z):
    x = QQ(x)
    y = QQ(y)
    z = QQ(z)
    return y*x**2 + 2*y*(y + z)*x


def k_from_z(z):
    return (QQ(z) - B) / A


def fixed_denominator_numerator_from_z(z):
    z = ZZ(z)
    if (z - B) % 6 != 0:
        return None
    return (z - B) // 6


def rational_sqrt(q):
    q = QQ(q)
    if q < 0:
        return None

    numerator = ZZ(q.numerator())
    denominator = ZZ(q.denominator())
    root_numerator = ZZ(isqrt(int(numerator)))
    root_denominator = ZZ(isqrt(int(denominator)))

    if root_numerator**2 == numerator and root_denominator**2 == denominator:
        return QQ(root_numerator) / QQ(root_denominator)
    return None


def rationals_of_height(height, include_zero=True):
    if include_zero:
        yield QQ(0)

    for denominator in range(1, height + 1):
        for numerator in range(-height, height + 1):
            if numerator == 0:
                continue
            if gcd(abs(numerator), denominator) != 1:
                continue
            yield QQ(numerator) / QQ(denominator)


def add_solution(solutions, seen, x, y, z, source):
    x = QQ(x)
    y = QQ(y)
    z = QQ(z)
    k = k_from_z(z)
    key = (x, y, k)

    if key in seen:
        return
    if lhs_reduced(x, y, z) != rhs_reduced(z):
        return
    if lhs_original(x, y, k) != rhs_original(k):
        return

    seen.add(key)
    solutions.append((x, y, z, k, source))


def search_integral_yz(bound=200, max_solutions=20):
    solutions = []
    seen = set()

    for z in range(-bound, bound + 1):
        z = ZZ(z)
        target = rhs_reduced(z)
        for y in range(-bound, bound + 1):
            if y == 0:
                continue
            y = ZZ(y)
            radicand = (y + z)**2 + target / y
            root = rational_sqrt(radicand)
            if root is None:
                continue

            add_solution(solutions, seen, -y - z + root, y, z, "integer y,z search")
            add_solution(solutions, seen, -y - z - root, y, z, "integer y,z search")

            if len(solutions) >= max_solutions:
                return solutions

    return solutions


def search_rational_yz(height=25, max_solutions=20):
    solutions = []
    seen = set()
    values = list(rationals_of_height(height))

    for z in values:
        target = rhs_reduced(z)
        for y in values:
            if y == 0:
                continue
            radicand = (y + z)**2 + target / y
            root = rational_sqrt(radicand)
            if root is None:
                continue

            add_solution(solutions, seen, -y - z + root, y, z, "rational y,z search")
            add_solution(solutions, seen, -y - z - root, y, z, "rational y,z search")

            if len(solutions) >= max_solutions:
                return solutions

    return solutions


def search_fixed_denominator(z_bound=200, y_bound=200, max_solutions=20):
    solutions = []
    seen = set()

    for z in range(-z_bound, z_bound + 1):
        z = ZZ(z)
        a = fixed_denominator_numerator_from_z(z)
        if a is None or gcd(abs(ZZ(a)), FIXED_DENOMINATOR) != 1:
            continue

        target = rhs_reduced(z)
        for y in range(-y_bound, y_bound + 1):
            if y == 0:
                continue
            y = ZZ(y)
            radicand = (y + z)**2 + target / y
            root = rational_sqrt(radicand)
            if root is None:
                continue

            add_solution(solutions, seen, -y - z + root, y, z, "fixed denominator search")
            add_solution(solutions, seen, -y - z - root, y, z, "fixed denominator search")

            if len(solutions) >= max_solutions:
                return solutions

    return solutions


def print_solution(solution, show_fixed_denominator=False):
    x, y, z, k, source = solution
    print(f"source: {source}")
    print(f"x = {x}")
    print(f"y = {y}")
    print(f"z = A*k + B = {z}")
    print(f"k = {k}")
    if show_fixed_denominator:
        a = fixed_denominator_numerator_from_z(z)
        print(f"a = {a}")
        print(f"b = {FIXED_DENOMINATOR}")
        print(f"gcd(a,b) = {gcd(abs(ZZ(a)), FIXED_DENOMINATOR)}")
    print()


def option_value(name, default):
    prefix = name + "="
    for argument in sys.argv[1:]:
        if argument.startswith(prefix):
            return int(argument[len(prefix):])
    return default


assert QQ(C) == QQ(A)**3 / 6
assert QQ(D) == QQ(A)**2 * QQ(B) / 2
assert QQ(E) == QQ(A) * QQ(B)**2 / 2
assert QQ(F) == QQ(B)**3 / 6 - 23
assert A == 6 * FIXED_DENOMINATOR


if __name__ == "__main__":
    print("Using z = A*k + B, the RHS is z^3/6 - 23.")
    print("Searching the reduced equation y*x^2 + 2*y*(y + z)*x = z^3/6 - 23.")
    print()

    fixed_denominator_mode = "--fixed-denominator" in sys.argv[1:]
    if fixed_denominator_mode:
        z_bound = option_value("--z-bound", 200)
        y_bound = option_value("--y-bound", 200)
        max_solutions = option_value("--max", 20)
        print(f"Restricting to k = a/b with b = {FIXED_DENOMINATOR} and gcd(a,b) = 1.")
        print(f"Searching |z| <= {z_bound}, |y| <= {y_bound}.")
        print()
        solutions = search_fixed_denominator(
            z_bound=z_bound,
            y_bound=y_bound,
            max_solutions=max_solutions,
        )
    else:
        solutions = search_integral_yz(bound=200, max_solutions=20)
    if not solutions:
        if fixed_denominator_mode:
            print("No fixed-denominator solutions found in the selected bounds.")
            sys.exit(0)
        solutions = search_rational_yz(height=25, max_solutions=20)

    if not solutions:
        print("No solutions found in the selected bounds.")
    else:
        for solution in solutions:
            print_solution(solution, show_fixed_denominator=fixed_denominator_mode)