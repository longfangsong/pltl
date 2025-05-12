def generate_ltl(n: int) -> str:
    result_subparts = []
    for i in range(n):
        for j in range(n):
            if i != j:
                result_subparts.append(f"!(g{i} & g{j})")
    for i in range(n):
        result_subparts.append(f"(G (r{i} -> (F g{i})))")
    for i in range(n):
        result_subparts.append(f"(!g{i} W r{i})")
    for i in range(n):
        result_subparts.append(f"(g{i} -> X(!g{i} W r{i}))")
    return " & ".join(result_subparts)

def generate_pltl(n: int) -> str:
    result_subparts = []
    for i in range(n):
        for j in range(n):
            if i != j:
                result_subparts.append(f"¬(g{i} & g{j})")
    for i in range(n):
        result_subparts.append(f"G(F(¬r{i} ~S g{i}))")
    for i in range(n):
        result_subparts.append(f"G(g{i} -> (r{i} | Y(r{i} B ¬g{i})))")
    return " & ".join(result_subparts)

def main():
    import sys
    if len(sys.argv) != 2:
        print("用法: python formular_gen.py <n>")
        sys.exit(1)
    try:
        n = int(sys.argv[1])
    except ValueError:
        print("错误: n 必须是一个整数")
        sys.exit(1)
    print(generate_ltl(n))
    print(generate_pltl(n))

if __name__ == "__main__":
    main()
