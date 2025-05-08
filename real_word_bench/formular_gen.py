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
    print(generate_ltl(3))
    print(generate_pltl(3))

if __name__ == "__main__":
    main()
