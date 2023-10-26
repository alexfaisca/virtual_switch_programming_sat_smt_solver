def parse_input(input_str: str):
    """Parses the input file. The input file provided is assumed to be correct

    Args:
        input_str (str): Input to parse

    Returns:
        n (int): Number of groups of rules
        m (int): Number of switches
        mr (list[int]): List of memory requirement
        ns (list[int]): List of number of stages
        mc (list[int]): List of memory capacity
        d (int): Number of dependencies
        f (list[(list[int])]): List of rules for forwarding
    """
    if input_str[-1] != '\n':
        input_str += '\n'
    lines = input_str.split('\n')[:-1]
    n, m = [int(line) for line in lines[:2]]
    mr = [int(i) for i in lines[2].split(' ')]
    ns = [int(i) for i in lines[3].split(' ')]
    mc = [int(i) for i in lines[4].split(' ')]
    d = int(lines[5])
    f = [[int(i) for i in line.split(' ')] for line in lines[6: (6 + d)]]

    return n, m, mr, ns, mc, d, f


def generate_output(recirculations: int, order: list, placements: list):
    """Generates the string to be output to solution.txt

    Args:
        recirculations (int): Overall number of re-circulations
        order (list[int]): Order of the switches
        placements (list[(list[list[int]])]): Placement of groups of rules in each stage of each switch

    Returns:
        out (str): String to be printed to solution.txt
    """
    out = f"{recirculations}\n"

    for i in range(len(order)):
        out += f"{order[i]} "

    out = out[:-1]
    out += "\n"

    for switch in placements:
        for stage in switch:
            for rule in stage:
                out += f"{rule} "
            out = out[:-1]
            out += ", "
        out = out[:-2]
        out += "\n"

    return out