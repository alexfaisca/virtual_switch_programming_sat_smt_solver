# 1. Encoding

In MaxSAT problems, encoding variables is a crucial step in representing constraints and optimizing solutions efficiently. The encoding we decided to use is divided into two contiguous zones: the first one (1) is dedicated to encode which groups of rules are attributed to each of the stages of each switch, and the second zone (2) encodes the relative positions of each pair of switches:

(1) To encode the position in the switch of the groups of rules into SAT variables we considered the continuous order of all switches such that each variable indicates the presence of its encoding rule in the switche’s stage it belongs to. As such, we used the following formula:

	E(switch, stage, rule) = max(E(switch - 1, -, -)) + (#previous_stages . #rules) + rule

(2) To encode the relative position of each pair of switches we started the encoding in the maximum id + 1, ensuring that no SAT variable is repeated. This separation value between the two encoding zones plays a crucial role throughout the developed code. Following this divide, there are #switches² encoded positions: each for each one of the possible paired relative positions. To ensure that there is a variable which indicates the relative position switch_A-switch_B and another one which encodes the relative position switch_B-switch_A we used the following formula for the second part of the encoding:

	E(previous_switch, succeding_switch) = d + switch_count . (previous_switch - 1) + (succeding_switch - 1) + 1 with, d = max(E(switches_count, -, -))

The drawback of this method is that there are switch_count positions which indicate the relative position of a switch in relation to itself. As such, we remove these positions from the solver’s solution before building the representation to be output. 

# 2. Algorithm Constraints

The project goal is to present a solution satisfying the problem’s hard restrictions while minimizing the number of re-circulations. As a MAXSAT problem, there are hard and soft clauses, that is, the must-haves and the preferences, respectively. The chosen solver “”RC2” tries to maximize the number of soft clauses satisfied (each one with a weight of 1, meaning they all have the same priority) while obligatorily satisfying all hard clauses. Please note that before adding the clauses in our project we included an annotation regarding which of the following clauses the code constitutes. For this purpose, the hard and soft clauses generated were the following:

1 - Hard Clauses

1.1 - Individually placing a group of rules in a stage
1.1.1 - For each stage of every switch at least one group of rules is placed there. Please note that this requirement is placed in the same loop as the requirement 1.4.1 to improve performance.
1.1.2 - Each group of rules appears at least once in one stage in one switch.
1.1.3 - If a group of rules appears in a certain stage of a switch, then, it cannot appear in any of the remaining stages of the same switch.
1.1.4 - If a group of rules appears in a certain stage of a switch, then, it cannot appear in any of the remaining stages of all of the remaining switches.

1.2 - Consistent relative switch order, i.e. either switch_a comes before switch_b or switch_b comes before switch_a.

We decided to use a topological sort to convert a list of pairs of relative positions to a list of absolute positions. With this intention, we decided to use the function “DiGraph” to create the graph from which its topological order is to be derived and the function “topological_sort” to extract its absolute order. Both of these functions reside in the “networkx” module. With the purpose of obtaining a valid absolute order the following hard constraints were taken into account:

1.2.1 - Regarding the second part of the continuous of encoding (relative position of each pair of switches) if the variable x that encodes that switch A precedes switch B is true, then the variable y that encodes that switch B precedes switch A is false. That is, x ⇒ not y.
1.2.2 - Also regarding the second part of the continuous encoding, either the variable x that encodes that switch A precedes switch B is true or the variable y that encodes that switch B precedes switch A is true, that is x ∨ y.	
1.2.3 - The transitivity of switch positions is respected, i.e. if switch A comes before switch B and switch B comes before switch C, then switch A must come before switch C.

1.3 - For each dependency (A, B) A cannot be placed in a switch which succeeds the switch in which B is placed (there is no re-circulation between switches).

1.3.1 - For each dependency (A, B) given, if A is placed in a certain switch in a certain stage and if B is placed in a certain switch in a certain stage (they are not in the same place), then the switch where A is cannot succeed B.

1.4 - The sum of all memory requirements of all the groups of rules placed in a stage of a switch cannot exceed the switch’s memory capacity (value for each of its stages).

1.4.1 - Using the “atmost” (leq) function of the “PBEnc” module we declared a list of hard clauses enforcing this hard requirement. The “lits” parameter contains the encoding of all rules per switches’ stage with the “weights” parameter being the list of memory requirements of said rules.

2 - Soft Clauses

2.1 - The number of intra switch forwarding must be minimized as much as possible without compromising any hard clauses.

2.1.1 - The number of occurrences where a group of rules A is placed in a certain stage of a switch and a group of rules B such that (A, B) is a dependency and B is placed in the same stage of the same switch as A is minimized accounting for 2.1.2.
2.1.2 - The number of occurrences where a group of rules A is placed in a certain stage of a switch and a group of rules B such that (A, B) is a dependency and B is placed in a previous stage of the same switch as A is minimized accounting for 2.1.1.

# 3. Algorithm Optimizations

Given the time consuming nature of this problem computationally, making sure that the algorithm used is as efficient as possible is of high importance, so that solutions can be obtained within a reasonable time with reasonable resources. As such, we applied the following optimizations to our solution:

1 - Upon setting the “adapt” flag to true in the “RC2” solver we noticed a considerable performance improvement in larger tests. We hypothesize that is due to detection and adaptation of AtMost1 constraints, that is, the creation of our requirements create several instances where this applies.	

2 - Avoiding redundant clause appendage. The creation of clauses is done iteratively and in the development process we realized that merely looping through the possible value range of the switch and rule set groups and creating clauses from said values, up to three quarters of the clauses for each requirement would add no value in constraining the solution and, in turn, represented a stark increase in computation time.

3 - Initially, we opted for encoding switch positions through a direct translation of absolute position placements of each switch. However, in the scope of the regarded problem, the absolute position is not relevant if not for the deduction of switch precedence which may be directly encoded in boolean variables, greatly simplifying the clause creation process and expressiveness with which the different switches are positionally related to each other.

4 - Excluding clauses upfront. By accounting for rule set memory requirements and switch stage memory capacity we were able to reduce the number of created clauses, simplify the derivative process, therefore reducing computation time.

# 4. Running the Code

The project was implemented using python 3.9 with the help of the following functions:

The function “RC2” from the “pysat.examples.rc2” module:
Implementation of the “RC2” (relaxed cardinality constraints) algorithm, used for solving maximum satisfiability problems.
The function “WCFN” from the “pysat.formula module”:
Functions used for partially weighted “CNF” formula manipulation.
The “PBEnc” function from the pysat.pb module:
Functions used for creating CNF encoded pseudo-boolean constraints.
The “DiGraph” and “topological_sort” functions from the “networkx” module:
Functions used for obtaining the topological sort of a graph created with a list of pairs of relative positions in order to obtain the absolute positions.
			
In order to install the necessary dependencies from the main directory run:

### pip3 install -r requirements.md

Following this, to run the project from the main directory simply run the main python file as follows:

### python3 project1.py < instance.apr > solution.out

instance.apr contains the formulation of the problem. 
project1 writes the solution to the standard output, which can, however, be redirected to a certain file (e.g. solution.out).

		



