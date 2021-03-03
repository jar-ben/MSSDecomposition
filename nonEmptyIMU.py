from imuSolver import IMUSolver
import glob

#parse .gcnf instance,
#returns a pair C,B where B contains the base (hard) clauses and C the other clauses
def parse(filename):
    C = []
    B = []
    with open(filename, "r") as f:
        lines = f.readlines()
        if filename[-5:] == ".gcnf":
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[1:-1]]
                if len(cl) > 0:
                    if line[0] == "{0}":
                        B.append(cl)
                    else:
                        C.append(cl)
        else:
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[:-1]]
                if len(cl) > 0:
                    C.append(cl)
    return C,B

with open("emptyIMU.csv", "w") as f:
    empty = []
    iter = 1
    for b in glob.glob("/home/xbendik/benchmarks/SAT11/*.cnf"):
        print(b)
        C,B = parse(b)
        if IMUSolver(C,B).emptyImu():
            print ("empty", len(empty), iter)
            empty.append(b)
            f.write(b + "\n")
        else:
            print("Nonempty", len(empty), iter)
        iter += 1
    print("\n\n")
    for b in empty:
        print(b)


