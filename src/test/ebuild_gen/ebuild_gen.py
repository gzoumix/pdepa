import subprocess
import pathlib
import os
import random

DIR = "./icse"
NAME = "icse"

FM_NUM = 100
FEATURE_NUM = 100
SHARED_FEATURES_POSSIBLE_NUMS = range(0,6)
CONSTRAINTS_NUM = 400

CNF_GEN_CMD = ["Power-Law-Random-SAT-Generator/CreateSAT", "-g", "u", "-k", "3", "-u", "1"] #, "-q"]

# -s seed
# -f file
# -v {} -c {}


# generate directory FMcat if it does not exist
pathlib.Path("{}/{}".format(DIR,NAME)).mkdir(parents=True, exist_ok=True)

for i in range(FM_NUM):

    # generate the CNF file

    opt = ["-s", "{}".format(i)]
    opt += ["-f", "{}/{}".format(DIR,i)]
    opt += ["-v", "{}".format(FEATURE_NUM), "-c", "{}".format(CONSTRAINTS_NUM)]

    process = subprocess.Popen(CNF_GEN_CMD + opt,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()

    # load the clauses in memory and delete the cnf file
    with open(DIR + "/{}.cnf".format(i)) as f:
        lines = f.readlines()
    os.remove(DIR + "/{}.cnf".format(i))
    lines = [x for x in lines if not x.startswith("c") and not x.startswith("p")]
    clauses = [[int(x) for x in y.split(" ")] for y in lines]

    # start content
    content = """EAPI=6
DESCRIPTION="FM {}, features {}, shared features {}, constraints {}"
SLOT="0"
KEYWORDS="amd64 sh sparc x86"
""".format(FM_NUM, FEATURE_NUM, SHARED_FEATURES_POSSIBLE_NUMS, CONSTRAINTS_NUM)

    # generate IUSE
    content += "IUSE=\""
    for j in range(1,FEATURE_NUM+1):
        content += " f{}".format(j)
    content += "\"\n"

    # generate REQUIRED_USE
    content += "REQUIRED_USE=\""
    for j in clauses:
        content += " || ("
        for k in j:
            if k > 0:
                content += " f{}".format(k)
            elif k < 0:
                content += " !f{}".format(-k)
        content += " )"
    content += "\"\n"

    # generate shared feature constraints
    n = random.choice(SHARED_FEATURES_POSSIBLE_NUMS)
    if n > 0:
        shared_features = random.choices(list(range(i)) + list(range(i+1,FM_NUM)), k=n)
        content += "DEPEND=\""
        for j in range(n):
            content += " f{}? ( {}/FM{} )".format(j+1, NAME, shared_features[j])
        content += "\"\n"

    #write ebuild file
    pathlib.Path("{}/{}/FM{}".format(DIR,NAME,i)).mkdir(parents=True, exist_ok=True)
    with open("{}/{}/FM{}/FM{}-0.ebuild".format(DIR,NAME,i,i), "w") as f:
        f.write(content)

    # write metadata
    pathlib.Path(DIR + "/metadata").mkdir(parents=True, exist_ok=True)
    with open(DIR + "/metadata/layout.conf", "w") as f:
        f.write("repo-name={}\nmasters=".format(NAME))

    # write categories
    with open(DIR + "/categories", "w") as f:
        f.write("{}\n".format(NAME))
