# FM random generator

The script ebuild_gen.py creates a portage repository containing packages
corresponding to randomly generated FM. To generate the feature models the
SAT generator available at
https://github.com/RalfRothenberger/Power-Law-Random-SAT-Generator.git
is used.

## Install & Run

To install the generator the SAT generator must be installed first .
This can be done by running in the folder containing the ebuild_gen.py
the following commands.

```
git clone https://github.com/RalfRothenberger/Power-Law-Random-SAT-Generator.git
cd Power-Law-Random-SAT-Generator
make
```

To run the generator you can run the command `python3 ebuild_gen.py` in the
folder containing it. This will create a folder icse containing the generated
ebuild files.

The number of FMs, their features and constraints can be controlled by setting
the values of the the variables in the ebuild_gen.py file.

