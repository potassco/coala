from distutils.core import setup
from distutils.command.install import INSTALL_SCHEMES

for scheme in INSTALL_SCHEMES.values():
    scheme['data'] = scheme['purelib']

setup(
    # Application name:
    name="coala",

    # Version number (initial):
    version="2.459",

    # Application author details:
    author="Christian Schulz-Hanke",
    author_email="Christian.Schulz-Hanke@cs.uni-potsdam.de",

    # Packages
    packages=["coala","coala.parse","coala.bc","coala.bc_legacy","coala.bcLc","coala.b","coala.bcAgent","coala.bcAgent_legacy"],

    #
    scripts=["coala/coala","outputformatclingocoala"],

    # Include additional files into the package
    #include_package_data=True,

    # Details
    url="https://github.com/potassco/coala",

    #
    # license="LICENSE.txt",
    description="coala - Action Language Translation Tool.",

    # long_description=open("README.txt").read(),
    long_description=open("README.txt").read(),

    # Dependent packages (distributions)
    install_requires=[
        "ply>=3.8",
    ],

    data_files=[
            ("coala",["coala/README_BC.txt"]),
            ("coala/internal", ["coala/internal/arithmetic.lp", \
                "coala/internal/csp.lp", \
                "coala/internal/fixed.lp", \
                "coala/internal/fixed_not_decoupled.lp", \
                "coala/internal/iterative.lp", \
                "coala/internal/iterative_not_decoupled.lp", \
                "coala/internal/states.lp", \
                "coala/internal/states_not_decoupled.lp", \
                "coala/internal/transitions.lp", \
                "coala/internal/transitions_not_decoupled.lp", \
                "coala/internal/only_in_domains.lp"]),

            ("coala/testcases", [ "coala/testcases/add_1.bc", \
                "coala/testcases/add_2.bc", \
                "coala/testcases/add_3.bc", \
                "coala/testcases/add_4.bc", \
                "coala/testcases/bug2.b", \
                "coala/testcases/bug.b", \
                "coala/testcases/dom_1.bc", \
                "coala/testcases/dom_2.bc", \
                "coala/testcases/dom_3.bc", \
                "coala/testcases/dom_4.bc", \
                "coala/testcases/ex_int_2.sh", \
                "coala/testcases/ex_int.sh", \
                "coala/testcases/flu.bc", \
                "coala/testcases/greedy.bc", \
                "coala/testcases/int_10.bc", \
                "coala/testcases/int_11.bc", \
                "coala/testcases/int_12.bc", \
                "coala/testcases/int_13.bc", \
                "coala/testcases/int_14.bc", \
                "coala/testcases/int_15.bc", \
                "coala/testcases/int_16.bc", \
                "coala/testcases/int_17.bc", \
                "coala/testcases/int_18.bc", \
                "coala/testcases/int_19.bc", \
                "coala/testcases/int_20.bc", \
                "coala/testcases/int_21.bc", \
                "coala/testcases/int_22.bc", \
                "coala/testcases/int_23.bc", \
                "coala/testcases/int_2.bc", \
                "coala/testcases/int_3.bc", \
                "coala/testcases/int_4.bc", \
                "coala/testcases/int_5.bc", \
                "coala/testcases/int_6.bc", \
                "coala/testcases/int_7.bc", \
                "coala/testcases/int_8.bc", \
                "coala/testcases/int_9.bc", \
                "coala/testcases/int.bc", \
                "coala/testcases/neg.bc", \
                "coala/testcases/role_1.bc", \
                "coala/testcases/role_2.bc", \
                "coala/testcases/role_3.bc", \
                "coala/testcases/role_4.bc", \
                "coala/testcases/role_5b.bc", \
                "coala/testcases/role_5.bc", \
                "coala/testcases/role_6.bc", \
                "coala/testcases/statebuild.bc", \
                "coala/testcases/test10.bc", \
                "coala/testcases/test1.b", \
                "coala/testcases/test1.bc", \
                "coala/testcases/test2.bc", \
                "coala/testcases/test3.bc", \
                "coala/testcases/test4.bc", \
                "coala/testcases/test5.bc", \
                "coala/testcases/test6.bc", \
                "coala/testcases/test7.bc", \
                "coala/testcases/test8.bc", \
                "coala/testcases/test9.bc", \
                "coala/testcases/test_benjamin2.bc", \
                "coala/testcases/test_benjamin3.bc", \
                "coala/testcases/test_benjamin.bc", \
                "coala/testcases/test_evil.bc", \
                "coala/testcases/test_false.bc", \
                "coala/testcases/test_neg_act.bc", \
                "coala/testcases/test_nex.bc", \
                "coala/testcases/test_true.bc", \
                "coala/testcases/test_where.b", \
                "coala/testcases/test_where.bc", \
		"coala/testcases/test_true_2.bc", \
		"coala/testcases/test_bound.bc", \
		"coala/testcases/test_bound_2.bc", \
		"coala/testcases/test_bound_3.bc", \
		"coala/testcases/var_bug_2.bc", \
		"coala/testcases/var_bug_1.bc", \
		"coala/testcases/binding_3.bc", \
		"coala/testcases/binding_2.bc", \
		"coala/testcases/binding_1.bc", \
		"coala/testcases/test_domain_var.bc", \
		"coala/testcases/dom_6.bc", \
		"coala/testcases/dom_5.bc", \
		"coala/testcases/test_where_dot.bc", \
		"coala/testcases/test_where_6.bc", \
		"coala/testcases/test_where_5.bc", \
		"coala/testcases/test_where_4.bc", \
		"coala/testcases/test_where_3.bc", \
		"coala/testcases/test_where_2.bc", \
		"coala/testcases/test_true_false.bc"])
            ]
)

# Build: python setup.py sdist
