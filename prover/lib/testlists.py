#!/usr/bin/env python3

from itertools          import combinations

def read_list(file):
    return list(map(str.strip, open(file).readlines()))

no_unfold_3_5_20 = [ 't/SL-COMP18/bench/qf_shid_entl/16.tst.smt2'
                   , 't/SL-COMP18/bench/qf_shid_entl/append_sll_cll_slk-17.smt2'
                   , 't/SL-COMP18/bench/qf_shid_entl/lsegex4_slk-3.smt2'
                   , 't/SL-COMP18/bench/qf_shid_entl/lsegex4_slk-4.smt2'
                   , 't/SL-COMP18/bench/qf_shid_entl/lsegex4_slk-5.smt2'
                   ]
unfold_3_5_20 = [ 't/SL-COMP18/bench/qf_shid_entl/lsevenodd_ls2_01.sb.smt2'
                , 't/SL-COMP18/bench/qf_shid_entl/lsevenodd_ls2_02.sb.smt2'
                , 't/SL-COMP18/bench/qf_shid_entl/lsevenodd_ls2_05.sb.smt2'
                , 't/SL-COMP18/bench/qf_shid_entl/lsevenodd_ls2_06.sb.smt2'
                ]
    #         prefix   KT  RU timeout tests
test_lists = [ ('unfold-mut-recs . ',  3,  3,  '5m', read_list('t/test-lists/passing-3-3-5'))
             , ('unfold-mut-recs . ',  5, 12, '40m', read_list('t/test-lists/passing-5-12-40'))
             , ('unfold-mut-recs . ',  5,  6, '20m', read_list('t/test-lists/qf_shid_entl.unsat.5'))
             , ('unfold-mut-recs . ',  5,  9, '20m', read_list('t/test-lists/qf_shid_entl.unsat.8'))
             , ('',                    3,  5, '20m', no_unfold_3_5_20)
             , ('unfold-mut-recs . ',  3,  5, '20m', unfold_3_5_20)
             , ('unfold-mut-recs . ',  7,  7, '20m', ['t/SL-COMP18/bench/qf_shid_entl/ls_entail_ls_nonrec_07.sb.smt2'])
             , ('unfold-mut-recs . ',  8,  8, '20m', ['t/SL-COMP18/bench/qf_shid_entl/ls_entail_ls_nonrec_11.sb.smt2'])
             , ('unfold-mut-recs . ',  9,  9, '20m', ['t/SL-COMP18/bench/qf_shid_entl/ls_entail_ls_nonrec_12.sb.smt2'])
             , ('unfold-mut-recs . ', 10, 10, '20m', ['t/SL-COMP18/bench/qf_shid_entl/ls_entail_ls_nonrec_13.sb.smt2'])
             , ('unfold-mut-recs . ', 11, 11, '20m', ['t/SL-COMP18/bench/qf_shid_entl/ls_entail_ls_nonrec_14.sb.smt2'])
             , ('unfold-mut-recs . ', 12, 12, '20m', ['t/SL-COMP18/bench/qf_shid_entl/ls_entail_ls_nonrec_15.sb.smt2'])
             , ('unfold-mut-recs . ', 13, 13, '20m', ['t/SL-COMP18/bench/qf_shid_entl/ls_entail_ls_nonrec_16.sb.smt2'])
             , ('unfold-mut-recs . ',  6, 12, '10m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_02.sb.smt2'])
             , ('unfold-mut-recs . ',  8, 14, '10m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_03.sb.smt2'])
             , ('unfold-mut-recs . ',  6, 14, '10m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_04.sb.smt2'])
             , ('unfold-mut-recs . ',  6, 14, '10m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_05.sb.smt2'])
             , ('unfold-mut-recs . ', 10, 16, '20m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_07.sb.smt2'])
             , ('unfold-mut-recs . ',  8, 16, '10m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_08.sb.smt2'])
             , ('unfold-mut-recs . ',  8, 16, '10m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_09.sb.smt2'])
             , ('unfold-mut-recs . ',  8, 16, '10m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_10.sb.smt2'])
             , ('unfold-mut-recs . ', 10, 16, '20m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_11.sb.smt2'])
             , ('unfold-mut-recs . ',  6, 16, '10m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_12.sb.smt2'])
             , ('unfold-mut-recs . ', 12, 18, '60m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_13.sb.smt2'])
             ## these 3 tests should go through with this strategy, but they will need a very high
             ## time bound (>60m)
             # , ('unfold-mut-recs . ', 14, 20, '60m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_14.sb.smt2'])
             # , ('unfold-mut-recs . ', 16, 22, '60m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_15.sb.smt2'])
             # , ('unfold-mut-recs . ', 18, 24, '60m', ['t/SL-COMP18/bench/qf_shid_entl/ls_nonrec_entail_ls_16.sb.smt2'])
             , ('unfold-mut-recs . ',  2,  2, '20m', ['t/SL-COMP18/bench/qf_shid_entl/append_sll_cll_slk-1.smt2'])
             , ('unfold-mut-recs . ',  2,  2, '20m', ['t/SL-COMP18/bench/qf_shid_entl/append_sll_cll_slk-10.smt2'])
             , ('unfold-mut-recs . ',  5,  2, '20m', ['t/SL-COMP18/bench/qf_shid_entl/lsleftright_15.sb.smt2'])
             , ('unfold-mut-recs . ',  8,  9, '20m', ['t/SL-COMP18/bench/qf_shid_entl/eolseg_07.sb.smt2'])
             , ('unfold-mut-recs . ',  5,  2, '20m', ['t/SL-COMP18/bench/qf_shid_entl/lsleftright_14.sb.smt2'])
             , ('alternate',           3,  2, '10m', ['t/SL-COMP18/bench/qf_shid_entl/tll_slk-13.smt2'])
             , ('abstract . ',         3,  5, '10m', ['t/SL-COMP18/bench/qf_shid_entl/dll-rev-entails-dll.smt2'])
             , ('abstract . ',         3,  5, '10m', ['t/SL-COMP18/bench/qf_shid_entl/dll-entails-dll-rev.smt2'])
             , ('abstract . ',         3,  5, '10m', ['t/SL-COMP18/bench/qf_shid_entl/dll-entails-dll0+.smt2'])
             , ('abstract . ',         3,  5, '10m', ['t/SL-COMP18/bench/qf_shid_entl/dll_append_tail_entails_dllnull_nil.sb.smt2'])
             ]

qf_shid_entl_unsat_tests = read_list('t/test-lists/qf_shid_entl.unsat')

for (l1, l2) in combinations(test_lists, 2):
    (_, _, _, _, ts1) = l1
    (_, _, _, _, ts2) = l2
    assert (set(ts1) & set(ts2) == set()), set(ts1) & set(ts2)
