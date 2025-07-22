#ifndef IC3_h_INCLUDED
#define IC3_h_INCLUDED

#include "Model.h"

namespace IC3 {
    bool check(Model &model,
               int verbose = 0, // 0: silent, 1: stats, 2: informative
               bool basic = false, // simple inductive generalization
               bool random = false); // random runs for statistical profiling
}

#endif
