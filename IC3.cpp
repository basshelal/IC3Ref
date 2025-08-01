#include <algorithm>
#include <iostream>
#include <set>

#ifdef _WIN32
#include <ctime>
// Define a dummy sysconf for Windows (typically 100 clock ticks per second)
#define sysconf(x) 100
#else
#include <sys/times.h>
#endif // _WIN32

#include "IC3.h"
#include "Helpers.hpp"
#include "Solver.h"
#include "Vec.h"
#include "Core.hpp"

// A reference implementation of IC3, i.e., one that is meant to be
// read and used as a starting point for tuning, extending, and
// experimenting.
//
// High-level details:
//
//  o The overall structure described in
//
//      Aaron R. Bradley, "SAT-Based Model Checking without
//      Unrolling," VMCAI'11
//
//    including frames, a priority queue of frame-specific proof
//    obligations, and induction-based generalization.  See check(),
//    strengthen(), handleObligations(), mic(), propagate().
//
//  o Lifting, inspired by
//
//      Niklas Een, Alan Mishchenko, Robert Brayton, "Efficient
//      Implementation of Property Directed Reachability," FMCAD'11
//
//    Each CTI is lifted to a larger cube whose states all have the
//    same successor.  The implementation is based on
//
//      H. Chockler, A. Ivrii, A. Matsliah, S. Moran, and Z. Nevo,
//      "Incremental Formal Veriﬁcation of Hardware," FMCAD'11.
//
//    In particular, if s with inputs i is a predecessor of t, then s
//    & i & T & ~t' is unsatisfiable, where T is the transition
//    relation.  The unsat core reveals a suitable lifting of s.  See
//    stateOf().
//
//  o One solver per frame, which various authors of IC3
//    implementations have tried (including me in pre-publication
//    work, at which time I thought that moving to one solver was
//    better).
//
//  o A straightforward proof obligation scheme, inspired by the ABC
//    implementation.  I have so far favored generalizing relative to
//    the maximum possible level in order to avoid over-strengthening,
//    but doing so requires a more complicated generalization scheme.
//    Experiments by Zyad Hassan indicate that generalizing relative
//    to earlier levels works about as well.  Because literals seem to
//    be dropped more quickly, an implementation of the "up" algorithm
//    (described in my FMCAD'07 paper) is unnecessary.
//
//    The scheme is as follows.  For obligation <s, i>:
//
//    1. Check consecution of ~s relative to i-1.
//
//    2. If it succeeds, generalize, then push foward to, say, j.  If
//       j <= k (the frontier), enqueue obligation <s, j>.
//
//    3. If it fails, extract the predecessor t (using stateOf()) and
//       enqueue obligation <t, i-1>.
//
//    The upshot for this reference implementation is that it is
//    short, simple, and effective.  See handleObligations() and
//    generalize().
//
//  o The generalization method described in
//
//      Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
//      Generalization in IC3," (submitted May 2013)
//
//    which seems to be superior to the single-clause method described
//    in the original paper, first described in
//
//      Aaron R. Bradley and Zohar Manna, "Checking Safety by
//      Inductive Generalization of Counterexamples to Induction,"
//      FMCAD'07
//
//    The main idea is to address not only CTIs, which are states
//    discovered through IC3's explict backward search, but also
//    counterexamples to generalization (CTGs), which are states that
//    are counterexamples to induction during generalization.  See
//    mic() and ctgDown().
//
//    A basic one-cube generalization scheme can be used instead
//    (third argument of check()).
//
// Limitations in roughly descending order of significance:
//
//  o A permanent limitation is that there is absolutely no
//    simplification of the AIGER spec.  Use, e.g.,
//
//      iimc -t pp -t print_aiger 
//
//    or ABC's simplification methods to produce preprocessed AIGER
//    benchmarks.  This implementation is intentionally being kept
//    small and simple.
//
//  o An implementation of "up" is not provided, as it seems that it's
//    unnecessary when both lifting-based and unsat core-based
//    reduction are applied to a state, followed by mic before
//    pushing.  The resulting cube is sufficiently small.

// For IC3's overall frame structure.
struct Frame {
    std::size_t k_f; // steps from initial state
    CubeSet borderCubes_f; // additional cubes in this and previous frames
    Minisat::Solver *solver_f;
};

namespace IC3 {
    class IC3 {
    private: // fields
        bool verbose_f;
        Model &model_f;
        std::size_t k_f = 1;
        std::vector<State> states_f;
        std::size_t nextState_f = 0;
        std::size_t maxDepth_f = 1;
        std::size_t maxCTGs_f = 3;
        std::size_t maxJoins_f = 1 << 20;
        std::size_t micAttempts_f = 3;

        std::vector<Frame> frames_f;

        Minisat::Solver *lifts_f;
        Minisat::Lit notInvConstraints_f;
        float numLits_f = 0;
        float numUpdates_f = 0;

        std::size_t cexState_f = 0; // beginning of counterexample trace
        bool trivial_f = false;
        // indicates whether strengthening was required during major iteration
        int nQuery_f = 0;
        int nCTI_f = 0;
        int nCTG_f = 0;
        int nmic_f = 0;
        ::clock_t startTime_f = 0;
        ::clock_t satTime_f = 0;
        int nCoreReduced_f = 0;
        int nAbortJoin_f = 0;
        int nAbortMic_f = 0;
        ::clock_t timer_f;
        SlimLitOrder slimLitOrder_f;
        HeuristicLitOrder litOrder_f;
        std::size_t earliest_f; // track earliest modified level in a major iteration

    public:
        explicit
        IC3(Model &model)
            : model_f(model) {
            this->slimLitOrder_f.heuristicLitOrder = &this->litOrder_f;
            // construct lifting solver
            this->lifts_f = this->model_f.newSolver("lifts");
            // don't assert primed invariant constraints
            this->model_f.loadTransitionRelation(*this->lifts_f, false);
            // assert notInvConstraints (in stateOf) when lifting
            this->notInvConstraints_f = Minisat::mkLit(this->lifts_f->newVar());
            Minisat::vec<Minisat::Lit> cls;
            cls.push(~this->notInvConstraints_f);
            for (const Minisat::Lit &lit: this->model_f.invariantConstraints()) {
                cls.push(this->model_f.primeLit(~lit));
            }
            this->lifts_f->addClause_(cls);
        }

        ~IC3() {
            for (const auto &frame: this->frames_f) {
                delete frame.solver_f;
            }
            delete this->lifts_f;
        }

        void
        printCurrentFrame() {
            REQUIRE(this->k_f < this->frames_f.size(), "k < frames.size() was false");
            // REQUIRE(this->nextState < this->states.size(),
            // "nextState < states.size() was false %zu, %zu", nextState, states.size());
            const Frame &currentFrame = this->frames_f.at(this->k_f);
            // const State& currentState = this->states.at(this->nextState);
            LOG("Current frame: k = %zu", this->k_f);
            for (const std::vector<Minisat::Lit> &cubes: currentFrame.borderCubes_f) {
                const std::string string = stringOfLitVec(cubes);
                LOG("%s", string.c_str());
            }
            // LOG("Current state index: %zu", currentState.index);
        }

        // The main loop
        bool
        check() {
            this->startTime_f = this->time(); // stats
            while (true) {
                LOG("Level: %zu ", this->k_f);
                this->extendFrames(); // push frontier frame
                if (!this->strengthen()) {
                    // this->printCurrentFrame();
                    return false; // strengthen to remove bad successors
                }
                if (this->propagate()) {
                    // this->printCurrentFrame();
                    return true; // propagate clauses; check for proof
                }
                this->printStats();
                this->k_f++; // increment frontier
            }
        }

        // Follows and prints chain of states from cexState forward.
        void
        printWitness() {
            if (this->cexState_f != 0) {
                std::size_t curr = this->cexState_f;
                while (curr) {
                    const State &state = this->state(curr);
                    PRINT("%s%s", this->stringOfLitVec(state.inputs).c_str(),
                          this->stringOfLitVec(state.latches).c_str());
                    curr = state.successor;
                }
            }
        }

    private:
        std::string
        stringOfLitVec(const std::vector<Minisat::Lit> &literals) {
            std::stringstream ss;
            for (const Minisat::Lit &lit: literals) {
                ss << this->model_f.stringOfLit(lit) << " ";
            }
            return ss.str();
        }

        // WARNING: do not keep reference across newState() calls
        State &
        state(std::size_t sti) {
            return this->states_f[sti - 1];
        }

        std::size_t
        newState() {
            if (this->nextState_f >= this->states_f.size()) {
                this->states_f.resize(this->states_f.size() + 1);
                this->states_f.back().index = this->states_f.size();
                this->states_f.back().used = false;
            }
            std::size_t ns = this->nextState_f;
            assert(!this->states_f[ns].used);
            this->states_f[ns].used = true;
            while (this->nextState_f < this->states_f.size() &&
                   this->states_f[this->nextState_f].used) {
                this->nextState_f++;
            }
            return ns + 1;
        }

        void
        delState(std::size_t sti) {
            State &st = state(sti);
            st.used = false;
            st.latches.clear();
            st.inputs.clear();
            if (this->nextState_f > st.index - 1) {
                this->nextState_f = st.index - 1;
            }
        }

        void
        resetStates() {
            for (State &state: this->states_f) {
                state.used = false;
                state.latches.clear();
                state.inputs.clear();
            }
            this->nextState_f = 0;
        }

        void
        extendFrames() {
            const std::size_t newFramesSize = this->k_f + 2;
            LOG("Extending frames to %zu", newFramesSize);
            while (this->frames_f.size() < newFramesSize) {
                this->frames_f.resize(this->frames_f.size() + 1);
                Frame &frame = this->frames_f.back();
                frame.k_f = this->frames_f.size() - 1;
                std::stringstream solverName;
                solverName << "Frame " << frame.k_f;
                frame.solver_f = this->model_f.newSolver(solverName.str());
                LOG("Added Frame with index: %zu", frame.k_f);
                if (frame.k_f == 0) {
                    this->model_f.loadInitialCondition(*frame.solver_f);
                }
                this->model_f.loadTransitionRelation(*frame.solver_f, true);
            }
            LOG("Frames size: %zu", this->frames_f.size());
        }

        // Orders assumptions for Minisat
        void
        orderAssumptions(Minisat::vec<Minisat::Lit> &cube, bool reverse, int start) {
            std::stable_sort(cube + start, cube + cube.size(), this->slimLitOrder_f);
            if (reverse) {
                std::reverse(cube + start, cube + cube.size());
            }
        }

        // Assumes that last call to fr.consecution->solve() was
        // satisfiable.  Extracts state(s) cube from satisfying
        // assignment
        std::size_t
        stateOf(Frame &frame, std::size_t successor) {
            // create state
            std::size_t state = this->newState();
            this->state(state).successor = successor;
            Minisat::vec<Minisat::Lit> assumptions;
            assumptions.capacity(1 + 2 * (this->model_f.endInputs() - this->model_f.beginInputs())
                                 + (this->model_f.endLatches() - this->model_f.beginLatches())
            );
            Minisat::Lit act = Minisat::mkLit(this->lifts_f->newVar()); // activation literal
            assumptions.push(act);
            Minisat::vec<Minisat::Lit> cls;
            cls.push(~act);
            cls.push(this->notInvConstraints_f); // successor must satisfy inv. constraint
            if (successor == 0) {
                cls.push(~this->model_f.primedError());
            } else {
                for (const auto &lit: this->state(successor).latches) {
                    cls.push(this->model_f.primeLit(~lit));
                }
            }
            this->lifts_f->addClause_(cls);
            // extract and assert primary inputs
            for (auto it = this->model_f.beginInputs(); it != this->model_f.endInputs(); ++it) {
                Minisat::lbool val = frame.solver_f->modelValue(it->var());
                if (val != Minisat::l_Undef) {
                    Minisat::Lit pi = it->lit(val == Minisat::l_False);
                    this->state(state).inputs.push_back(pi); // record full inputs
                    assumptions.push(pi);
                }
            }
            // some properties include inputs, so assert primed inputs after
            for (auto it = model_f.beginInputs(); it != this->model_f.endInputs(); ++it) {
                Minisat::lbool pval =
                        frame.solver_f->modelValue(this->model_f.primeVar(*it).var());
                if (pval != Minisat::l_Undef) {
                    assumptions.push(this->model_f.primeLit(it->lit(pval == Minisat::l_False)));
                }
            }
            int sz = assumptions.size();
            // extract and assert latches
            std::vector<Minisat::Lit> latches;
            for (auto it = this->model_f.beginLatches(); it != this->model_f.endLatches(); ++it) {
                Minisat::lbool val = frame.solver_f->modelValue(it->var());
                if (val != Minisat::l_Undef) {
                    Minisat::Lit la = it->lit(val == Minisat::l_False);
                    latches.push_back(la);
                    assumptions.push(la);
                }
            }
            this->orderAssumptions(assumptions, false, sz); // empirically found to be best choice
            // State s, inputs i, transition relation T, successor t:
            //   s & i & T & ~t' is unsat
            // Core assumptions reveal a lifting of s.
            ++this->nQuery_f;
            this->startTimer(); // stats
            bool rv = this->lifts_f->solve(assumptions);
            this->endTimer(this->satTime_f);
            assert(!rv);
            // obtain lifted latch set from unsat core
            for (const Minisat::Lit &latch: latches) {
                if (this->lifts_f->conflict.has(~latch)) {
                    this->state(state).latches.push_back(latch); // record lifted latches
                }
            }
            // deactivate negation of successor
            this->lifts_f->releaseVar(~act);
            return state;
        }

        // Checks if cube contains any initial states.
        bool
        initiation(const std::vector<Minisat::Lit> &latches) {
            return !this->model_f.isInitial(latches);
        }

        // Check if ~latches is inductive relative to frame fi.  If it's
        // inductive and core is provided, extracts the unsat core.  If
        // it's not inductive and pred is provided, extracts
        // predecessor(s).
        bool
        consecution(std::size_t fi, const std::vector<Minisat::Lit> &latches, std::size_t succ = 0,
                    std::vector<Minisat::Lit> *core = nullptr, std::size_t *pred = nullptr,
                    bool orderedCore = false) {
            Frame &fr = this->frames_f[fi];
            Minisat::vec<Minisat::Lit> assumps;
            Minisat::vec<Minisat::Lit> cls;
            assumps.capacity(1 + latches.size());
            cls.capacity(1 + latches.size());
            Minisat::Lit act = Minisat::mkLit(fr.solver_f->newVar());
            assumps.push(act);
            cls.push(~act);
            for (const Minisat::Lit &latch: latches) {
                cls.push(~latch);
                assumps.push(latch); // push unprimed...
            }
            // ... order... (empirically found to best choice)
            if (pred != nullptr) {
                this->orderAssumptions(assumps, false, 1);
            } else {
                this->orderAssumptions(assumps, orderedCore, 1);
            }
            // ... now prime
            for (int i = 1; i < assumps.size(); ++i) {
                assumps[i] = this->model_f.primeLit(assumps[i]);
            }
            fr.solver_f->addClause_(cls);
            // F_fi & ~latches & T & latches'
            ++this->nQuery_f;
            this->startTimer(); // stats
            bool rv = fr.solver_f->solve(assumps);
            this->endTimer(this->satTime_f);
            if (rv) {
                // fails: extract predecessor(s)
                if (pred != nullptr) {
                    *pred = this->stateOf(fr, succ);
                }
                fr.solver_f->releaseVar(~act);
                return false;
            }
            // succeeds
            if (core != nullptr) {
                if (orderedCore && pred != nullptr) {
                    // redo with correctly ordered assumps
                    std::reverse(assumps + 1, assumps + assumps.size());
                    ++this->nQuery_f;
                    this->startTimer(); // stats
                    rv = fr.solver_f->solve(assumps);
                    assert(!rv);
                    this->endTimer(this->satTime_f);
                }
                for (const Minisat::Lit &latch: latches) {
                    if (fr.solver_f->conflict.has(~this->model_f.primeLit(latch))) {
                        core->push_back(latch);
                    }
                }
                if (!this->initiation(*core)) {
                    *core = latches;
                }
            }
            fr.solver_f->releaseVar(~act);
            return true;
        }

        // Based on
        //
        //   Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
        //   Generalization in IC3," (submitted May 2013)
        //
        // Improves upon "down" from the original paper (and the FMCAD'07
        // paper) by handling CTGs.
        bool
        ctgDown(std::size_t level, std::vector<Minisat::Lit> &cube, std::size_t keepTo,
                std::size_t recDepth) {
            std::size_t ctgs = 0;
            std::size_t joins = 0;
            while (true) {
                // induction check
                if (!this->initiation(cube)) {
                    return false;
                }
                if (recDepth > this->maxDepth_f) {
                    // quick check if recursion depth is exceeded
                    std::vector<Minisat::Lit> core;
                    bool rv = consecution(level, cube, 0, &core, nullptr, true);
                    if (rv && core.size() < cube.size()) {
                        ++this->nCoreReduced_f; // stats
                        cube = core;
                    }
                    return rv;
                }
                // prepare to obtain CTG
                std::size_t cubeState = newState();
                this->state(cubeState).successor = 0;
                this->state(cubeState).latches = cube;
                std::size_t ctg;
                std::vector<Minisat::Lit> core;
                if (this->consecution(level, cube, cubeState, &core, &ctg, true)) {
                    if (core.size() < cube.size()) {
                        ++this->nCoreReduced_f; // stats
                        cube = core;
                    }
                    // inductive, so clean up
                    this->delState(cubeState);
                    return true;
                }
                // not inductive, address interfering CTG
                std::vector<Minisat::Lit> ctgCore;
                bool ret = false;
                if (ctgs < this->maxCTGs_f && level > 1 && this->initiation(
                        this->state(ctg).latches)
                    && this->consecution(level - 1, this->state(ctg).latches, cubeState,
                                         &ctgCore)) {
                    // CTG is inductive relative to level-1; push forward and generalize
                    ++this->nCTG_f; // stats
                    ++ctgs;
                    std::size_t j = level;
                    // QUERY: generalize then push or vice versa?
                    while (j <= this->k_f && this->consecution(j, ctgCore)) {
                        ++j;
                    }
                    this->mic(j - 1, ctgCore, recDepth + 1);
                    this->addCube(j, ctgCore, true);
                } else if (joins < this->maxJoins_f) {
                    // ran out of CTG attempts, so join instead
                    ctgs = 0;
                    ++joins;
                    std::vector<Minisat::Lit> tmp;
                    for (std::size_t i = 0; i < cube.size(); ++i)
                        if (std::binary_search(this->state(ctg).latches.begin(),
                                               this->state(ctg).latches.end(), cube[i])) {
                            tmp.push_back(cube[i]);
                        } else if (i < keepTo) {
                            // previously failed when this literal was dropped
                            ++this->nAbortJoin_f; // stats
                            ret = true;
                            break;
                        }
                    cube = tmp; // enlarged cube
                } else {
                    ret = true;
                }
                // clean up
                this->delState(cubeState);
                this->delState(ctg);
                if (ret) {
                    return false;
                }
            }
        }

        // Extracts minimal inductive (relative to level) subclause from
        // ~cube --- at least that's where the name comes from.  With
        // ctgDown, it's not quite a MIC anymore, but what's returned is
        // inductive relative to the possibly modifed level.
        void
        mic(std::size_t level, std::vector<Minisat::Lit> &cube, std::size_t recDepth) {
            ++this->nmic_f; // stats
            // try dropping each literal in turn
            std::size_t attempts = this->micAttempts_f;
            std::stable_sort(cube.begin(), cube.end(), this->slimLitOrder_f);
            for (std::size_t i = 0; i < cube.size();) {
                std::vector<Minisat::Lit> cp(cube.begin(), cube.begin() + i);
                cp.insert(cp.end(), cube.begin() + i + 1, cube.end());
                if (this->ctgDown(level, cp, i, recDepth)) {
                    // maintain original order
                    std::set<Minisat::Lit> lits(cp.begin(), cp.end());
                    std::vector<Minisat::Lit> tmp;
                    for (auto j = cube.begin(); j != cube.end(); ++j) {
                        if (lits.find(*j) != lits.end()) {
                            tmp.push_back(*j);
                        }
                    }
                    cube.swap(tmp);
                    // reset attempts
                    attempts = this->micAttempts_f;
                } else {
                    if (!--attempts) {
                        // Limit number of attempts: if micAttempts literals in a
                        // row cannot be dropped, conclude that the cube is just
                        // about minimal.  Definitely improves mics/second to use
                        // a low micAttempts, but does it improve overall
                        // performance?
                        ++this->nAbortMic_f; // stats
                        return;
                    }
                    ++i;
                }
            }
        }

        // wrapper to start inductive generalization
        void
        mic(std::size_t level, std::vector<Minisat::Lit> &cube) {
            mic(level, cube, 1);
        }

        // Adds cube to frames at and below level, unless !toAll, in which
        // case only to level.
        void
        addCube(std::size_t level, std::vector<Minisat::Lit> &cube, bool toAll) {
            std::sort(cube.begin(), cube.end());
            std::pair<CubeSet::iterator, bool> rv = this->frames_f[level].borderCubes_f.insert(cube);
            if (!rv.second) {
                return;
            }
            if (this->verbose_f) {
                std::cout << level << ": " << this->stringOfLitVec(cube) << std::endl;
            }
            this->earliest_f = std::min(this->earliest_f, level);
            Minisat::vec<Minisat::Lit> cls;
            cls.capacity(cube.size());
            for (const Minisat::Lit &lit: cube) {
                cls.push(~lit);
            }
            for (std::size_t i = toAll ? 1 : level; i <= level; ++i) {
                this->frames_f[i].solver_f->addClause_(cls);
            }
            if (toAll) {
                this->litOrder_f.decay();
                this->numUpdates_f += 1;
                this->numLits_f += cube.size();
                this->litOrder_f.count(cube);
            }
        }

        // ~cube was found to be inductive relative to level; now see if
        // we can do better.
        std::size_t
        generalize(std::size_t level, std::vector<Minisat::Lit> &cube) {
            // generalize
            this->mic(level, cube);
            // push
            do {
                ++level;
            } while (level <= this->k_f && this->consecution(level, cube));
            this->addCube(level, cube, true);
            return level;
        }

        // Process obligations according to priority
        bool
        handleObligations(PriorityQueue &obligations) {
            while (!obligations.empty()) {
                PriorityQueue::iterator iter = obligations.begin();
                Obligation obligation = *iter;
                std::vector<Minisat::Lit> core;
                std::size_t predi;
                // Is the obligation fulfilled?
                if (this->consecution(obligation.level,
                                      this->state(obligation.state).latches, obligation.state,
                                      &core, &predi)) {
                    // Yes, so generalize and possibly produce a new obligation
                    // at a higher level.
                    obligations.erase(iter);
                    std::size_t n = this->generalize(obligation.level, core);
                    if (n <= this->k_f) {
                        obligations.insert(Obligation(obligation.state, n, obligation.depth));
                    }
                } else if (obligation.level == 0) {
                    // No, in fact an initial state is a predecessor.
                    this->cexState_f = predi;
                    return false;
                } else {
                    ++this->nCTI_f; // stats
                    // No, so focus on predecessor.
                    obligations.insert(
                        Obligation(predi, obligation.level - 1, obligation.depth + 1)
                    );
                }
            }
            return true;
        }

        // Strengthens frontier to remove error successors
        bool
        strengthen() {
            LOG("Strengthening frontier frame");
            Frame &frontier = this->frames_f[this->k_f];
            this->trivial_f = true; // whether any cubes are generated
            this->earliest_f = this->k_f + 1; // earliest frame with enlarged borderCubes

            while (true) {
                this->nQuery_f++;
                this->startTimer();
                const Minisat::Lit &property = this->model_f.primedError();
                LOG("Solving for frame at index: %zu assuming primed safety property: %s",
                    frontier.k_f, this->model_f.stringOfLit(property).c_str());
                bool rv = frontier.solver_f->solve(property);
                LOG("Solver result: %s", BOOL_TO_STRING(rv));
                this->endTimer(this->satTime_f);
                if (!rv) {
                    return true;
                }
                // handle CTI with error successor
                this->nCTI_f++;
                this->trivial_f = false;
                // TODO continue here! What is going on here and how does this relate
                //  to our understanding of the high level algorithm
                //  Also we really may need to create our own solver wrapper which stores all the
                //  clauses added to it so that we can print them and keep track of them nicely
                PriorityQueue queue;
                // enqueue main obligation and handle
                std::size_t state = this->stateOf(frontier, 0);
                Obligation mainObligation(state, this->k_f - 1, 1);
                queue.insert(mainObligation);
                if (!this->handleObligations(queue)) {
                    return false;
                }
                // finished with States for this iteration, so clean up
                this->resetStates();
            }
        }

        // Propagates clauses forward using induction.  If any frame has
        // all of its clauses propagated forward, then two frames' clause
        // sets agree; hence those clause sets are inductive
        // strengthenings of the property.  See the four invariants of IC3
        // in the original paper.
        bool
        propagate() {
            if (this->verbose_f) {
                std::cout << "propagate" << std::endl;
            }
            // 1. clean up: remove c in frame i if c appears in frame j when i < j
            CubeSet all;
            for (std::size_t i = this->k_f + 1; i >= this->earliest_f; --i) {
                Frame &fr = this->frames_f[i];
                CubeSet rem;
                CubeSet nall;
                std::set_difference(fr.borderCubes_f.begin(), fr.borderCubes_f.end(),
                                    all.begin(), all.end(),
                                    std::inserter(rem, rem.end()), LitVecComp());
                if (this->verbose_f) {
                    std::cout << i << " " << fr.borderCubes_f.size() << " " << rem.size() << " ";
                }
                fr.borderCubes_f.swap(rem);
                std::set_union(rem.begin(), rem.end(),
                               all.begin(), all.end(),
                               std::inserter(nall, nall.end()), LitVecComp());
                all.swap(nall);
                for (CubeSet::const_iterator i = fr.borderCubes_f.begin();
                     i != fr.borderCubes_f.end(); ++i) {
                    assert(all.find(*i) != all.end());
                }
                if (this->verbose_f)
                    std::cout << all.size() << std::endl;
            }
            // 2. check if each c in frame i can be pushed to frame j
            for (size_t i = this->trivial_f ? this->k_f : 1; i <= this->k_f; ++i) {
                int ckeep = 0;
                int cprop = 0;
                int cdrop = 0;
                Frame &fr = this->frames_f[i];
                for (CubeSet::iterator j = fr.borderCubes_f.begin(); j != fr.borderCubes_f.end();) {
                    std::vector<Minisat::Lit> core;
                    if (this->consecution(i, *j, 0, &core)) {
                        ++cprop;
                        // only add to frame i+1 unless the core is reduced
                        this->addCube(i + 1, core, core.size() < j->size());
                        CubeSet::iterator tmp = j;
                        ++j;
                        fr.borderCubes_f.erase(tmp);
                    } else {
                        ++ckeep;
                        ++j;
                    }
                }
                if (this->verbose_f) {
                    std::cout << i << " " << ckeep << " " << cprop << " " << cdrop << std::endl;
                }
                if (fr.borderCubes_f.empty()) {
                    return true;
                }
            }
            // 3. simplify frames
            for (size_t i = this->trivial_f ? this->k_f : 1; i <= this->k_f + 1; ++i) {
                this->frames_f[i].solver_f->simplify();
            }
            this->lifts_f->simplify();
            return false;
        }

        // TODO for time stuff just use C++ standard time tools

        ::clock_t
        time() {
#ifdef _WIN32
        return std::clock();
#else
            ::tms t{};
            ::times(&t);
            return t.tms_utime;
#endif // _WIN32
        }

        void
        startTimer() {
            this->timer_f = this->time();
        }

        void
        endTimer(clock_t &t) {
            t += (this->time() - this->timer_f);
        }

        void
        printStats() {
            if (!this->verbose_f) {
                return;
            }
            ::clock_t etime = this->time();
            std::cout << ". Elapsed time: " << ((double) etime / ::sysconf(_SC_CLK_TCK)) <<
                    std::endl;
            etime -= this->startTime_f;
            if (!etime) {
                etime = 1;
            }
            std::cout << ". % SAT:        " << (int) (
                        100 * (((double) this->satTime_f) / ((double) etime))) <<
                    std::endl;
            std::cout << ". K:            " << this->k_f << std::endl;
            std::cout << ". # Queries:    " << this->nQuery_f << std::endl;
            std::cout << ". # CTIs:       " << this->nCTI_f << std::endl;
            std::cout << ". # CTGs:       " << this->nCTG_f << std::endl;
            std::cout << ". # mic calls:  " << this->nmic_f << std::endl;
            std::cout << ". Queries/sec:  " << (int) (
                ((double) this->nQuery_f) / ((double) etime) * ::sysconf(_SC_CLK_TCK)) << std::endl;
            std::cout << ". Mics/sec:     " << (int) (
                ((double) this->nmic_f) / ((double) etime) * ::sysconf(_SC_CLK_TCK)) << std::endl;
            std::cout << ". # Red. cores: " << this->nCoreReduced_f << std::endl;
            std::cout << ". # Int. joins: " << this->nAbortJoin_f << std::endl;
            std::cout << ". # Int. mics:  " << this->nAbortMic_f << std::endl;
            if (this->numUpdates_f < 0) {
                std::cout << ". Avg lits/cls: " << this->numLits_f / this->numUpdates_f <<
                        std::endl;
            }
        }

        friend bool check(Model &model, bool verbose);
    };

    // IC3 does not check for 0-step and 1-step reachability, so do it
    // separately.
    bool
    baseCases(Model &model) {
        LOG("Checking base cases");
        LOG("Frame Index: 0 (InitialState =/> SafetyProperty)");
        Minisat::Solver *solver = model.newSolver("Step0");
        model.loadInitialCondition(*solver);
        model.loadError(*solver);
        Minisat::Lit property = model.error();
        bool rv = solver->solve(property);
        delete solver;
        if (rv) {
            LOG("InitialState was unsafe");
            return false;
        }

        solver = model.newSolver("Step1");
        LOG("Frame Index: 1 (InitialState & Transition =/> SafetyProperty)");
        model.loadInitialCondition(*solver);
        model.loadTransitionRelation(*solver, true);
        property = model.primedError();
        rv = solver->solve(property);
        delete solver;
        if (rv) {
            LOG("(InitialState & Transition) was unsafe");
            return false;
        }

        model.lockPrimes();

        return true;
    }

    // External function to make the magic happen.
    bool
    check(Model &model, bool verbose) {
        if (!baseCases(model)) {
            return false;
        }
        LOG("Base cases safe, moving on to iteration");
        IC3 ic3(model);
        ic3.verbose_f = verbose;
        bool rv = ic3.check();
        if (!rv && verbose) {
            ic3.printWitness();
        }
        if (verbose) {
            ic3.printStats();
        }
        return rv;
    }
}
