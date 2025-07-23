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

namespace IC3 {
    class IC3 {
    private: // types

        // The State structures are for tracking trees of (lifted) CTIs.
        // Because States are created frequently, I want to avoid dynamic
        // memory management; instead their (de)allocation is handled via
        // a vector-based pool.
        struct State {
            std::size_t successor; // successor State
            LitVec latches;
            LitVec inputs;
            std::size_t index; // for pool
            bool used; // for pool
        };

        class LitVecComp {
        public:
            bool
            operator()(const LitVec &v1, const LitVec &v2) const {
                return _LitVecComp(v1, v2);
            }
        };

        typedef set<LitVec, LitVecComp> CubeSet;

        // A proof obligation.
        struct Obligation {
            std::size_t state; // Generalize this state...
            std::size_t level; // ... relative to this level.
            std::size_t depth; // Length of CTI suffix to error.

            Obligation(size_t st, size_t l, size_t d)
                : state(st), level(l), depth(d) {
            }
        };

        class ObligationComp {
        public:
            bool
            operator()(const Obligation &o1, const Obligation &o2) const {
                if (o1.level < o2.level) return true; // prefer lower levels (required)
                if (o1.level > o2.level) return false;
                if (o1.depth < o2.depth) return true; // prefer shallower (heuristic)
                if (o1.depth > o2.depth) return false;
                if (o1.state < o2.state) return true; // canonical final decider
                return false;
            }
        };

        typedef set<Obligation, ObligationComp> PriorityQueue;

        // For IC3's overall frame structure.
        struct Frame {
            std::size_t k; // steps from initial state
            CubeSet borderCubes; // additional cubes in this and previous frames
            Minisat::Solver *consecution;
        };

        // Structure and methods for imposing priorities on literals
        // through ordering the dropping of literals in mic (drop leftmost
        // literal first) and assumptions to Minisat.  The implemented
        // ordering prefers to keep literals that appear frequently in
        // addCube() calls.
        struct HeuristicLitOrder {
            std::vector<float> counts;
            std::size_t _mini;

            HeuristicLitOrder()
                : _mini(1 << 20) {
            }

            void
            count(const LitVec &cube) {
                assert(!cube.empty());
                // assumes cube is ordered
                size_t sz = (size_t) Minisat::toInt(Minisat::var(cube.back()));
                if (sz >= counts.size()) counts.resize(sz + 1);
                _mini = (size_t) Minisat::toInt(Minisat::var(cube[0]));
                for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
                    counts[(size_t) Minisat::toInt(Minisat::var(*i))] += 1;
            }

            void
            decay() {
                for (size_t i = _mini; i < counts.size(); ++i)
                    counts[i] *= 0.99;
            }
        };

        struct SlimLitOrder {
            HeuristicLitOrder *heuristicLitOrder;

            bool
            operator()(const Minisat::Lit &l1, const Minisat::Lit &l2) const {
                // l1, l2 must be unprimed
                std::size_t i2 = (std::size_t) Minisat::toInt(Minisat::var(l2));
                if (i2 >= heuristicLitOrder->counts.size()) return false;
                std::size_t i1 = (std::size_t) Minisat::toInt(Minisat::var(l1));
                if (i1 >= heuristicLitOrder->counts.size()) return true;
                return (heuristicLitOrder->counts[i1] < heuristicLitOrder->counts[i2]);
            }
        };

        typedef Minisat::vec<Minisat::Lit> MSLitVec;

    private: // fields
        int verbose_f = 0; // 0: silent, 1: stats, 2: all
        bool random_f = false;
        Model &model_f;
        std::size_t k_f = 1;
        vector<State> states_f;
        std::size_t nextState_f = 0;
        std::size_t maxDepth_f = 1;
        std::size_t maxCTGs_f = 3;
        std::size_t maxJoins_f = 1 << 20;
        std::size_t micAttempts_f = 3;

        vector<Frame> frames_f;

        Minisat::Solver *lifts_f;
        Minisat::Lit notInvConstraints_f;
        float numLits_f = 0;
        float numUpdates_f = 0;

        std::size_t cexState_f = 0; // beginning of counterexample trace
        bool trivial_f; // indicates whether strengthening was required
        // during major iteration
        int nQuery_f = 0;
        int nCTI_f = 0;
        int nCTG_f = 0;
        int nmic_f = 0;
        ::clock_t startTime_f;
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
            slimLitOrder_f.heuristicLitOrder = &litOrder_f;

            // construct lifting solver
            lifts_f = model_f.newSolver();
            // don't assert primed invariant constraints
            model_f.loadTransitionRelation(*lifts_f, false);
            // assert notInvConstraints (in stateOf) when lifting
            notInvConstraints_f = Minisat::mkLit(lifts_f->newVar());
            Minisat::vec<Minisat::Lit> cls;
            cls.push(~notInvConstraints_f);
            for (LitVec::const_iterator i = model_f.invariantConstraints().begin();
                 i != model_f.invariantConstraints().end(); ++i)
                cls.push(model_f.primeLit(~*i));
            lifts_f->addClause_(cls);
        }

        ~IC3() {
            for (vector<Frame>::const_iterator i = frames_f.begin();
                 i != frames_f.end(); ++i)
                if (i->consecution) delete i->consecution;
            delete lifts_f;
        }

        void
        printCurrentFrame() {
            REQUIRE(this->k_f < this->frames_f.size(), "k < frames.size() was false");
            // REQUIRE(this->nextState < this->states.size(),
            // "nextState < states.size() was false %zu, %zu", nextState, states.size());
            const Frame &currentFrame = this->frames_f.at(this->k_f);
            // const State& currentState = this->states.at(this->nextState);
            LOG("Current frame: k = %zu", this->k_f);
            for (const LitVec &cubes: currentFrame.borderCubes) {
                const std::string string = stringOfLitVec(cubes);
                LOG("%s", string.c_str());
            }
            // LOG("Current state index: %zu", currentState.index);
        }

        // The main loop.
        bool
        check() {
            this->startTime_f = this->time(); // stats
            while (true) {
                if (this->verbose_f > 1) {
                    LOG("Level %zu: ", this->k_f);
                }
                this->extend(); // push frontier frame
                if (!this->strengthen()) {
                    this->printCurrentFrame();
                    return false; // strengthen to remove bad successors
                }
                if (this->propagate()) {
                    this->printCurrentFrame();
                    return true; // propagate clauses; check for proof
                }
                this->printStats();
                this->k_f++; // increment frontier
            }
        }

        // Follows and prints chain of states from cexState forward.
        void
        printWitness() {
            if (cexState_f != 0) {
                size_t curr = cexState_f;
                while (curr) {
                    cout << stringOfLitVec(state(curr).inputs)
                            << stringOfLitVec(state(curr).latches) << endl;
                    curr = state(curr).successor;
                }
            }
        }

    private:
        std::string
        stringOfLitVec(const LitVec &vec) {
            stringstream ss;
            for (LitVec::const_iterator i = vec.begin(); i != vec.end(); ++i)
                ss << model_f.stringOfLit(*i) << " ";
            return ss.str();
        }

        // WARNING: do not keep reference across newState() calls
        State &
        state(size_t sti) {
            return states_f[sti - 1];
        }

        std::size_t
        newState() {
            if (nextState_f >= states_f.size()) {
                states_f.resize(states_f.size() + 1);
                states_f.back().index = states_f.size();
                states_f.back().used = false;
            }
            size_t ns = nextState_f;
            assert(!states_f[ns].used);
            states_f[ns].used = true;
            while (nextState_f < states_f.size() && states_f[nextState_f].used)
                nextState_f++;
            return ns + 1;
        }

        void
        delState(std::size_t sti) {
            State &st = state(sti);
            st.used = false;
            st.latches.clear();
            st.inputs.clear();
            if (nextState_f > st.index - 1) nextState_f = st.index - 1;
        }

        void
        resetStates() {
            for (std::vector<State>::iterator i = states_f.begin(); i != states_f.end(); ++i) {
                i->used = false;
                i->latches.clear();
                i->inputs.clear();
            }
            nextState_f = 0;
        }

        // A CubeSet is a set of ordered (by integer value) vectors of
        // Minisat::Lits.
        static
        bool
        _LitVecComp(const LitVec &v1, const LitVec &v2) {
            if (v1.size() < v2.size()) return true;
            if (v1.size() > v2.size()) return false;
            for (size_t i = 0; i < v1.size(); ++i) {
                if (v1[i] < v2[i]) return true;
                if (v2[i] < v1[i]) return false;
            }
            return false;
        }

        static
        bool
        _LitVecEq(const LitVec &v1, const LitVec &v2) {
            if (v1.size() != v2.size()) return false;
            for (size_t i = 0; i < v1.size(); ++i)
                if (v1[i] != v2[i]) return false;
            return true;
        }

        // Push a new Frame.
        void
        extend() {
            LOG("Extending frames");
            while (this->frames_f.size() < this->k_f + 2) {
                this->frames_f.resize(this->frames_f.size() + 1);
                Frame &frame = this->frames_f.back();
                frame.k = this->frames_f.size() - 1;
                frame.consecution = this->model_f.newSolver();
                LOG("Added Frame with index: %zu", frame.k);
                if (this->random_f) {
                    frame.consecution->random_seed = ::rand();
                    frame.consecution->rnd_init_act = true;
                }
                if (frame.k == 0) {
                    this->model_f.loadInitialCondition(*frame.consecution);
                }
                this->model_f.loadTransitionRelation(*frame.consecution);
            }
        }

        void
        updateLitOrder(const LitVec &cube, size_t level) {
            litOrder_f.decay();
            numUpdates_f += 1;
            numLits_f += cube.size();
            litOrder_f.count(cube);
        }

        // order according to preference
        void
        orderCube(LitVec &cube) {
            std::stable_sort(cube.begin(), cube.end(), slimLitOrder_f);
        }

        // Orders assumptions for Minisat.
        void
        orderAssumps(MSLitVec &cube, bool rev, int start = 0) {
            std::stable_sort(cube + start, cube + cube.size(), slimLitOrder_f);
            if (rev) std::reverse(cube + start, cube + cube.size());
        }

        // Assumes that last call to fr.consecution->solve() was
        // satisfiable.  Extracts state(s) cube from satisfying
        // assignment.
        std::size_t
        stateOf(Frame &fr, size_t succ = 0) {
            // create state
            size_t st = newState();
            state(st).successor = succ;
            MSLitVec assumps;
            assumps.capacity(1 + 2 * (model_f.endInputs() - model_f.beginInputs())
                             + (model_f.endLatches() - model_f.beginLatches()));
            Minisat::Lit act = Minisat::mkLit(lifts_f->newVar()); // activation literal
            assumps.push(act);
            Minisat::vec<Minisat::Lit> cls;
            cls.push(~act);
            cls.push(notInvConstraints_f); // successor must satisfy inv. constraint
            if (succ == 0)
                cls.push(~model_f.primedError());
            else
                for (LitVec::const_iterator i = state(succ).latches.begin();
                     i != state(succ).latches.end(); ++i)
                    cls.push(model_f.primeLit(~*i));
            lifts_f->addClause_(cls);
            // extract and assert primary inputs
            for (VarVec::const_iterator i = model_f.beginInputs();
                 i != model_f.endInputs(); ++i) {
                Minisat::lbool val = fr.consecution->modelValue(i->var());
                if (val != Minisat::l_Undef) {
                    Minisat::Lit pi = i->lit(val == Minisat::l_False);
                    state(st).inputs.push_back(pi); // record full inputs
                    assumps.push(pi);
                }
            }
            // some properties include inputs, so assert primed inputs after
            for (VarVec::const_iterator i = model_f.beginInputs();
                 i != model_f.endInputs(); ++i) {
                Minisat::lbool pval =
                        fr.consecution->modelValue(model_f.primeVar(*i).var());
                if (pval != Minisat::l_Undef)
                    assumps.push(model_f.primeLit(i->lit(pval == Minisat::l_False)));
            }
            int sz = assumps.size();
            // extract and assert latches
            LitVec latches;
            for (VarVec::const_iterator i = model_f.beginLatches();
                 i != model_f.endLatches(); ++i) {
                Minisat::lbool val = fr.consecution->modelValue(i->var());
                if (val != Minisat::l_Undef) {
                    Minisat::Lit la = i->lit(val == Minisat::l_False);
                    latches.push_back(la);
                    assumps.push(la);
                }
            }
            orderAssumps(assumps, false, sz); // empirically found to be best choice
            // State s, inputs i, transition relation T, successor t:
            //   s & i & T & ~t' is unsat
            // Core assumptions reveal a lifting of s.
            ++nQuery_f;
            startTimer(); // stats
            bool rv = lifts_f->solve(assumps);
            endTimer(satTime_f);
            assert(!rv);
            // obtain lifted latch set from unsat core
            for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i)
                if (lifts_f->conflict.has(~*i))
                    state(st).latches.push_back(*i); // record lifted latches
            // deactivate negation of successor
            lifts_f->releaseVar(~act);
            return st;
        }

        // Checks if cube contains any initial states.
        bool
        initiation(const LitVec &latches) {
            return !model_f.isInitial(latches);
        }

        // Check if ~latches is inductive relative to frame fi.  If it's
        // inductive and core is provided, extracts the unsat core.  If
        // it's not inductive and pred is provided, extracts
        // predecessor(s).
        bool
        consecution(size_t fi, const LitVec &latches, size_t succ = 0,
                    LitVec *core = NULL, size_t *pred = NULL,
                    bool orderedCore = false) {
            Frame &fr = frames_f[fi];
            MSLitVec assumps, cls;
            assumps.capacity(1 + latches.size());
            cls.capacity(1 + latches.size());
            Minisat::Lit act = Minisat::mkLit(fr.consecution->newVar());
            assumps.push(act);
            cls.push(~act);
            for (LitVec::const_iterator i = latches.begin();
                 i != latches.end(); ++i) {
                cls.push(~*i);
                assumps.push(*i); // push unprimed...
            }
            // ... order... (empirically found to best choice)
            if (pred) orderAssumps(assumps, false, 1);
            else orderAssumps(assumps, orderedCore, 1);
            // ... now prime
            for (int i = 1; i < assumps.size(); ++i)
                assumps[i] = model_f.primeLit(assumps[i]);
            fr.consecution->addClause_(cls);
            // F_fi & ~latches & T & latches'
            ++nQuery_f;
            startTimer(); // stats
            bool rv = fr.consecution->solve(assumps);
            endTimer(satTime_f);
            if (rv) {
                // fails: extract predecessor(s)
                if (pred) *pred = stateOf(fr, succ);
                fr.consecution->releaseVar(~act);
                return false;
            }
            // succeeds
            if (core) {
                if (pred && orderedCore) {
                    // redo with correctly ordered assumps
                    reverse(assumps + 1, assumps + assumps.size());
                    ++nQuery_f;
                    startTimer(); // stats
                    rv = fr.consecution->solve(assumps);
                    assert(!rv);
                    endTimer(satTime_f);
                }
                for (LitVec::const_iterator i = latches.begin();
                     i != latches.end(); ++i)
                    if (fr.consecution->conflict.has(~model_f.primeLit(*i)))
                        core->push_back(*i);
                if (!initiation(*core))
                    *core = latches;
            }
            fr.consecution->releaseVar(~act);
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
        ctgDown(size_t level, LitVec &cube, size_t keepTo, size_t recDepth) {
            size_t ctgs = 0, joins = 0;
            while (true) {
                // induction check
                if (!initiation(cube))
                    return false;
                if (recDepth > maxDepth_f) {
                    // quick check if recursion depth is exceeded
                    LitVec core;
                    bool rv = consecution(level, cube, 0, &core, NULL, true);
                    if (rv && core.size() < cube.size()) {
                        ++nCoreReduced_f; // stats
                        cube = core;
                    }
                    return rv;
                }
                // prepare to obtain CTG
                size_t cubeState = newState();
                state(cubeState).successor = 0;
                state(cubeState).latches = cube;
                size_t ctg;
                LitVec core;
                if (consecution(level, cube, cubeState, &core, &ctg, true)) {
                    if (core.size() < cube.size()) {
                        ++nCoreReduced_f; // stats
                        cube = core;
                    }
                    // inductive, so clean up
                    delState(cubeState);
                    return true;
                }
                // not inductive, address interfering CTG
                LitVec ctgCore;
                bool ret = false;
                if (ctgs < maxCTGs_f && level > 1 && initiation(state(ctg).latches)
                    && consecution(level - 1, state(ctg).latches, cubeState, &ctgCore)) {
                    // CTG is inductive relative to level-1; push forward and generalize
                    ++nCTG_f; // stats
                    ++ctgs;
                    size_t j = level;
                    // QUERY: generalize then push or vice versa?
                    while (j <= k_f && consecution(j, ctgCore)) ++j;
                    mic(j - 1, ctgCore, recDepth + 1);
                    addCube(j, ctgCore);
                } else if (joins < maxJoins_f) {
                    // ran out of CTG attempts, so join instead
                    ctgs = 0;
                    ++joins;
                    LitVec tmp;
                    for (size_t i = 0; i < cube.size(); ++i)
                        if (binary_search(state(ctg).latches.begin(),
                                          state(ctg).latches.end(), cube[i]))
                            tmp.push_back(cube[i]);
                        else if (i < keepTo) {
                            // previously failed when this literal was dropped
                            ++nAbortJoin_f; // stats
                            ret = true;
                            break;
                        }
                    cube = tmp; // enlarged cube
                } else
                    ret = true;
                // clean up
                delState(cubeState);
                delState(ctg);
                if (ret) return false;
            }
        }

        // Extracts minimal inductive (relative to level) subclause from
        // ~cube --- at least that's where the name comes from.  With
        // ctgDown, it's not quite a MIC anymore, but what's returned is
        // inductive relative to the possibly modifed level.
        void
        mic(size_t level, LitVec &cube, size_t recDepth) {
            ++nmic_f; // stats
            // try dropping each literal in turn
            size_t attempts = micAttempts_f;
            orderCube(cube);
            for (size_t i = 0; i < cube.size();) {
                LitVec cp(cube.begin(), cube.begin() + i);
                cp.insert(cp.end(), cube.begin() + i + 1, cube.end());
                if (ctgDown(level, cp, i, recDepth)) {
                    // maintain original order
                    LitSet lits(cp.begin(), cp.end());
                    LitVec tmp;
                    for (LitVec::const_iterator j = cube.begin(); j != cube.end(); ++j)
                        if (lits.find(*j) != lits.end())
                            tmp.push_back(*j);
                    cube.swap(tmp);
                    // reset attempts
                    attempts = micAttempts_f;
                } else {
                    if (!--attempts) {
                        // Limit number of attempts: if micAttempts literals in a
                        // row cannot be dropped, conclude that the cube is just
                        // about minimal.  Definitely improves mics/second to use
                        // a low micAttempts, but does it improve overall
                        // performance?
                        ++nAbortMic_f; // stats
                        return;
                    }
                    ++i;
                }
            }
        }

        // wrapper to start inductive generalization
        void
        mic(size_t level, LitVec &cube) {
            mic(level, cube, 1);
        }


        // Adds cube to frames at and below level, unless !toAll, in which
        // case only to level.
        void
        addCube(size_t level, LitVec &cube, bool toAll = true,
                bool silent = false) {
            sort(cube.begin(), cube.end());
            pair<CubeSet::iterator, bool> rv = frames_f[level].borderCubes.insert(cube);
            if (!rv.second) return;
            if (!silent && verbose_f > 1)
                cout << level << ": " << stringOfLitVec(cube) << endl;
            earliest_f = min(earliest_f, level);
            MSLitVec cls;
            cls.capacity(cube.size());
            for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
                cls.push(~*i);
            for (size_t i = toAll ? 1 : level; i <= level; ++i)
                frames_f[i].consecution->addClause(cls);
            if (toAll && !silent) updateLitOrder(cube, level);
        }

        // ~cube was found to be inductive relative to level; now see if
        // we can do better.
        std::size_t
        generalize(size_t level, LitVec cube) {
            // generalize
            mic(level, cube);
            // push
            do { ++level; } while (level <= k_f && consecution(level, cube));
            addCube(level, cube);
            return level;
        }

        // Process obligations according to priority.
        bool
        handleObligations(PriorityQueue obls) {
            while (!obls.empty()) {
                PriorityQueue::iterator obli = obls.begin();
                Obligation obl = *obli;
                LitVec core;
                size_t predi;
                // Is the obligation fulfilled?
                if (consecution(obl.level, state(obl.state).latches, obl.state,
                                &core, &predi)) {
                    // Yes, so generalize and possibly produce a new obligation
                    // at a higher level.
                    obls.erase(obli);
                    size_t n = generalize(obl.level, core);
                    if (n <= k_f)
                        obls.insert(Obligation(obl.state, n, obl.depth));
                } else if (obl.level == 0) {
                    // No, in fact an initial state is a predecessor.
                    cexState_f = predi;
                    return false;
                } else {
                    ++nCTI_f; // stats
                    // No, so focus on predecessor.
                    obls.insert(Obligation(predi, obl.level - 1, obl.depth + 1));
                }
            }
            return true;
        }

        // Strengthens frontier to remove error successors.
        bool
        strengthen() {
            LOG("Strengthening frontier frame");
            Frame &frontier = this->frames_f[this->k_f];
            this->trivial_f = true; // whether any cubes are generated
            this->earliest_f = this->k_f + 1; // earliest frame with enlarged borderCubes
            while (true) {
                ++this->nQuery_f;
                this->startTimer(); // stats
                bool rv = frontier.consecution->solve(this->model_f.primedError());
                this->endTimer(this->satTime_f);
                if (!rv) {
                    return true;
                }
                // handle CTI with error successor
                ++this->nCTI_f; // stats
                this->trivial_f = false;
                PriorityQueue pq;
                // enqueue main obligation and handle
                pq.insert(Obligation(stateOf(frontier), this->k_f - 1, 1));
                if (!this->handleObligations(pq)) {
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
            if (verbose_f > 1) cout << "propagate" << endl;
            // 1. clean up: remove c in frame i if c appears in frame j when i < j
            CubeSet all;
            for (size_t i = k_f + 1; i >= earliest_f; --i) {
                Frame &fr = frames_f[i];
                CubeSet rem, nall;
                set_difference(fr.borderCubes.begin(), fr.borderCubes.end(),
                               all.begin(), all.end(),
                               inserter(rem, rem.end()), LitVecComp());
                if (verbose_f > 1)
                    cout << i << " " << fr.borderCubes.size() << " " << rem.size() << " ";
                fr.borderCubes.swap(rem);
                set_union(rem.begin(), rem.end(),
                          all.begin(), all.end(),
                          inserter(nall, nall.end()), LitVecComp());
                all.swap(nall);
                for (CubeSet::const_iterator i = fr.borderCubes.begin();
                     i != fr.borderCubes.end(); ++i)
                    assert(all.find(*i) != all.end());
                if (verbose_f > 1)
                    cout << all.size() << endl;
            }
            // 2. check if each c in frame i can be pushed to frame j
            for (size_t i = trivial_f ? k_f : 1; i <= k_f; ++i) {
                int ckeep = 0, cprop = 0, cdrop = 0;
                Frame &fr = frames_f[i];
                for (CubeSet::iterator j = fr.borderCubes.begin();
                     j != fr.borderCubes.end();) {
                    LitVec core;
                    if (consecution(i, *j, 0, &core)) {
                        ++cprop;
                        // only add to frame i+1 unless the core is reduced
                        addCube(i + 1, core, core.size() < j->size(), true);
                        CubeSet::iterator tmp = j;
                        ++j;
                        fr.borderCubes.erase(tmp);
                    } else {
                        ++ckeep;
                        ++j;
                    }
                }
                if (verbose_f > 1)
                    cout << i << " " << ckeep << " " << cprop << " " << cdrop << endl;
                if (fr.borderCubes.empty())
                    return true;
            }
            // 3. simplify frames
            for (size_t i = trivial_f ? k_f : 1; i <= k_f + 1; ++i)
                frames_f[i].consecution->simplify();
            lifts_f->simplify();
            return false;
        }

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
            timer_f = time();
        }

        void
        endTimer(clock_t &t) {
            t += (time() - timer_f);
        }

        void
        printStats() {
            if (!verbose_f) return;
            clock_t etime = time();
            cout << ". Elapsed time: " << ((double) etime / sysconf(_SC_CLK_TCK)) << endl;
            etime -= startTime_f;
            if (!etime) etime = 1;
            cout << ". % SAT:        " << (int) (100 * (((double) satTime_f) / ((double) etime))) <<
                    endl;
            cout << ". K:            " << k_f << endl;
            cout << ". # Queries:    " << nQuery_f << endl;
            cout << ". # CTIs:       " << nCTI_f << endl;
            cout << ". # CTGs:       " << nCTG_f << endl;
            cout << ". # mic calls:  " << nmic_f << endl;
            cout << ". Queries/sec:  " << (int) (
                ((double) nQuery_f) / ((double) etime) * sysconf(_SC_CLK_TCK)) << endl;
            cout << ". Mics/sec:     " << (int) (
                ((double) nmic_f) / ((double) etime) * sysconf(_SC_CLK_TCK)) << endl;
            cout << ". # Red. cores: " << nCoreReduced_f << endl;
            cout << ". # Int. joins: " << nAbortJoin_f << endl;
            cout << ". # Int. mics:  " << nAbortMic_f << endl;
            if (numUpdates_f) cout << ". Avg lits/cls: " << numLits_f / numUpdates_f << endl;
        }

        friend bool check(Model &, int, bool, bool);
    };

    // IC3 does not check for 0-step and 1-step reachability, so do it
    // separately.
    bool
    baseCases(Model &model) {
        LOG("Checking base cases");
        LOG("Frame Index: 0 (InitialState =/> SafetyProperty)");
        Minisat::Solver *solver = model.newSolver();
        model.loadInitialCondition(*solver);
        model.loadError(*solver);
        Minisat::Lit property = model.error();
        LOG("Solving assuming (safety property): %s", model.stringOfLit(property).c_str());
        bool rv = solver->solve(property);
        LOG("Solver result: %s", BOOL_TO_STRING(rv));
        delete solver;
        if (rv) {
            LOG("InitialState was unsafe");
            return false;
        }

        solver = model.newSolver();
        LOG("Frame Index: 1 (InitialState & Transition =/> SafetyProperty)");
        model.loadInitialCondition(*solver);
        model.loadTransitionRelation(*solver);
        property = model.primedError();
        LOG("Solving assuming (safety property): %s", model.stringOfLit(property).c_str());
        rv = solver->solve(property);
        LOG("Solver result: %s", BOOL_TO_STRING(rv));
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
    check(Model &model, int verbose, bool basic, bool random) {
        if (!baseCases(model)) {
            return false;
        }
        LOG("Base cases safe, moving on to iteration");
        IC3 ic3(model);
        ic3.verbose_f = verbose;
        if (basic) {
            ic3.maxDepth_f = 0;
            ic3.maxJoins_f = 0;
            ic3.maxCTGs_f = 0;
        }
        if (random) {
            ic3.random_f = true;
        }
        bool rv = ic3.check();
        if (!rv && verbose > 1) {
            ic3.printWitness();
        }
        if (verbose) {
            ic3.printStats();
        }
        return rv;
    }
}
