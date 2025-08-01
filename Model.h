#ifndef MODEL_H_INCLUDED
#define MODEL_H_INCLUDED

#include <algorithm>
#include <set>
#include <sstream>
#include <unordered_map>
#include <utility>
#include <vector>

#include "Core.hpp"
#include "Helpers.hpp"

extern "C" {
#include "aiger.h"
}

#include "Solver.h"
#include "SimpSolver.h"

// A simple wrapper around an AIGER-specified invariance benchmark.
// It specifically disallows primed variables beyond those required to
// express the (property-constrained) transition relation and the
// primed error constraint.  Variables are kept aligned with the
// variables of any solver created through newSolver().
class Model {
public: // types
    class SolverDecorator;

private: // types
    typedef std::unordered_map<std::size_t, std::size_t> IndexMap;

private: // fields
    std::vector<Var> vars_f;
    const std::size_t inputsOffset_f;
    const std::size_t latchesOffset_f;
    const std::size_t gatesOffset_f;
    const std::size_t primesOffset_f;

    bool primesUnlocked_f = true;
    IndexMap primedAnds_f;

    const std::vector<AigRow> andGates_f;
    const std::vector<Minisat::Lit> init_f;
    const std::vector<Minisat::Lit> constraints_f;
    const std::vector<Minisat::Lit> nextStateFns_f;
    const Minisat::Lit error_f;
    Minisat::Lit primedError_f;

    Minisat::Solver *inits_f = nullptr;
    Minisat::SimpSolver *simpleSolver_f = nullptr;

    std::set<Minisat::Lit> initLits_f;

public: // constructors
    // Construct a model from a vector of variables, indices indicating
    // divisions between variable types, constraints, next-state
    // functions, the error, and the AND table, closely reflecting the
    // AIGER format.  Easier to use "modelFromAiger()", below.
    Model(std::vector<Var> vars,
          std::size_t inputs, std::size_t latches, std::size_t reps,
          std::vector<Minisat::Lit> init, std::vector<Minisat::Lit> constraints,
          std::vector<Minisat::Lit> nextStateFns, Minisat::Lit err, std::vector<AigRow> andGates)
        : vars_f(vars),
          inputsOffset_f(inputs), latchesOffset_f(latches), gatesOffset_f(reps),
          primesOffset_f(vars.size()), andGates_f(andGates), init_f(init),
          constraints_f(constraints), nextStateFns_f(nextStateFns), error_f(err) {
        // create primed inputs and latches in known region of vars
        for (std::size_t i = this->inputsOffset_f; i < this->gatesOffset_f; ++i) {
            std::stringstream ss;
            ss << this->vars_f[i].name() << "'";
            this->vars_f.push_back(Var(ss.str()));
        }
        // same with primed error
        this->primedError_f = this->primeLit(this->error_f);
        // same with primed constraints
        for (const Minisat::Lit &lit: this->constraints_f) {
            this->primeLit(lit);
        }

        LOG("Model created with vars: %zu", this->vars_f.size());
        for (std::size_t i = 0; i < this->vars_f.size(); ++i) {
            const Var &var = this->vars_f[i];
            if (i == this->inputsOffset_f) {
                LOG("Inputs offset: %zu", this->inputsOffset_f);
            }
            if (i == this->latchesOffset_f) {
                LOG("Latches offset: %zu", this->latchesOffset_f);
            }
            if (i == this->gatesOffset_f) {
                LOG("Gates offset: %zu", this->gatesOffset_f);
            }
            if (i == this->primesOffset_f) {
                LOG("Primes offset: %zu", this->primesOffset_f);
            }
            LOG("Var: name: %s index: %zu", var.name().c_str(), var.index());
        }
        LOG("Model init: %zu", this->init_f.size());
        for (const Minisat::Lit &lit: this->init_f) {
            LOG("%s", this->stringOfLit(lit).c_str());
        }
        LOG("Model constraints: %zu", this->constraints_f.size());
        for (const Minisat::Lit &lit: this->constraints_f) {
            LOG("%s", this->stringOfLit(lit).c_str());
        }
        LOG("Model next state functions: %zu", this->nextStateFns_f.size());
        for (const Minisat::Lit &lit: this->nextStateFns_f) {
            LOG("%s", this->stringOfLit(lit).c_str());
        }
        LOG("Model error: %s", this->stringOfLit(this->error_f).c_str());
        LOG("Model primed error: %s", this->stringOfLit(this->primedError_f).c_str());
        LOG("-----------------------------------------------------------");
    }

    ~Model() {
        delete this->inits_f;
        delete this->simpleSolver_f;
    }

    // Returns the Var of the given Minisat::Lit
    const Var &
    varOfLit(const Minisat::Lit &lit) const {
        const auto v = static_cast<std::size_t>(Minisat::var(lit));
        ASSERT(v < this->vars_f.size(), "v: %zu, this->vars_f.size(): %zu", v, this->vars_f.size());
        return this->vars_f[v];
    }

    // Returns the name of the Minisat::Lit
    std::string
    stringOfLit(const Minisat::Lit &lit) const {
        std::stringstream ss;
        if (Minisat::sign(lit)) {
            ss << "~";
        }
        ss << this->varOfLit(lit).name();
        return ss.str();
    }

    // Returns the primed Var/Minisat::Lit for the given
    // Var/Minisat::Lit. Once lockPrimes() is called, primeVar() fails
    // (with an assertion violation) if it is asked to create a new
    // variable
    const Var &
    primeVar(const Var &v, Minisat::SimpSolver *slv = nullptr) {
        // var for false
        if (v.index() == 0) {
            return v;
        }
        // latch or PI
        if (v.index() < this->gatesOffset_f) {
            return this->vars_f[this->primesOffset_f + v.index() - this->inputsOffset_f];
        }
        // AND lit
        ASSERT(v.index() >= this->gatesOffset_f,
               "v.index(): %zu this->gatesOffset_f: %zu",
               v.index(), this->gatesOffset_f);
        ASSERT(v.index() < this->primesOffset_f,
               "v.index(): %zu this->primesOffset_f: %zu",
               v.index(), this->primesOffset_f);
        // created previously?
        IndexMap::const_iterator i = this->primedAnds_f.find(v.index());
        std::size_t index;
        if (i == this->primedAnds_f.end()) {
            // no, so make sure the model hasn't been locked
            ASSERT(this->primesUnlocked_f, "this->primesUnlocked_f: %s",
                   BOOL_TO_STRING(this->primesUnlocked_f));
            // create a primed version
            std::stringstream ss;
            ss << v.name() << "'";
            index = this->vars_f.size();
            this->vars_f.push_back(Var(ss.str()));
            if (slv != nullptr) {
                Minisat::Var newVar = slv->newVar();
                const Minisat::Var &backVar = this->vars_f.back().var();
                ASSERT(newVar == backVar, "newVar: %d backVar: %d",
                       newVar, backVar);
            }
            ASSERT(this->vars_f.back().index() == index,
                   "this->vars_f.back().index(): %zu index: %zu",
                   this->vars_f.back().index(), index);
            this->primedAnds_f.emplace(v.index(), index);
        } else {
            index = i->second;
        }
        return this->vars_f[index];
    }

    Minisat::Lit
    primeLit(Minisat::Lit lit, Minisat::SimpSolver *slv = nullptr) {
        const Var &pv = this->primeVar(this->varOfLit(lit), slv);
        return pv.lit(Minisat::sign(lit));
    }

    Minisat::Lit
    unprimeLit(Minisat::Lit lit) {
        auto i = (std::size_t) Minisat::var(lit);
        if (i >= this->primesOffset_f &&
            i < this->primesOffset_f + this->gatesOffset_f - this->inputsOffset_f) {
            return Minisat::mkLit((Minisat::Var) (i - this->primesOffset_f + this->inputsOffset_f),
                                  Minisat::sign(lit));
        }
        return lit;
    }

    // Once all primed variables have been created, it locks the Model
    // from creating any further ones.  Then Solver::newVar() may be
    // called safely
    //
    // WARNING: Do not call Solver::newVar() until lockPrimes() has been
    // called
    void
    lockPrimes() {
        this->primesUnlocked_f = false;
    }

    // Minisat::Lits corresponding to true/false.
    Minisat::Lit
    btrue() const {
        return Minisat::mkLit(this->vars_f[0].var(), true);
    }

    Minisat::Lit
    bfalse() const {
        return Minisat::mkLit(this->vars_f[0].var(), false);
    }

    std::vector<Var>::const_iterator
    beginInputs() const {
        return this->vars_f.begin() + this->inputsOffset_f;
    }

    std::vector<Var>::const_iterator
    endInputs() const {
        return this->vars_f.begin() + this->latchesOffset_f;
    }

    std::vector<Var>::const_iterator
    beginLatches() const {
        return this->vars_f.begin() + this->latchesOffset_f;
    }

    std::vector<Var>::const_iterator
    endLatches() const {
        return this->vars_f.begin() + this->gatesOffset_f;
    }

    // Next-state function for given latch
    Minisat::Lit
    nextStateOfLatch(const Var &latch) const {
        assert(latch.index() >= this->latchesOffset_f && latch.index() < this->gatesOffset_f);
        return this->nextStateFns_f[latch.index() - this->latchesOffset_f];
    }

    // Error and its primed form
    Minisat::Lit
    error() const {
        return this->error_f;
    }

    Minisat::Lit
    primedError() const {
        return this->primedError_f;
    }

    // Invariant constraints
    const std::vector<Minisat::Lit> &
    invariantConstraints() {
        return this->constraints_f;
    }

    class SolverDecorator {
    public: // types
        using Clause = std::vector<Minisat::Lit>;

    private: // fields
        const Model &model_f;
        std::string id_f;
        Minisat::Solver solver_f;
        std::vector<Clause> clauses_f;

    public: // constructors
        explicit
        SolverDecorator(const Model &model, std::string id)
            : model_f(model), id_f(std::move(id)) {
        }

        ~SolverDecorator() = default;

    public: // getters
        [[nodiscard]]
        Minisat::Solver &
        solver() {
            return this->solver_f;
        }

        [[nodiscard]]
        const std::vector<Clause> &
        clauses() const {
            return this->clauses_f;
        }

    public: // member functions
        Minisat::Var
        newVar() {
            Minisat::Var var = this->solver_f.newVar();
            LOG("Solver: %s, new var: %d", this->id_f.c_str(), var);
            return var;
        }

        void
        add_clause(const Clause &clause) {
            Minisat::vec<Minisat::Lit> vec;
            vector_to_minisat_vec(clause, vec);
            this->solver_f.addClause_(vec);
            LOG("Solver: %s, added clause: %s",
                this->id_f.c_str(),
                SolverDecorator::clause_to_string(this->model_f, clause).c_str());
            this->clauses_f.emplace_back(clause);
        }

        void
        add_clause(Minisat::vec<Minisat::Lit> &clause) {
            std::vector<Minisat::Lit> vector = minisat_vec_to_vector(clause);
            this->solver_f.addClause_(clause);
            LOG("Solver: %s, added clause: %s",
                this->id_f.c_str(),
                SolverDecorator::clause_to_string(this->model_f, vector).c_str());
            this->clauses_f.emplace_back(vector);
        }

        void
        add_clause(const Minisat::Lit &literals...) {
            const Clause clause{literals};
            this->add_clause(clause);
        }

        void
        add_gate(const AigRow &gate) {
            LOG("Solver: %s, adding gate to solver: %s = %s & %s",
                this->id_f.c_str(),
                this->model_f.stringOfLit(gate.lhs).c_str(),
                this->model_f.stringOfLit(gate.rhs0).c_str(),
                this->model_f.stringOfLit(gate.rhs1).c_str()
            );
            this->add_clause(~gate.lhs, gate.rhs0);
            this->add_clause(~gate.lhs, gate.rhs1);
            this->add_clause(~gate.rhs0, ~gate.rhs1, gate.lhs);
        }

        bool
        solve(const Clause &assumptions) {
            Minisat::vec<Minisat::Lit> vec;
            vector_to_minisat_vec(assumptions, vec);
            LOG("Solver: %s, solving with assumptions: %s",
                this->id_f.c_str(),
                SolverDecorator::clause_to_string(this->model_f, assumptions).c_str());
            const bool result = this->solver_f.solve(vec);
            LOG("Solver result: %s", BOOL_TO_STRING(result));
            return result;
        }

        bool
        solve(Minisat::vec<Minisat::Lit> &assumptions) {
            std::vector<Minisat::Lit> vector = minisat_vec_to_vector(assumptions);
            LOG("Solver: %s, solving with assumptions: %s",
                this->id_f.c_str(),
                SolverDecorator::clause_to_string(this->model_f, vector).c_str());
            const bool result = this->solver_f.solve(assumptions);
            LOG("Solver: %s, result: %s", this->id_f.c_str(), BOOL_TO_STRING(result));
            return result;
        }

        bool
        solve(const Minisat::Lit &literals...) {
            const Clause clause{literals};
            return this->solve(clause);
        }

        [[nodiscard]]
        std::string
        clauses_to_string() const {
            std::stringstream ss;
            for (std::size_t i = 0; i < this->clauses_f.size(); ++i) {
                const Clause &clause = this->clauses_f[i];
                ss << SolverDecorator::clause_to_string(this->model_f, clause);
                if (i != clause.size() - 1) {
                    ss << " & ";
                }
            }
            return ss.str();
        }

    public: // static functions
        [[nodiscard]]
        static
        std::string
        clause_to_string(const Model &model, const Clause &clause) {
            std::stringstream ss;
            ss << "(";
            for (std::size_t i = 0; i < clause.size(); ++i) {
                const Minisat::Lit &lit = clause[i];
                ss << model.stringOfLit(lit);
                if (i != clause.size() - 1) {
                    ss << " | ";
                }
            }
            ss << ")";
            return ss.str();
        }

        template<typename T>
        static
        void
        vector_to_minisat_vec(const std::vector<T> &vector, Minisat::vec<T> &dest) {
            dest.clear();
            dest.capacity(vector.size());
            for (const Minisat::Lit &lit: vector) {
                dest.push(lit);
            }
            const std::size_t destSize = dest.size();
            const std::size_t vectorSize = vector.size();
            ASSERT(destSize == vectorSize, "destSize: %zu vectorSize: %zu", destSize, vectorSize);
        }

        template<typename T>
        [[nodiscard]]
        static
        std::vector<T>
        minisat_vec_to_vector(const Minisat::vec<T> &vec) {
            std::vector<Minisat::Lit> vector;
            vector.reserve(vec.size());
            for (int i = 0; i < vec.size(); ++i) {
                const Minisat::Lit &lit = vec[i];
                vector.push_back(lit);
            }
            const std::size_t vectorSize = vector.size();
            const std::size_t vecSize = vec.size();
            ASSERT(vectorSize == vecSize, "vectorSize: %zu vecSize: %zu", vectorSize, vecSize);
            return vector;
        }
    };

    // Creates a Solver and initializes its variables to maintain
    // alignment with the Model's variables.
    Minisat::Solver *
    newSolver(const std::string &_) const {
        Minisat::Solver *solver = new Minisat::Solver();
        // load all variables to maintain alignment
        for (const Var &var: this->vars_f) {
            Minisat::Var newVar = solver->newVar();
            ASSERT(newVar == var.var(), "newVar: %d var.var(): %d", newVar, var.var());
        }
        return solver;
    }

    SolverDecorator *
    newSolverDecorator(const std::string &id) const {
        SolverDecorator *solver = new SolverDecorator(*this, id);
        LOG("New solver: %s", id.c_str());
        // load all variables to maintain alignment
        for (const Var &var: this->vars_f) {
            Minisat::Var newVar = solver->newVar();
            ASSERT(newVar == var.var(), "newVar: %d var.var(): %d", newVar, var.var());
        }
        return solver;
    }

    // Loads the TR into the solver.  Also loads the primed error
    // definition such that Model::primedError() need only be asserted
    // to activate it.  Invariant constraints (AIGER 1.9) and the
    // negation of the error are always added --- except that the primed
    // form of the invariant constraints are not asserted if
    // !primeConstraints.
    void
    loadTransitionRelation(Minisat::Solver &solver, bool primeConstraints) {
        LOG("Load transition relation into solver");
        if (!this->simpleSolver_f) {
            // create a simplified CNF version of (this slice of) the TR
            this->simpleSolver_f = new Minisat::SimpSolver();
            Minisat::SimpSolver &simpleSolver = *this->simpleSolver_f;

            // introduce all variables to maintain alignment
            for (std::size_t i = 0; i < this->vars_f.size(); ++i) {
                Minisat::Var newVar = simpleSolver.newVar();
                ASSERT(newVar == this->vars_f[i].var(), "");
            }

            // freeze inputs, latches, and special nodes (and primed forms)
            // This is why we use a SimpleSolver, to "freeze" variables

            // Freeze inputs and primed inputs
            for (auto iter = this->beginInputs(); iter != this->endInputs(); ++iter) {
                const Var &input = *iter;
                simpleSolver.setFrozen(input.var(), true);
                simpleSolver.setFrozen(this->primeVar(input).var(), true);
            }

            // Freeze latches and primed latches
            for (auto iter = this->beginLatches(); iter != this->endLatches(); ++iter) {
                const Var &latch = *iter;
                simpleSolver.setFrozen(latch.var(), true);
                simpleSolver.setFrozen(this->primeVar(latch).var(), true);
            }

            // Freeze safety property (output or bad) and its primed
            simpleSolver.setFrozen(this->varOfLit(this->error()).var(), true);
            simpleSolver.setFrozen(this->varOfLit(this->primedError()).var(), true);

            // Freeze constraints and primed constraints
            for (auto iter = this->constraints_f.begin(); iter != this->constraints_f.end(); ++
                 iter) {
                const Var &constraint = this->varOfLit(*iter);
                simpleSolver.setFrozen(constraint.var(), true);
                simpleSolver.setFrozen(this->primeVar(constraint).var(), true);
            }

            // initialize with roots of required formulas
            std::set<Minisat::Lit> require; // unprimed formulas
            for (auto iter = this->beginLatches(); iter != this->endLatches(); ++iter) {
                require.insert(this->nextStateOfLatch(*iter));
            }
            require.insert(this->error_f);
            require.insert(this->constraints_f.begin(), this->constraints_f.end());

            std::set<Minisat::Lit> prequire; // for primed formulas; always subset of require
            prequire.insert(this->error_f);
            prequire.insert(this->constraints_f.begin(), this->constraints_f.end());

            // traverse AIG backward
            for (auto iter = this->andGates_f.rbegin(); iter != this->andGates_f.rend(); ++iter) {
                const AigRow &gate = *iter;
                // skip if this row is not required
                if (!require.contains(gate.lhs) && !require.contains(~gate.lhs)) {
                    continue;
                }
                // encode into CNF
                LOG("Loading gate into solver: %s = %s & %s",
                    this->stringOfLit(gate.lhs).c_str(),
                    this->stringOfLit(gate.rhs0).c_str(),
                    this->stringOfLit(gate.rhs1).c_str()
                );
                simpleSolver.addClause(~gate.lhs, gate.rhs0);
                simpleSolver.addClause(~gate.lhs, gate.rhs1);
                simpleSolver.addClause(~gate.rhs0, ~gate.rhs1, gate.lhs);

                // require arguments
                require.insert(gate.rhs0);
                require.insert(gate.rhs1);

                // primed: skip if not required
                if (!prequire.contains(gate.lhs) && !prequire.contains(~gate.lhs)) {
                    continue;
                }

                // encode PRIMED form into CNF
                Minisat::Lit lhsPrime = this->primeLit(gate.lhs, this->simpleSolver_f);
                Minisat::Lit rhs0Prime = this->primeLit(gate.rhs0, this->simpleSolver_f);
                Minisat::Lit rhs1Prime = this->primeLit(gate.rhs1, this->simpleSolver_f);
                LOG("Loading gate into solver: %s = %s & %s",
                    this->stringOfLit(lhsPrime).c_str(),
                    this->stringOfLit(rhs0Prime).c_str(),
                    this->stringOfLit(rhs1Prime).c_str()
                );
                simpleSolver.addClause(~lhsPrime, rhs0Prime);
                simpleSolver.addClause(~lhsPrime, rhs1Prime);
                simpleSolver.addClause(~rhs0Prime, ~rhs1Prime, lhsPrime);

                // require arguments
                prequire.insert(gate.rhs0);
                prequire.insert(gate.rhs1);
            }

            // assert literal for true
            simpleSolver.addClause(this->btrue());
            // assert ~error, constraints, and primed constraints
            simpleSolver.addClause(~this->error_f);
            LOG("Adding constraints to solver");
            for (auto iter = this->constraints_f.begin(); iter != this->constraints_f.end(); ++
                 iter) {
                simpleSolver.addClause(*iter);
                // TODO 22-Jul-2025 18:01 @basshelal : Primed constraints aren't here,
                //  is this a bug by Bradley?
            }
            LOG("Adding primed latches and latch next states to solver");
            // assert l' = f for each latch l
            for (auto iter = this->beginLatches(); iter != this->endLatches(); ++iter) {
                const Var &latch = *iter;
                Minisat::Lit primedLatch = this->primeLit(latch.lit(false));
                Minisat::Lit latchNext = this->nextStateOfLatch(latch);
                simpleSolver.addClause(~primedLatch, latchNext);
                simpleSolver.addClause(~latchNext, primedLatch);
            }
            // turn off elimination (I don't know why)
            simpleSolver.eliminate(true);
        }

        Minisat::SimpSolver &simpleSolver = *this->simpleSolver_f;
        // load the clauses from the simplified context
        while (solver.nVars() < simpleSolver.nVars()) {
            solver.newVar();
        }
        for (auto iter = simpleSolver.clausesBegin(); iter != simpleSolver.clausesEnd(); ++iter) {
            const Minisat::Clause &clause = *iter;
            Minisat::vec<Minisat::Lit> literals;
            for (int i = 0; i < clause.size(); ++i) {
                const Minisat::Lit &lit = clause[i];
                literals.push(lit);
            }
            solver.addClause_(literals);
        }
        for (auto iter = simpleSolver.trailBegin(); iter != simpleSolver.trailEnd(); ++iter) {
            const Minisat::Lit &lit = *iter;
            solver.addClause(lit);
        }

        if (primeConstraints) {
            for (const Minisat::Lit &lit: this->constraints_f) {
                solver.addClause(this->primeLit(lit));
            }
        }
    }

    // Loads the initial condition into the solver.
    void
    loadInitialCondition(Minisat::Solver &solver) const {
        LOG("Load initial condition into solver");
        solver.addClause(this->btrue());
        for (const Minisat::Lit &lit: this->init_f) {
            solver.addClause(lit);
        }
        if (this->constraints_f.empty()) {
            return;
        }

        // impose invariant constraints on initial states (AIGER 1.9)
        std::set<Minisat::Lit> require;
        require.insert(this->constraints_f.begin(), this->constraints_f.end());
        for (auto iter = this->andGates_f.rbegin(); iter != this->andGates_f.rend(); ++iter) {
            const AigRow &gate = *iter;
            // skip if this (*i) is not required
            if (!require.contains(gate.lhs) && !require.contains(~gate.lhs)) {
                continue;
            }
            // solver.add_gate(gate);
            solver.addClause(~gate.lhs, gate.rhs0);
            solver.addClause(~gate.lhs, gate.rhs1);
            solver.addClause(~gate.rhs0, ~gate.rhs1, gate.lhs);
            // require arguments
            require.insert(gate.rhs0);
            require.insert(gate.rhs1);
        }
        for (auto iter = this->constraints_f.begin(); iter != this->constraints_f.end(); ++iter) {
            const Minisat::Lit &lit = *iter;
            solver.addClause(lit);
        }
    }

    // Loads the error into the solver, which is only necessary for the
    // 0-step base case of IC3.
    void
    loadError(Minisat::Solver &solver) const {
        LOG("Load safety property into solver");
        std::set<Minisat::Lit> require; // unprimed formulas
        require.insert(this->error_f);
        // traverse AIG backward
        for (auto iter = this->andGates_f.rbegin(); iter != this->andGates_f.rend(); ++iter) {
            const AigRow &gate = *iter;
            // skip if this row is not required
            if (!require.contains(gate.lhs) && !require.contains(~gate.lhs)) {
                continue;
            }
            // encode into CNF
            LOG("Loading gate into solver: %s = %s & %s",
                this->stringOfLit(gate.lhs).c_str(),
                this->stringOfLit(gate.rhs0).c_str(),
                this->stringOfLit(gate.rhs1).c_str()
            );
            solver.addClause(~gate.lhs, gate.rhs0);
            solver.addClause(~gate.lhs, gate.rhs1);
            solver.addClause(~gate.rhs0, ~gate.rhs1, gate.lhs);
            // require arguments
            require.insert(gate.rhs0);
            require.insert(gate.rhs1);
        }
    }

    // Use this method to allow the Model to decide how best to decide
    // if a cube has an initial state.
    bool
    isInitial(const std::vector<Minisat::Lit> &latches) {
        if (this->constraints_f.empty()) {
            // an intersection check (AIGER 1.9 w/o invariant constraints)
            if (this->initLits_f.empty()) {
                this->initLits_f.insert(this->init_f.begin(), this->init_f.end());
            }
            for (const Minisat::Lit &lit: latches) {
                if (this->initLits_f.contains(~lit)) {
                    return false;
                }
            }
            return true;
        }
        // a full SAT query
        if (this->inits_f == nullptr) {
            this->inits_f = this->newSolver("inits");
            this->loadInitialCondition(*this->inits_f);
        }
        Minisat::vec<Minisat::Lit> assumps;
        assumps.capacity(latches.size());
        for (const Minisat::Lit &lit: latches) {
            assumps.push(lit);
        }
        return this->inits_f->solve(assumps);
    }
};

// The easiest way to create a model
Model *
modelFromAiger(aiger *aig, unsigned int propertyIndex);

#endif
