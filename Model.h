#ifndef MODEL_H_INCLUDED
#define MODEL_H_INCLUDED

#include <algorithm>
#include <set>
#include <sstream>
#include <unordered_map>
#include <utility>
#include <vector>

#include "Core.hpp"

extern "C" {
#include "aiger.h"
}

#include "Solver.h"
#include "SimpSolver.h"

// A row of the AIGER spec: lhs = rhs0 & rhs1.
struct AigRow {
    Minisat::Lit lhs;
    Minisat::Lit rhs0;
    Minisat::Lit rhs1;

    AigRow(Minisat::Lit _lhs, Minisat::Lit _rhs0, Minisat::Lit _rhs1)
        : lhs(_lhs), rhs0(_rhs0), rhs1(_rhs1) {
    }
};

// Intended to hold the AND section of an AIGER spec.
typedef std::vector<AigRow> AigVec;
typedef std::vector<Minisat::Lit> LitVec;

// A lightweight wrapper around Minisat::Var that includes a name.
class Var {
private: // fields
    Minisat::Var _var; // corresponding Minisat::Var in *any* solver
    std::string _name;

private: // static fields
    static
    Minisat::Var gvi; // aligned with solvers
public:
    explicit
    Var(std::string name)
        : _var(Var::gvi++),
          _name(std::move(name)) {
    }

    [[nodiscard]]
    std::size_t
    index() const {
        return (std::size_t) this->_var;
    }

    [[nodiscard]]
    Minisat::Var
    var() const {
        return this->_var;
    }

    [[nodiscard]]
    Minisat::Lit
    lit(bool neg) const {
        return Minisat::mkLit(this->_var, neg);
    }

    [[nodiscard]]
    std::string
    name() const {
        return this->_name;
    }
};

typedef std::vector<Var> VarVec;

class VarComp {
public:
    bool operator()(const Var &v1, const Var &v2) {
        return v1.index() < v2.index();
    }
};

typedef std::set<Var, VarComp> VarSet;
typedef std::set<Minisat::Lit> LitSet;

// A simple wrapper around an AIGER-specified invariance benchmark.
// It specifically disallows primed variables beyond those required to
// express the (property-constrained) transition relation and the
// primed error constraint.  Variables are kept aligned with the
// variables of any solver created through newSolver().
class Model {
private: // fields
    VarVec vars;
    const std::size_t inputs;
    const std::size_t latches;
    const std::size_t reps;
    const std::size_t primes;

    bool primesUnlocked;
    typedef std::unordered_map<std::size_t, std::size_t> IndexMap;
    IndexMap primedAnds;

    const AigVec aig;
    const LitVec init, constraints, nextStateFns;
    const Minisat::Lit _error;
    Minisat::Lit _primedError;

    typedef std::size_t TRMapKey;
    typedef std::unordered_map<TRMapKey, Minisat::SimpSolver *> TRMap;
    TRMap trmap;

    Minisat::Solver *inits;
    LitSet initLits;

    Minisat::SimpSolver *sslv;

public: // constructors
    // Construct a model from a vector of variables, indices indicating
    // divisions between variable types, constraints, next-state
    // functions, the error, and the AND table, closely reflecting the
    // AIGER format.  Easier to use "modelFromAiger()", below.
    Model(std::vector<Var> _vars,
          std::size_t _inputs, std::size_t _latches, std::size_t _reps,
          LitVec _init, LitVec _constraints, LitVec _nextStateFns,
          Minisat::Lit _err, AigVec _aig)
        : vars(_vars),
          inputs(_inputs), latches(_latches), reps(_reps),
          primes(_vars.size()), primesUnlocked(true), aig(_aig),
          init(_init), constraints(_constraints), nextStateFns(_nextStateFns),
          _error(_err), inits(NULL), sslv(NULL) {
        // create primed inputs and latches in known region of vars
        for (std::size_t i = inputs; i < reps; ++i) {
            std::stringstream ss;
            ss << vars[i].name() << "'";
            vars.push_back(Var(ss.str()));
        }
        // same with primed error
        _primedError = primeLit(_error);
        // same with primed constraints
        for (LitVec::const_iterator i = constraints.begin();
             i != constraints.end(); ++i)
            primeLit(*i);
    }

    ~Model() {
        delete this->inits;
        delete this->sslv;
    }

    // Returns the Var of the given Minisat::Lit.
    const Var &
    varOfLit(Minisat::Lit lit) const {
        const auto v = static_cast<std::size_t>(Minisat::var(lit));
        ASSERT(v < this->vars.size(), "");
        return this->vars[v];
    }

    // Returns the name of the Minisat::Lit.
    std::string
    stringOfLit(Minisat::Lit lit) const {
        std::stringstream ss;
        if (Minisat::sign(lit)) {
            ss << "~";
        }
        ss << this->varOfLit(lit).name();
        return ss.str();
    }

    // Returns the primed Var/Minisat::Lit for the given
    // Var/Minisat::Lit.  Once lockPrimes() is called, primeVar() fails
    // (with an assertion violation) if it is asked to create a new
    // variable.
    const Var &
    primeVar(const Var &v, Minisat::SimpSolver *slv = nullptr);

    Minisat::Lit
    primeLit(Minisat::Lit lit, Minisat::SimpSolver *slv = nullptr) {
        const Var &pv = this->primeVar(this->varOfLit(lit), slv);
        return pv.lit(Minisat::sign(lit));
    }

    Minisat::Lit
    unprimeLit(Minisat::Lit lit) {
        std::size_t i = (std::size_t) var(lit);
        if (i >= primes && i < primes + reps - inputs)
            return Minisat::mkLit((Minisat::Var) (i - primes + inputs), sign(lit));
        else
            return lit;
    }

    // Once all primed variables have been created, it locks the Model
    // from creating any further ones.  Then Solver::newVar() may be
    // called safely.
    //
    // WARNING: Do not call Solver::newVar() until lockPrimes() has been
    // called.
    void
    lockPrimes() {
        this->primesUnlocked = false;
    }

    // Minisat::Lits corresponding to true/false.
    Minisat::Lit
    btrue() const {
        return Minisat::mkLit(this->vars[0].var(), true);
    }

    Minisat::Lit
    bfalse() const {
        return Minisat::mkLit(this->vars[0].var(), false);
    }

    // Primary inputs.
    VarVec::const_iterator
    beginInputs() const {
        return this->vars.begin() + this->inputs;
    }

    VarVec::const_iterator
    endInputs() const {
        return this->vars.begin() + this->latches;
    }

    // Latches.
    VarVec::const_iterator
    beginLatches() const {
        return this->vars.begin() + this->latches;
    }

    VarVec::const_iterator
    endLatches() const {
        return this->vars.begin() + this->reps;
    }

    // Next-state function for given latch.
    Minisat::Lit
    nextStateFn(const Var &latch) const {
        assert(latch.index() >= latches && latch.index() < reps);
        return nextStateFns[latch.index() - latches];
    }

    // Error and its primed form.
    Minisat::Lit
    error() const {
        return _error;
    }

    Minisat::Lit
    primedError() const {
        return _primedError;
    }

    // Invariant constraints
    const LitVec &
    invariantConstraints() {
        return constraints;
    }

    void
    addClause1(Minisat::Solver &solver,
               const Minisat::Lit &lit0) const {
        LOG("Added clause: (%s)",
            this->stringOfLit(lit0).c_str()
        );
        solver.addClause(lit0);
    }

    void
    addClause1(Minisat::SimpSolver &solver,
               const Minisat::Lit &lit0) const {
        LOG("Added clause: (%s)",
            this->stringOfLit(lit0).c_str()
        );
        solver.addClause(lit0);
    }

    void
    addClause2(Minisat::Solver &solver,
               const Minisat::Lit &lit0, const Minisat::Lit &lit1) const {
        LOG("Added clause: (%s | %s)",
            this->stringOfLit(lit0).c_str(),
            this->stringOfLit(lit1).c_str()
        );
        solver.addClause(lit0, lit1);
    }

    void
    addClause2(Minisat::SimpSolver &solver,
               const Minisat::Lit &lit0, const Minisat::Lit &lit1) const {
        LOG("Added clause: (%s | %s)",
            this->stringOfLit(lit0).c_str(),
            this->stringOfLit(lit1).c_str()
        );
        solver.addClause(lit0, lit1);
    }

    void
    addClause3(Minisat::Solver &solver,
               const Minisat::Lit &lit0, const Minisat::Lit &lit1, const Minisat::Lit &lit2) const {
        LOG("Added clause: (%s | %s | %s)",
            this->stringOfLit(lit0).c_str(),
            this->stringOfLit(lit1).c_str(),
            this->stringOfLit(lit2).c_str()
        );
        solver.addClause(lit0, lit1, lit2);
    }

    void
    addClause3(Minisat::SimpSolver &solver,
               const Minisat::Lit &lit0, const Minisat::Lit &lit1, const Minisat::Lit &lit2) const {
        LOG("Added clause: (%s | %s | %s)",
            this->stringOfLit(lit0).c_str(),
            this->stringOfLit(lit1).c_str(),
            this->stringOfLit(lit2).c_str()
        );
        solver.addClause(lit0, lit1, lit2);
    }

    void
    addClauseVec(Minisat::Solver &solver, Minisat::vec<Minisat::Lit> &literals) const {
        std::stringstream ss;
        ss << "Added clause: (";
        for (auto i = 0; i < literals.size(); ++i) {
            const Minisat::Lit lit = literals[i];
            ss << this->stringOfLit(lit);
            if (i != literals.size() - 1) {
                ss << " | ";
            }
        }
        ss << ")";
        LOG("%s", ss.str().c_str());
        solver.addClause_(literals);
    }

    void
    addClauseVec(Minisat::SimpSolver &solver, Minisat::vec<Minisat::Lit> &literals) const {
        std::stringstream ss;
        ss << "Added clause: (";
        for (auto i = 0; i < literals.size(); ++i) {
            const Minisat::Lit lit = literals[i];
            ss << this->stringOfLit(lit);
            if (i != literals.size() - 1) {
                ss << " | ";
            }
        }
        ss << ")";
        LOG("%s", ss.str().c_str());
        solver.addClause_(literals);
    }

    // Creates a Solver and initializes its variables to maintain
    // alignment with the Model's variables.
    Minisat::Solver *
    newSolver() const {
        Minisat::Solver *solver = new Minisat::Solver();
        // load all variables to maintain alignment
        for (const Var &var: this->vars) {
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
    loadTransitionRelation(Minisat::Solver &solver, bool primeConstraints = true);

    // Loads the initial condition into the solver.
    void
    loadInitialCondition(Minisat::Solver &solver) const;

    // Loads the error into the solver, which is only necessary for the
    // 0-step base case of IC3.
    void
    loadError(Minisat::Solver &solver) const {
        LOG("Load safety property into solver");
        LitSet require; // unprimed formulas
        require.insert(this->_error);
        // traverse AIG backward
        for (auto iter = this->aig.rbegin(); iter != this->aig.rend(); ++iter) {
            const auto &gate = *iter;
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
            this->addClause2(solver, ~gate.lhs, gate.rhs0);
            this->addClause2(solver, ~gate.lhs, gate.rhs1);
            this->addClause3(solver, ~gate.rhs0, ~gate.rhs1, gate.lhs);
            // require arguments
            require.insert(gate.rhs0);
            require.insert(gate.rhs1);
        }
    }

    // Use this method to allow the Model to decide how best to decide
    // if a cube has an initial state.
    bool
    isInitial(const LitVec &latches) {
        if (this->constraints.empty()) {
            // an intersection check (AIGER 1.9 w/o invariant constraints)
            if (this->initLits.empty()) {
                this->initLits.insert(this->init.begin(), this->init.end());
            }
            for (const Minisat::Lit &lit: latches) {
                if (this->initLits.contains(~lit)) {
                    return false;
                }
            }
            return true;
        }
        // a full SAT query
        if (this->inits == nullptr) {
            this->inits = this->newSolver();
            this->loadInitialCondition(*this->inits);
        }
        Minisat::vec<Minisat::Lit> assumps;
        assumps.capacity(latches.size());
        for (const Minisat::Lit &lit: latches) {
            assumps.push(lit);
        }
        return this->inits->solve(assumps);
    }
};

// The easiest way to create a model.
Model *modelFromAiger(aiger *aig, unsigned int propertyIndex);

#endif
