#ifndef SOLVERDECORATOR_HPP
#define SOLVERDECORATOR_HPP

#include "Model.h"
#include "Solver.h"
#include "Vec.h"
#include <vector>

class SolverDecorator {
public: // types
    using Clause = std::vector<Minisat::Lit>;

private: // fields
    Model &model_f;
    Minisat::Solver solver_f;
    std::vector<Clause> clauses_f;

public: // constructors
    explicit
    SolverDecorator(Model &model)
        : model_f(model) {
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
    void
    add_clause(const Clause &clause) {
        Minisat::vec<Minisat::Lit> vec;
        for (const Minisat::Lit &element: clause) {
            vec.push(element);
        }
        const std::size_t vecSize = vec.size();
        const std::size_t clauseSize = clause.size();
        ASSERT(vecSize == clauseSize, "vecSize: %zu clauseSize: %zu", vecSize, clauseSize);

        this->solver_f.addClause_(vec);
        LOG("Added clause: %s", SolverDecorator::clause_to_string(this->model_f, clause).c_str());
        this->clauses_f.emplace_back(clause);
    }

    void
    add_clause(std::initializer_list<Minisat::Lit> literals...) {
        const Clause clause{literals};
        this->add_clause(clause);
    }

    void
    add_clause(const Minisat::Lit &literals...) {
        const Clause clause{literals};
        this->add_clause(clause);
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
        for (int i = 0; i < clause.size(); ++i) {
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
    [[nodiscard]]
    static
    Minisat::vec<T>
    vector_to_minisat_vec(const std::vector<T> &vector) {
        Minisat::vec<T> result(vector.size());
        ASSERT(result.capacity() == vector.size(), "");
        for (const T &element: vector) {
            result.push(element);
        }
        return result;
    }
};

#endif //SOLVERDECORATOR_HPP
