# TODO

Minisat always simplifies when we add clauses to the solver, so we can't just add and then query 
what clauses it has and expect it to return the same ones to us, if we _really_ want to see what 
clauses were added the moment before solving for example `clauses: [...]` we need to store them 
manually which means writing our own solver which has an instance/reference of the minisat 
solver inside it (as a field), this is complicated so leave it for later