/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>
 *
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat;

import java.util.ArrayList;

enum Sat { OK, UNSATISFIABLE; };

/**
 * Simple SAT solver.
 * Takes a set of Horn clauses. Goes through all variables in sequence, and
 * tries to set each to true.
 *
 * Note that we stick to the convention introduced in HornClause3.java:
 * the variables 0 and 1 are reserved for constant true and false,
 * respectively.
 *
 * @author stimpflj
 */
public class MaxSATSolve {
	public static final char NONE = 0;
	public static final char TRUE = 1;
	public static final char FALSE = 2;

    /** the number of boolean variables */
    int numVars;

    /** the problem in CNF */
    private ArrayList<HornClause3> clauses;

    /** variable -> clauses in which it occurs */
    private IntArray[] occur;

    /** variable -> assigned value (NONE, TRUE, FALSE) */
    private char[] assign;

    /** last assignment operations */
    private IntArray op;

    public MaxSATSolve(ArrayList<HornClause3> clauses) {
        this.clauses = clauses;

        numVars = 2; // const true and const false
        for (HornClause3 c : clauses) {
            assert 0 <= c.l0;
            assert 0 <= c.l1;
            assert 0 <= c.l2;
            numVars = Math.max(numVars, c.l0 + 1);
            numVars = Math.max(numVars, c.l1 + 1);
            numVars = Math.max(numVars, c.l2 + 1);
        }

        assign = new char[numVars];
        op = new IntArray();

        occur = new IntArray[numVars];
        for (int i = 0; i < numVars; i++)
        	occur[i] = new IntArray();

        for (int i = 0; i < clauses.size(); i++) {
            occur[clauses.get(i).l0].add(i);
            occur[clauses.get(i).l1].add(i);
            occur[clauses.get(i).l2].add(i);
        }

        for (int i = 0; i < numVars; i++)
            assign[i] = NONE;
        assign[HornClause3.trueVar] = TRUE;
        assign[HornClause3.falseVar] = FALSE;
    }

    private void setVar(int v, char a) {
        assert a != NONE;
        assert assign[v] == NONE;
        op.add(v);
        assign[v] = a;
    }

    private Sat check(HornClause3 c) {
        if (assign[c.l0] == TRUE &&
            assign[c.l1] == TRUE &&
            assign[c.l2] == FALSE)
            return Sat.UNSATISFIABLE;
        else if (assign[c.l0] == NONE &&
                 assign[c.l1] == TRUE &&
                 assign[c.l2] == FALSE)
            setVar(c.l0, FALSE);
        else if (assign[c.l0] == TRUE &&
                 assign[c.l1] == NONE &&
                 assign[c.l2] == FALSE)
            setVar(c.l1, FALSE);
        else if (assign[c.l0] == TRUE &&
                 assign[c.l1] == TRUE &&
                 assign[c.l2] == NONE)
            setVar(c.l2, TRUE);
        return Sat.OK;
    }

    private Sat propagate() {
        /* NOTE: the termination condition is "flexible" since the
         * loop body might insert new elements into `op' */
        for (int i = 0; i < op.size(); i++) {
            for (int c : occur[op.get(i)]) {
                if (check(clauses.get(c)) == Sat.UNSATISFIABLE) {
                    return Sat.UNSATISFIABLE;
                }
            }
        }
        return Sat.OK;
    }

    private Sat setAndPropagate(int v, char a) {
        assert op.size() == 0;
        setVar(v, a);
        if (propagate() == Sat.UNSATISFIABLE) {
            /* rollback */
            for (int v2 : op)
                assign[v2] = NONE;
            op.clear();
            return Sat.UNSATISFIABLE;
        }
        op.clear();
        return Sat.OK;
    }

    /**
     * Solve the thing. Call only once, i.e.
     *
     * char[] = new MaxSATSolve(numVars, theclauses).solve()
     *
     * (Yes, this is a broken design. But I bet Java is happy to create
     * another object for you.)
     *
     * @return <code>null</code> if there is no solution, or an array
     * of assignments (TRUE or FALSE) for each variable.
     */
    public char[] solve() {
        assert op.size() == 0;

        for (HornClause3 c : clauses)
            if (check(c) == Sat.UNSATISFIABLE)
                return null;
        if (propagate() == Sat.UNSATISFIABLE)
            return null;
        op.clear();

        for (int v = 0; v < numVars; v++) {
            if (assign[v] == NONE) {
                if (setAndPropagate(v, TRUE) == Sat.UNSATISFIABLE
                    && setAndPropagate(v, FALSE) == Sat.UNSATISFIABLE) {
                    /* should not happen */
                    assert false;
                }
            }
        }

        /* test */
        for (HornClause3 c : clauses) {
            assert assign[c.l0] == FALSE
                    || assign[c.l1] == FALSE
                    || assign[c.l2] == TRUE;
        }

        return assign;
    }


    // "test" the thing
    public static void main(String[] args) {
        char assign[];
        ArrayList<HornClause3> clauses;

        clauses = new ArrayList<HornClause3>();
        clauses.add(HornClause3.F(3));
        clauses.add(HornClause3.FT(2, 3));

        assign = new MaxSATSolve(clauses).solve();
        assert assign[2] == FALSE;
        assert assign[3] == FALSE;

        clauses = new ArrayList<HornClause3>();
        clauses.add(HornClause3.T(2));
        clauses.add(HornClause3.FT(2, 3));
        clauses.add(HornClause3.FFT(2, 3, 4));

        assign = new MaxSATSolve(clauses).solve();
        assert assign[2] == TRUE;
        assert assign[3] == TRUE;
        assert assign[4] == TRUE;

        clauses = new ArrayList<HornClause3>();
        clauses.add(HornClause3.T(2));
        clauses.add(HornClause3.FT(2, 3));
        clauses.add(HornClause3.FFT(2, 3, 4));
        clauses.add(HornClause3.F(4));

        assign = new MaxSATSolve(clauses).solve();
        assert assign == null;

        System.err.printf("tests passed\n");
    }
}
