/*
 * Copyright (C) 2016 Jens Stimpfle <stimpflj@informatik.uni-freiburg.de>

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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;

enum Sat { OK, UNSATISFIABLE; };
enum Assign { NONE, TRUE, FALSE };

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
	/** the number of boolean variables */
	int numVars;

	/** the number of Horn clauses */
	int numClauses;

    /** the problem in CNF */
    private ArrayList<HornClause3> clauses;

    /** variable -> clauses in which it occurs */
    private final int[][] occur;

    /** variable -> assigned value */
    private Assign[] assign;

    /** last assignment operations */
    private ArrayList<Integer> op;

    public MaxSATSolve(ArrayList<HornClause3> clauses) {
        this.clauses = clauses;

        numVars = 0;
        for (HornClause3 c : clauses) {
        	assert 0 <= c.l0;
        	assert 0 <= c.l1;
        	assert 0 <= c.l2;
        	numVars = Math.max(numVars, c.l0 + 1);
        	numVars = Math.max(numVars, c.l1 + 1);
        	numVars = Math.max(numVars, c.l2 + 1);
        }

        occur = new int[numVars][];
        assign = new Assign[numVars];
        op = new ArrayList<Integer>();

        // so much work if you want the nice syntax of arrays vs ArrayLists...
        int[] numOcc = new int[numVars];
        for (HornClause3 x : clauses) {
			numOcc[x.l0]++;
			numOcc[x.l1]++;
			numOcc[x.l2]++;
        }
        for (int i = 0; i < numVars; i++) {
			occur[i] = new int[numOcc[i]];
			numOcc[i] = 0;
        }
        for (int i = 0; i < clauses.size(); i++) {
			occur[clauses.get(i).l0][numOcc[clauses.get(i).l0]++] = i;
			occur[clauses.get(i).l1][numOcc[clauses.get(i).l1]++] = i;
			occur[clauses.get(i).l2][numOcc[clauses.get(i).l2]++] = i;
        }

        for (int i = 0; i < numVars; i++)
			assign[i] = Assign.NONE;
        assign[HornClause3.trueVar] = Assign.TRUE;
        assign[HornClause3.falseVar] = Assign.FALSE;
    }

    private void setVar(int v, Assign a) {
        assert a != Assign.NONE;
        assert assign[v] == Assign.NONE;
        op.add(v);
        assign[v] = a;
    }

    private Sat check(HornClause3 c) {
        if (assign[c.l0] == Assign.TRUE &&
            assign[c.l1] == Assign.TRUE &&
            assign[c.l2] == Assign.FALSE)
            return Sat.UNSATISFIABLE;
        else if (assign[c.l0] == Assign.NONE &&
                 assign[c.l1] == Assign.TRUE &&
                 assign[c.l2] == Assign.FALSE)
            setVar(c.l0, Assign.FALSE);
        else if (assign[c.l0] == Assign.TRUE &&
                 assign[c.l1] == Assign.NONE &&
                 assign[c.l2] == Assign.FALSE)
            setVar(c.l1, Assign.FALSE);
        else if (assign[c.l0] == Assign.TRUE &&
                 assign[c.l1] == Assign.TRUE &&
                 assign[c.l2] == Assign.NONE)
            setVar(c.l2, Assign.TRUE);
        return Sat.OK;
    }

    private Sat propagate() {
        /* NOTE: the termination condition is "flexible" since the
         * loop body might insert new elements into `op' */
        for (int i = 0; i < op.size(); i++)
            for (int c : occur[op.get(i)])
                if (check(clauses.get(c)) == Sat.UNSATISFIABLE)
                    return Sat.UNSATISFIABLE;
        return Sat.OK;
    }

    private Sat setAndPropagate(int v, Assign a) {
        assert op.size() == 0;
        setVar(v, a);
        if (propagate() == Sat.UNSATISFIABLE) {
            /* rollback */
            for (int v2 : op)
                assign[v2] = Assign.NONE;
            op.clear();
            return Sat.UNSATISFIABLE;
        }
        op.clear();
        return Sat.OK;
    }

    /**
     * Solve the thing. Call only once, i.e.
     *
     * Assign assign[] = new MaxSATSolve(numVars, theclauses).solve()
     *
     * (Yes, this is a broken design. But I bet Java is happy to create
     * another object for you.)
     *
     * @return <code>null</code> if there is no solution, or an array
     * of assignments (Assign.TRUE or Assign.FALSE) for each variable.
     */
    public Assign[] solve() {
        assert op.size() == 0;
        for (HornClause3 c : clauses)
            if (check(c) == Sat.UNSATISFIABLE)
                return null;
        if (propagate() == Sat.UNSATISFIABLE)
            return null;
        op.clear();
        /* dumb chooser of next variable: iterate from beginning to end */
        for (int v = 0; v < numVars; v++)
            if (assign[v] == Assign.NONE)
                if (setAndPropagate(v, Assign.TRUE) == Sat.UNSATISFIABLE)
                    if (setAndPropagate(v, Assign.FALSE) == Sat.UNSATISFIABLE)
                        /* should not happen */
                        assert false;
        return assign;
    }


    // "test" the thing
    public static void main(String[] args) {
		PrintWriter writer = new PrintWriter(new OutputStreamWriter(System.err));

		ArrayList<HornClause3> clauses;
		Assign assign[];

		clauses = new ArrayList<HornClause3>();
		clauses.add(HornClause3.F(3));
		clauses.add(HornClause3.FT(2, 3));
		assign = new MaxSATSolve(clauses).solve();
		assert assign[2] == Assign.FALSE;
		assert assign[3] == Assign.FALSE;

		clauses = new ArrayList<HornClause3>();
		clauses.add(HornClause3.T(2));
		clauses.add(HornClause3.FT(2, 3));
		clauses.add(HornClause3.FFT(2, 3, 4));
		assign = new MaxSATSolve(clauses).solve();
		assert assign[2] == Assign.TRUE;
		assert assign[3] == Assign.TRUE;
		assert assign[4] == Assign.TRUE;

		clauses = new ArrayList<HornClause3>();
		clauses.add(HornClause3.T(2));
		clauses.add(HornClause3.FT(2, 3));
		clauses.add(HornClause3.FFT(2, 3, 4));
		clauses.add(HornClause3.F(4));
		assign = new MaxSATSolve(clauses).solve();
		assert assign == null;

		writer.printf("tests passed\n");
		writer.flush();
    }
}
