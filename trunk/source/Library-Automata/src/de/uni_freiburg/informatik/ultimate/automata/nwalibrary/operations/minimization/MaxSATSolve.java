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

enum Sat { OK, UNSATISFIABLE; };
enum Assign { NONE, TRUE, FALSE };

/**
 * Stupid SAT solver.
 * Takes a set of Horn clauses. Goes through all variables in sequence, and
 * tries to set each to true.
 *
 * @author stimpflj
 */
public class MaxSATSolve {
	/* this convention is setup by HornClause3 */
    static final int falseVar = 0;
    static final int trueVar = 1;

    /** the problem in CNF */
    private HornClause3[] clause;

    /** variable -> clauses in which it occurs */
    private final int[][] occur;

    /** variable -> assigned value */
    private Assign[] assigned;

    /** last assignment operations */
    private ArrayList<Integer> op;

    public MaxSATSolve(int nvars, HornClause3[] theclause) {
        clause = theclause;
        occur = new int[nvars][];
        assigned = new Assign[nvars];
        op = new ArrayList<Integer>(0);

        for (HornClause3 c : clause) {
            assert 0 <= c.l0 && c.l0 < nvars;
            assert 0 <= c.l1 && c.l1 < nvars;
			assert 0 <= c.l2 && c.l2 < nvars;
        }

        // so much work if you want the nice syntax of arrays vs ArrayLists...
        int[] numOcc = new int[nvars];
        for (int i = 0; i < clause.length; i++) {
			numOcc[clause[i].l0]++;
			numOcc[clause[i].l1]++;
			numOcc[clause[i].l2]++;
        }
        for (int i = 0; i < nvars; i++) {
			occur[i] = new int[numOcc[i]];
			numOcc[i] = 0;
        }
        for (int i = 0; i < clause.length; i++) {
			occur[clause[i].l0][numOcc[clause[i].l0]++] = i;
			occur[clause[i].l1][numOcc[clause[i].l1]++] = i;
			occur[clause[i].l2][numOcc[clause[i].l2]++] = i;
        }

        for (int i = 0; i < nvars; i++)
			assigned[i] = Assign.NONE;
        assigned[trueVar] = Assign.TRUE;
        assigned[falseVar] = Assign.FALSE;
    }

    private void setVar(int v, Assign a) {
        assert(a != Assign.NONE);
        assert(assigned[v] == Assign.NONE);
        op.add(v);
        assigned[v] = a;
    }

    private Sat check(HornClause3 c) {
        if (assigned[c.l0] == Assign.TRUE &&
            assigned[c.l1] == Assign.TRUE &&
            assigned[c.l2] == Assign.FALSE)
            return Sat.UNSATISFIABLE;
        else if (assigned[c.l0] == Assign.NONE &&
                 assigned[c.l1] == Assign.TRUE &&
                 assigned[c.l2] == Assign.FALSE)
            setVar(c.l0, Assign.FALSE);
        else if (assigned[c.l0] == Assign.TRUE &&
                 assigned[c.l1] == Assign.NONE &&
                 assigned[c.l2] == Assign.FALSE)
            setVar(c.l1, Assign.FALSE);
        else if (assigned[c.l0] == Assign.TRUE &&
                 assigned[c.l1] == Assign.TRUE &&
                 assigned[c.l2] == Assign.NONE)
            setVar(c.l2, Assign.TRUE);
        return Sat.OK;
    }

    /* helper for setAndPropagate */
    private Sat propagate() {
        /* NOTE: the termination condition is "flexible" since the
         * loop body might insert new elements into `op' */
        for (int i = 0; i < op.size(); i++)
            for (int c : occur[op.get(i)])
                if (check(clause[c]) == Sat.UNSATISFIABLE)
                    return Sat.UNSATISFIABLE;
        return Sat.OK;
    }

    private Sat setAndPropagate(int v, Assign a) {
        op.clear();
        setVar(v, a);
        if (propagate() == Sat.UNSATISFIABLE) {
            /* rollback */
            for (int v2 : op)
                assigned[v2] = Assign.NONE;
            op.clear();
            return Sat.UNSATISFIABLE;
        }
        op.clear();
        return Sat.OK;
    }

    public Assign[] solve() {
        op.clear();
        for (HornClause3 c : clause)
            if (check(c) != Sat.OK)
                return null;
        if (propagate() == Sat.UNSATISFIABLE)
            return null;
        /* dumb chooser of next variable: iterate from beginning to end */
        for (int v = 0; v < assigned.length; v++)
            if (assigned[v] == Assign.NONE)
                if (setAndPropagate(v, Assign.TRUE) == Sat.UNSATISFIABLE)
                    if (setAndPropagate(v, Assign.FALSE) == Sat.UNSATISFIABLE)
                        /* should not happen */
                        assert(false);
        return assigned;
    }


    // "test" the thing
    public static void main(String[] args) {
		PrintWriter writer = new PrintWriter(new OutputStreamWriter(System.err));

		HornClause3[] clauses;
		Assign assign[];

		clauses = new HornClause3[] {
				HornClause3.F(3),
				HornClause3.FT(2, 3)
		};
		assign = new MaxSATSolve(4, clauses).solve();
		assert assign != null;
		assert assign[2] == Assign.FALSE;
		assert assign[3] == Assign.FALSE;

		clauses = new HornClause3[] {
				HornClause3.T(2),
				HornClause3.FT(2, 3),
				HornClause3.FFT(2, 3, 4)
		};
		assign = new MaxSATSolve(5, clauses).solve();
		assert assign != null;
		assert assign[2] == Assign.TRUE;
		assert assign[3] == Assign.TRUE;
		assert assign[4] == Assign.TRUE;

		clauses = new HornClause3[] {
				HornClause3.T(2),
				HornClause3.FT(2, 3),
				HornClause3.FFT(2, 3, 4),
				HornClause3.F(4)
		};
		assign = new MaxSATSolve(5, clauses).solve();
		assert assign == null;

		writer.printf("tests passed\n");
		writer.flush();
    }
}
