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

/**
 * Logical clause. Conjunction of one, two, or three literals.
 *
 * l0 is a negative literal (if >= 0)
 * l1 is a negative literal (if >= 0)
 * l2 is a positive literal (if >= 0)
 *
 * By convention, 0 is constant false and 1 is constant true.
 * In this way, clauses with effective length 0, 1, 2 or 3 can be constructed.
 *
 * @author stimpflj
 */
class HornClause3 {

    public final int l0, l1, l2;

    private HornClause3(int l0, int l1, int l2)
        { this.l0 = l0; this.l1 = l1; this.l2 = l2; }

    /* These are fixed constants: Clients rely on their values to not hit them
     * accidentally */
    public static final int falseVar = 0;
    public static final int trueVar = 1;

    public static HornClause3 T(int z)                 { return new HornClause3(1, 1, z); }
    public static HornClause3 F(int x)                 { return new HornClause3(x, 1, 0); }
    public static HornClause3 FF(int x, int y)         { return new HornClause3(x, y, 0); }
    public static HornClause3 FT(int x, int z)         { return new HornClause3(x, 1, z); }
    public static HornClause3 FFT(int x, int y, int z) { return new HornClause3(x, y, z); }
};
