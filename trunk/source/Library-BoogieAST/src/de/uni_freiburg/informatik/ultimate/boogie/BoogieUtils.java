/*
 * Copyright (C) 2025 Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;

/**
 * Provides static auxiliary methods for Boogie.
 */
public class BoogieUtils {

	private BoogieUtils() {
		// Prevent instantiation of this utility class
	}

	/**
	 * Is there a break statement insides this code that is not part of a while
	 * statement? (Motivation: We want to detect break statement that may jump out
	 * of this code. If the break statement occurs in an inner while statement, it
	 * jumps only after the while statement.)
	 */
	public static boolean containsOuterBreak(final Statement[] statementList) {
		for (final Statement element : statementList) {
			final boolean isBreakableCode = containsOuterBreak(element);
			if (isBreakableCode) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Is there a break statement insides this statement that is not part of a
	 * `while` statement? (Motivation: We want to detect break statement that may
	 * jump out of this code. If the break statement occurs in an inner while
	 * statement, it jumps only after the inner while statement.)
	 */
	public static boolean containsOuterBreak(final Statement st) {
		return switch (st) {
		case final BreakStatement brSt -> true;
		case final AssignmentStatement assiSt -> false;
		case final AssumeStatement assuSt -> false;
		case final HavocStatement havoSt -> false;
		case final IfStatement ifSt -> containsOuterBreak(ifSt);
		// BreakStatements inside an inner WhileStatement affect only this inner
		// WhileStatement
		case final WhileStatement whiSt -> false;
		case final AssertStatement assSt -> false;
		case final CallStatement caSt -> false;
		case final JoinStatement joSt -> false;
		case final ForkStatement foSt -> false;
		case final GotoStatement goSt -> false;
		case final Label laSt -> false;
		case final ReturnStatement reSt -> false;
		// Maybe superficial to traverse the AtomicStatement. AtomicStatements probably
		// should not contain a BreakStatement.
		case final AtomicStatement atoSt -> containsOuterBreak(atoSt.getBody());
		default -> throw new UnsupportedOperationException("Statement " + st.getClass() + " not supported");
		};
	}

	private static boolean containsOuterBreak(final IfStatement st) {
		final boolean isIfBreakableCode = containsOuterBreak(st.getThenPart());
		if (isIfBreakableCode) {
			return true;
		}
		return containsOuterBreak(st.getElsePart());
	}

}
