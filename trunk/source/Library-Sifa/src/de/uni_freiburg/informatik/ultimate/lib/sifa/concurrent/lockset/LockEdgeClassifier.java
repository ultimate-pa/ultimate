/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/** Recognizes the integer-valued mutex encoding produced by the current frontends. */
public final class LockEdgeClassifier {

	private LockEdgeClassifier() {
	}

	public static boolean isAcquire(final TransFormula tf, final IProgramVar var) {
		return Rational.ONE.equals(literalAssignedToOutVar(tf, var)) && assumesInVarZero(tf, var);
	}

	public static boolean isRelease(final TransFormula tf, final IProgramVar var) {
		return Rational.ZERO.equals(literalAssignedToOutVar(tf, var));
	}

	public static IProgramVar acquiredLockVarFromTf(final TransFormula tf, final Set<IProgramVar> lockVars) {
		for (final IProgramVar lockVar : lockVars) {
			if (isAcquire(tf, lockVar)) {
				return lockVar;
			}
		}
		return null;
	}

	public static IProgramVar releasedLockVarFromTf(final TransFormula tf, final Set<IProgramVar> lockVars) {
		for (final IProgramVar lockVar : lockVars) {
			if (isRelease(tf, lockVar)) {
				return lockVar;
			}
		}
		return null;
	}

	private static boolean assumesInVarZero(final TransFormula tf, final IProgramVar var) {
		final TermVariable inVar = tf.getInVars().get(var);
		if (inVar == null) {
			return false;
		}
		final var literal = literalBoundTo(tf.getFormula(), inVar);
		return literal != null && literal.equals(Rational.ZERO);
	}

	static Rational literalAssignedToOutVar(final TransFormula tf, final IProgramVar lockVar) {
		if (tf == null) {
			return null;
		}
		final TermVariable outVar = tf.getOutVars().get(lockVar);
		if (outVar == null || outVar.equals(tf.getInVars().get(lockVar))) {
			return null;
		}
		final Rational literal = literalBoundTo(tf.getFormula(), outVar);
		return Rational.ZERO.equals(literal) || Rational.ONE.equals(literal) ? literal : null;
	}

	private static Rational literalBoundTo(final Term formula, final TermVariable target) {
		for (final Term conjunct : SmtUtils.getConjuncts(formula)) {
			final ApplicationTerm app = SmtUtils.getFunctionApplication(conjunct, "=");
			if (app == null || app.getParameters().length != 2) {
				continue;
			}
			final Term left = app.getParameters()[0];
			final Term right = app.getParameters()[1];
			final Term other;
			if (target.equals(left)) {
				other = right;
			} else if (target.equals(right)) {
				other = left;
			} else {
				continue;
			}
			final Rational literal = SmtUtils.tryToConvertToLiteral(other);
			if (literal != null) {
				return literal;
			}
		}
		return null;
	}
}
