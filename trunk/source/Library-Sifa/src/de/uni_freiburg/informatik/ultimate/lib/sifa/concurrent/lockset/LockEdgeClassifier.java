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

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This class checks whether a statement locks or unlocks a mutex. The mutex can be stored in a variable or an array
 * element, including an element of a nested array.
 */
final class LockEdgeClassifier {

	enum Operation {
		ACQUIRE, RELEASE
	}

	record Update(List<Term> indices, Operation operation) {
	}

	private LockEdgeClassifier() {
	}

	static Update classify(final TransFormula transitionFormula, final IProgramVar variable,
			final Set<IProgramVar> stableIndexVars, final ManagedScript script) {
		final Term previousValue = transitionFormula.getInVars().get(variable);
		final Term assignedValue = findAssignedValue(SmtUtils.getConjuncts(transitionFormula.getFormula()),
				transitionFormula.getOutVars().get(variable));
		if (variable.getTermVariable().getSort().isArraySort()) {
			return classifyArrayWrite(transitionFormula, previousValue, assignedValue, stableIndexVars, script);
		}
		return classifyWrite(transitionFormula, List.of(), previousValue, assignedValue);
	}

	private static Update classifyArrayWrite(final TransFormula transitionFormula, final Term previousValue,
			final Term assignedValue, final Set<IProgramVar> stableIndexVars, final ManagedScript script) {
		final MultiDimensionalStore store = MultiDimensionalStore.of(assignedValue);
		if (store == null || !store.getArray().equals(previousValue) || store.getValue().getSort().isArraySort()) {
			return null;
		}
		final List<Term> indices = normalizeIndices(store.getIndex(), transitionFormula, stableIndexVars, script);
		if (indices == null) {
			return null;
		}
		final Term previousElement =
				SmtUtils.multiDimensionalSelect(script.getScript(), previousValue, store.getIndex());
		return classifyWrite(transitionFormula, indices, previousElement, store.getValue());
	}

	/**
	 * The lock and unlock statements must refer to the same array element, such as {@code locks[i]}. We use the program
	 * variables to compare the indices from different statements. If an index can change while other threads run, we do
	 * not track that mutex.
	 */
	private static List<Term> normalizeIndices(final ArrayIndex indices, final TransFormula transitionFormula,
			final Set<IProgramVar> stableIndexVars, final ManagedScript script) {
		final Map<TermVariable, TermVariable> substitution =
				TransFormulaUtils.constructInvarsToDefaultvarsMap(transitionFormula);
		final Set<TermVariable> stableIndexTerms =
				stableIndexVars.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		for (final Term index : indices) {
			for (final TermVariable variable : index.getFreeVars()) {
				if (!stableIndexTerms.contains(substitution.get(variable))) {
					return null;
				}
			}
		}
		return List.copyOf(indices.applySubstitution(script, substitution));
	}

	private static Update classifyWrite(final TransFormula transitionFormula, final List<Term> indices,
			final Term previousValue, final Term assignedValue) {
		if (isUnlocked(assignedValue)) {
			return new Update(indices, Operation.RELEASE);
		}
		if (isLocked(assignedValue)
				&& assumesUnlocked(SmtUtils.getConjuncts(transitionFormula.getFormula()), previousValue)) {
			return new Update(indices, Operation.ACQUIRE);
		}
		return null;
	}

	private static boolean assumesUnlocked(final Term[] conjuncts, final Term previousValue) {
		for (final Term conjunct : conjuncts) {
			if (isUnlocked(otherSideOfEquality(conjunct, previousValue))) {
				return true;
			}
			final ApplicationTerm negation = SmtUtils.getFunctionApplication(conjunct, "not");
			if (negation != null && negation.getParameters()[0].equals(previousValue)) {
				return true;
			}
		}
		return false;
	}

	private static boolean isUnlocked(final Term term) {
		return term != null
				&& (SmtUtils.isFalseLiteral(term) || Rational.ZERO.equals(SmtUtils.tryToConvertToLiteral(term)));
	}

	private static boolean isLocked(final Term term) {
		return term != null
				&& (SmtUtils.isTrueLiteral(term) || Rational.ONE.equals(SmtUtils.tryToConvertToLiteral(term)));
	}

	private static Term findAssignedValue(final Term[] conjuncts, final Term assignedVariable) {
		for (final Term conjunct : conjuncts) {
			final Term other = otherSideOfEquality(conjunct, assignedVariable);
			if (isUnlocked(other) || isLocked(other) || SmtUtils.getFunctionApplication(other, "store") != null) {
				return other;
			}
		}
		return null;
	}

	private static Term otherSideOfEquality(final Term formula, final Term knownSide) {
		final ApplicationTerm equality = SmtUtils.getFunctionApplication(formula, "=");
		if (equality == null || equality.getParameters().length != 2) {
			return null;
		}
		final Term left = equality.getParameters()[0];
		final Term right = equality.getParameters()[1];
		if (left.equals(knownSide)) {
			return right;
		}
		return right.equals(knownSide) ? left : null;
	}
}
