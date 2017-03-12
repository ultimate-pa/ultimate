/*
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.woelfing;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * An iterated symbolic memory.
 *
 * @author Dennis Wölfing
 *
 */
public class IteratedSymbolicMemory extends SymbolicMemory {
	private final List<TermVariable> mLoopCounters;
	private final Map<TermVariable, TermVariable> mRenamedVars;
	private final List<SymbolicMemory> mSymbolicMemories;

	/**
	 * Constructs an iterated symbolic memory.
	 *
	 * @param script
	 *            A ManagedScript.
	 * @param symbolicMemories
	 *            A list of symbolic memories of backbones.
	 */
	public IteratedSymbolicMemory(final ManagedScript script, final List<SymbolicMemory> symbolicMemories) {
		super(script);
		mRenamedVars = new HashMap<>();
		mSymbolicMemories = symbolicMemories;

		final int numLoops = mSymbolicMemories.size();
		mLoopCounters = new ArrayList<>(numLoops);
		final Sort sort = mScript.getScript().sort("Int");
		for (int i = 0; i < numLoops; i++) {
			mLoopCounters.add(mScript.constructFreshTermVariable("loopCounter", sort));
		}

		for (final SymbolicMemory symbolicMemory : mSymbolicMemories) {
			for (final IProgramVar var : symbolicMemory.mInVars.keySet()) {
				final TermVariable termVar = symbolicMemory.mInVars.get(var);

				if (mRenamedVars.containsKey(termVar)) {
					continue;
				}

				if (mInVars.containsKey(var)) {
					mRenamedVars.put(termVar, mInVars.get(var));
				} else {
					final TermVariable newTermVar = mScript.constructFreshCopy(termVar);
					mRenamedVars.put(termVar, newTermVar);
					mInVars.put(var, newTermVar);
				}
			}

			for (final IProgramVar var : symbolicMemory.mOutVars.keySet()) {
				final TermVariable termVar = symbolicMemory.mOutVars.get(var);
				if (mOutVars.containsKey(var)) {
					assert mOutVars.get(var) == termVar;
				} else {
					mOutVars.put(var, termVar);
				}
			}
		}

		final Deque<TermVariable> deque = new ArrayDeque<>(mOutVars.values());

		while (!deque.isEmpty()) {
			final TermVariable termVar = deque.pop();
			if (mLoopCounters.contains(termVar) || mInVars.containsValue(termVar)) {
				continue;
			}

			final Term[] terms = new Term[numLoops];
			for (int i = 0; i < numLoops; i++) {
				if (mSymbolicMemories.get(i).mVariableTerms.containsKey(termVar)) {
					terms[i] = mSymbolicMemories.get(i).mVariableTerms.get(termVar);
				}
			}

			final Term iteratedTerm = getIteratedTerm(terms, deque);
			if (iteratedTerm != null) {
				mVariableTerms.put(termVar, iteratedTerm);
			}
		}
	}

	private Term getIteratedTerm(final Term[] terms, final Deque<TermVariable> deque) {
		Term result = null;
		Term inVar = null;
		for (int i = 0; i < terms.length; i++) {
			if (terms[i] == null) {
				continue;
			}

			final Term term = simplifyTerm(terms[i]);

			// TODO: Parse terms that are not additions.
			if (term instanceof ApplicationTerm && "+".equals(((ApplicationTerm) term).getFunction().getName())) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				assert appTerm.getParameters().length == 2;
				if (inVar == null) {
					inVar = simplifyTerm(appTerm.getParameters()[0]);
					result = inVar;
				} else {
					assert inVar == simplifyTerm(appTerm.getParameters()[0]);
				}

				final Term newTerm = mScript.getScript().term("*", mLoopCounters.get(i), appTerm.getParameters()[1]);
				result = mScript.getScript().term("+", result, newTerm);
			}
		}

		if (result != null) {
			deque.addAll(Arrays.asList(result.getFreeVars()));
		}

		return result;
	}

	/**
	 * Simplifies a term.
	 *
	 * @param term
	 *            The term to be simplified.
	 * @return A simplified Term.
	 */
	private Term simplifyTerm(final Term term) {
		if (!(term instanceof TermVariable)) {
			return term;
		}

		if (mRenamedVars.containsKey(term)) {
			return simplifyTerm(mRenamedVars.get(term));
		}

		Term simplifiedTerm = null;

		for (final SymbolicMemory symbolicMemory : mSymbolicMemories) {
			if (symbolicMemory.mVariableTerms.containsKey(term)) {
				// Recursively simplify the term.
				final Term temp = simplifyTerm(symbolicMemory.mVariableTerms.get(term));
				if (simplifiedTerm == null) {
					simplifiedTerm = temp;
				} else if (simplifiedTerm != temp) {
					// The term cannot be simplified.
					return term;
				}
			}
		}

		if (simplifiedTerm != null) {
			return simplifiedTerm;
		}
		return term;
	}

	public List<TermVariable> getLoopCounters() {
		return mLoopCounters;
	}

	/**
	 * Gets one of the symbolic memories this IteratedSymbolicMemory was created from.
	 *
	 * @param index
	 *            The index of the symbolic memory.
	 * @return A SymbolicMemory.
	 */
	public SymbolicMemory getSymbolicMemory(final int index) {
		return mSymbolicMemories.get(index);
	}
}
