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
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
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
		final Sort sort = SmtSortUtils.getIntSort(mScript);
		for (int i = 0; i < numLoops; i++) {
			mLoopCounters.add(mScript.constructFreshTermVariable("loopCounter", sort));
		}

		for (final SymbolicMemory symbolicMemory : mSymbolicMemories) {
			mOverapproximation |= symbolicMemory.isOverapproximation();

			for (final IProgramVar var : symbolicMemory.mInVars.keySet()) {
				final TermVariable termVar = symbolicMemory.mInVars.get(var);

				if (mInVars.containsKey(var)) {
					assert !mInVars.get(var).equals(termVar);
					mRenamedVars.put(termVar, mInVars.get(var));
				} else if (mRenamedVars.containsKey(termVar)) {
					mInVars.put(var, mRenamedVars.get(termVar));
				} else {
					final TermVariable newTermVar = mScript.constructFreshCopy(termVar);
					mRenamedVars.put(termVar, newTermVar);
					mInVars.put(var, newTermVar);
				}
			}

			for (final IProgramVar var : symbolicMemory.mOutVars.keySet()) {
				final TermVariable termVar = symbolicMemory.mOutVars.get(var);

				if (mOutVars.containsKey(var)) {
					assert !mOutVars.get(var).equals(termVar);
					mRenamedVars.put(termVar, mOutVars.get(var));
				} else if (mRenamedVars.containsKey(termVar)) {
					mOutVars.put(var, mRenamedVars.get(termVar));
				} else {
					final TermVariable newTermVar = mScript.constructFreshCopy(termVar);
					mRenamedVars.put(termVar, newTermVar);
					mOutVars.put(var, newTermVar);
				}
			}
		}

		final Deque<IProgramVar> deque = new ArrayDeque<>(mOutVars.keySet());

		while (!deque.isEmpty()) {
			final IProgramVar var = deque.pop();

			final Term iteratedTerm = getIteratedTerm(var);
			if (iteratedTerm != null) {
				mVariableTerms.put(mOutVars.get(var), iteratedTerm);
			} else {
				mOverapproximation = true;
			}
		}
	}

	/**
	 * Calculates an iterated term for the given program variable.
	 *
	 * @param var
	 *            An IProgramVar.
	 * @return An iterated Term or null.
	 */
	private Term getIteratedTerm(final IProgramVar var) {
		final Term[] terms = new Term[mSymbolicMemories.size()];
		for (int i = 0; i < terms.length; i++) {
			terms[i] = mSymbolicMemories.get(i).getVariableTerm(var);
		}

		Term result = mInVars.get(var);
		ConstantTerm constantTerm = null;
		final List<TermVariable> constantLoopCounters = new ArrayList<>();

		for (int i = 0; i < terms.length; i++) {
			final Term term = simplifyTerm(mSymbolicMemories.get(i), terms[i]);

			if (term == null) {
				return null;
			}

			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				assert "+".equals(appTerm.getFunction().getName());
				final Term[] params = appTerm.getParameters();

				if (params[0] != mInVars.get(var)) {
					return null;
				}

				final Term[] newParams = new Term[params.length];
				newParams[0] = result;

				for (int j = 1; j < params.length; j++) {
					if (!(params[j] instanceof ConstantTerm)) {
						return null;
					}
					newParams[j] = mScript.getScript().term("*", mLoopCounters.get(i), params[j]);
				}

				result = mScript.getScript().term("+", mergeSums(newParams));
			} else if (term instanceof TermVariable) {
				if (term != mInVars.get(var)) {
					return null;
				}
			} else if (term instanceof ConstantTerm) {
				if (constantTerm != null && constantTerm != term) {
					return null;
				}
				constantTerm = (ConstantTerm) term;
				constantLoopCounters.add(mLoopCounters.get(i));
			} else {
				throw new AssertionError("Unexpected term type.");
			}
		}

		if (constantTerm != null) {
			if (result != mInVars.get(var)) {
				return null;
			}

			final Term zeroTerm = Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript));
			Term condition = mScript.getScript().term("false");

			for (final TermVariable loopCounter : constantLoopCounters) {
				final Term term = mScript.getScript().term(">", loopCounter, zeroTerm);
				condition = SmtUtils.or(mScript.getScript(), condition, term);
			}

			if (result == null) {
				// This can happen when no backbone that assigns to this variable does use the old value of that
				// variable. In this case just create a new TermVariable for it.
				final TermVariable newTermVar = mScript.constructFreshCopy(var.getTermVariable());
				mInVars.put(var, newTermVar);
				result = newTermVar;
			}

			return mScript.getScript().term("ite", condition, constantTerm, result);
		}

		return result;
	}

	/**
	 * Merges the parameters of of a + term.
	 *
	 * @param params
	 *            The parameters of a + term.
	 * @return The parameters of a new + term equivalent to the original term.
	 */
	private static Term[] mergeSums(final Term[] params) {
		final List<Term> newParams = new ArrayList<>(Arrays.asList(params));

		for (int i = 0; i < newParams.size(); i++) {
			if (newParams.get(i) instanceof ApplicationTerm
					&& "+".equals(((ApplicationTerm) newParams.get(i)).getFunction().getName())) {
				final ApplicationTerm appTerm = (ApplicationTerm) newParams.get(i);
				newParams.remove(i);
				newParams.addAll(i, Arrays.asList(appTerm.getParameters()));
			}
		}

		return newParams.toArray(new Term[0]);
	}

	/**
	 * Simplifies a given term and exclude things we cannot handle.
	 *
	 * @param symbolicMemory
	 *            The symbolic memory the term was taken from.
	 * @param term
	 *            A Term.
	 * @return A simplifies term.
	 */
	private Term simplifyTerm(final SymbolicMemory symbolicMemory, final Term term) {
		if (term instanceof TermVariable) {
			if (mRenamedVars.containsKey(term)) {
				return simplifyTerm(symbolicMemory, mRenamedVars.get(term));
			} else if (mInVars.containsValue(term)) {
				return term;
			}

			final Term t = symbolicMemory.getVariableTerm((TermVariable) term);
			return simplifyTerm(symbolicMemory, t);
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if ("+".equals(appTerm.getFunction().getName())) {
				Term[] params = appTerm.getParameters().clone();

				for (int i = 0; i < params.length; i++) {
					params[i] = simplifyTerm(symbolicMemory, params[i]);
					if (params[i] == null) {
						return null;
					}
				}

				params = mergeSums(params);
				assert mInVars.containsValue(params[0]);
				return mScript.getScript().term("+", params);
			}
		} else if (term instanceof ConstantTerm) {
			return term;
		}

		return null;
	}

	@Override
	public Term replaceTermVars(final Term term, final Map<IProgramVar, TermVariable> termInVars) {
		if (mRenamedVars.containsKey(term) && (termInVars == null || !termInVars.containsValue(term))) {
			if (mOutVars.containsValue(mRenamedVars.get(term))) {
				return replaceTermVars(mRenamedVars.get(term), termInVars);
			}
			assert false;
		}

		if (mRenamedVars.containsKey(term) && termInVars != null && termInVars.containsValue(term)) {
			for (final Map.Entry<IProgramVar, TermVariable> entry : termInVars.entrySet()) {
				if (entry.getValue().equals(term) && !mOutVars.containsKey(entry.getKey())) {
					return mRenamedVars.get(term);
				}
			}
		}

		return super.replaceTermVars(term, termInVars);
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
