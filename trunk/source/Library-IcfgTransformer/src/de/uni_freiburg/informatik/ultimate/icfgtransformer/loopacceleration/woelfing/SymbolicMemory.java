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

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * A symbolic memory.
 *
 * @author Dennis Wölfing
 *
 */
public class SymbolicMemory {
	protected final ManagedScript mScript;
	protected final Map<IProgramVar, TermVariable> mInVars;
	protected final Map<IProgramVar, TermVariable> mOutVars;
	protected final Map<TermVariable, Term> mVariableTerms;
	protected boolean mOverapproximation;

	protected SymbolicMemory(final ManagedScript script) {
		mScript = script;
		mInVars = new HashMap<>();
		mOutVars = new HashMap<>();
		mVariableTerms = new HashMap<>();
	}

	/**
	 * Constructs a SymbolicMemory from a given transformula.
	 *
	 * @param script
	 *            A ManagedScript.
	 * @param tf
	 *            A transformula that is a conjunction of equalities.
	 * @param overapproximation
	 *            Whether or not the given TransFormula is an overapproximation.
	 */
	public SymbolicMemory(final ManagedScript script, final TransFormula tf, final boolean overapproximation) {
		mScript = script;
		mInVars = tf.getInVars();
		mOutVars = tf.getOutVars();
		mVariableTerms = new HashMap<>();
		mOverapproximation = overapproximation;

		final Term term = tf.getFormula();
		if (!(term instanceof ApplicationTerm)) {
			return;
		}
		final ApplicationTerm appTerm = (ApplicationTerm) term;

		if ("and".equals(appTerm.getFunction().getName())) {
			for (final Term innerTerm : appTerm.getParameters()) {
				if (innerTerm instanceof ApplicationTerm
						&& "=".equals(((ApplicationTerm) innerTerm).getFunction().getName())) {
					final Term[] params = ((ApplicationTerm) innerTerm).getParameters();
					if (params[0] instanceof TermVariable && !mInVars.containsValue(params[0])
							&& !mVariableTerms.containsKey(params[0])) {
						mVariableTerms.put((TermVariable) params[0], params[1]);
					}
				}
			}
		}
	}

	/**
	 * Replaces all occurrences of TermVariables in a given Term by terms from the symbolic memory.
	 *
	 * @param term
	 *            The term to be transformed.
	 * @param termInVars
	 *            The inVars of the given term that should be replaced by outVars of the symbolic memory or null if
	 *            inVars should not be replaced.
	 * @return A transformed term.
	 */
	public Term replaceTermVars(final Term term, final Map<IProgramVar, TermVariable> termInVars) {
		if (mVariableTerms.containsKey(term)) {
			// note that we admit mappings to null here and you cannot replace contains/get with a get and null test
			final Term newTerm = mVariableTerms.get(term);
			return newTerm == null ? term : replaceTermVars(newTerm, termInVars);
		}

		if (termInVars != null && termInVars.values().contains(term)) {
			for (final Map.Entry<IProgramVar, TermVariable> entry : termInVars.entrySet()) {
				if (entry.getValue() == term && mOutVars.containsKey(entry.getKey())) {
					return replaceTermVars(mOutVars.get(entry.getKey()), termInVars);
				}
			}
		}

		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final Term[] params = appTerm.getParameters().clone();

			for (int i = 0; i < params.length; i++) {
				params[i] = replaceTermVars(params[i], termInVars);
			}

			if ("=".equals(appTerm.getFunction().getName()) && params.length == 2 && params[0].equals(params[1])) {
				// Replace equations where both sides are equal by true to simplify the resulting term.
				return mScript.getScript().term("true");
			}

			return mScript.getScript().term(appTerm.getFunction().getName(), params);
		}

		return term;
	}

	/**
	 * Converts the symbolic memory to a term.
	 *
	 * @return A Term containing all variable assignments.
	 */
	public Term toTerm() {
		Term term = mScript.getScript().term("true");

		for (final Map.Entry<TermVariable, Term> entry : mVariableTerms.entrySet()) {
			term = SmtUtils.and(mScript.getScript(), term, mScript.getScript().term("=", entry.getKey(), entry.getValue()));
		}

		return term;
	}

	public Map<IProgramVar, TermVariable> getInVars() {
		return mInVars;
	}

	public Map<IProgramVar, TermVariable> getOutVars() {
		return mOutVars;
	}

	public Map<TermVariable, Term> getVariableTerms() {
		return mVariableTerms;
	}

	/**
	 * Returns a term that represents the symbolic memory for a given output program variable.
	 *
	 * @param var
	 *            A IProgramVar.
	 * @return A Term for the given variable or null if the variable has an unknown value.
	 */
	public Term getVariableTerm(final IProgramVar var) {
		if (!mOutVars.containsKey(var)) {
			return null;
		}
		return getVariableTerm(mOutVars.get(var));
	}

	/**
	 * Returns a term for a given term variable.
	 *
	 * @param termVar
	 *            A TermVariable.
	 * @return A Term for the given variable or null if the variable has an unknown value.
	 */
	public Term getVariableTerm(final TermVariable termVar) {
		return mVariableTerms.get(termVar);
	}

	/**
	 * Returns whether this symbolic memory is an overapproximation.
	 *
	 * @return true if the symbolic memory is an overapproximation.
	 */
	public boolean isOverapproximation() {
		return mOverapproximation;
	}

	@Override
	public String toString() {
		return mVariableTerms.toString();
	}
}
