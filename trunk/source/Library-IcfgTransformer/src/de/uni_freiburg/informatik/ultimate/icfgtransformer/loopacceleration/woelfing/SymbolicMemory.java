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

/**
 * A symbolic memory.
 *
 * @author Dennis Wölfing
 *
 */
public class SymbolicMemory {
	protected final Map<IProgramVar, TermVariable> mInVars;
	protected final Map<IProgramVar, TermVariable> mOutVars;
	protected final Map<TermVariable, Term> mVariableTerms;

	protected SymbolicMemory() {
		mInVars = new HashMap<>();
		mOutVars = new HashMap<>();
		mVariableTerms = new HashMap<>();
	}

	/**
	 * Constructs a SymbolicMemory from a given transformula.
	 *
	 * @param tf
	 *            A transformula that is a conjunction of equalities.
	 */
	public SymbolicMemory(final TransFormula tf) {
		mInVars = tf.getInVars();
		mOutVars = tf.getOutVars();
		mVariableTerms = new HashMap<>();

		final Term term = tf.getFormula();
		if (!(term instanceof ApplicationTerm)) {
			return;
		}
		final ApplicationTerm appTerm = (ApplicationTerm) term;

		if ("and".equals(appTerm.getFunction().getName())) {
			for (final Term innerTerm : appTerm.getParameters()) {
				if (innerTerm instanceof ApplicationTerm && "=".equals(((ApplicationTerm) innerTerm).getFunction().getName())) {
					final Term[] params = ((ApplicationTerm) innerTerm).getParameters();
					if (params[0] instanceof TermVariable) {
						mVariableTerms.put((TermVariable) params[0], params[1]);
					}
				}
			}
		}
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

	@Override
	public String toString() {
		return mVariableTerms.toString();
	}
}
