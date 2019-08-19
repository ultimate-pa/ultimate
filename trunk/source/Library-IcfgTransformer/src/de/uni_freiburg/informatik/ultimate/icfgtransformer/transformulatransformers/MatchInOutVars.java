/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IcfgTransformer library.
 * 
 * The ULTIMATE IcfgTransformer library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IcfgTransformer library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Add a corresponding inVar for all outVars and a corresponding outVar for all inVars.
 * 
 * This is done to ease the implementation of the LassoRanker. Furthermore, if the loop has an outVar without a
 * corresponding inVar we can obtain an unsound supporting invariant (which is demonstrated by Madrid.bpl) There might
 * be also other soundness problems if we omit this preprocessor.
 */
public class MatchInOutVars extends TransitionPreprocessor {
	public static final String DESCRIPTION = "Add a corresponding inVars and outVars";

	public MatchInOutVars() {
		super();
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	@Override
	public ModifiableTransFormula process(final ManagedScript script, final ModifiableTransFormula tf) throws TermException {
		addMissingInVars(script, tf);
		addMissingOutVars(script, tf);
		// assert eachInVarHasOutVar(tf) : "some inVars do not have outVars";
		return tf;
	}

	private void addMissingInVars(final ManagedScript script, final ModifiableTransFormula tf) {
		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			if (!tf.getInVars().containsKey(entry.getKey())) {
				final String id = SmtUtils.removeSmtQuoteCharacters(entry.getKey().getGloballyUniqueId());
				final TermVariable inVar = script.constructFreshTermVariable(id, entry.getValue().getSort());
				tf.addInVar(entry.getKey(), inVar);
			}
		}
	}

	private void addMissingOutVars(final ManagedScript script, final ModifiableTransFormula tf) {
		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			if (!tf.getOutVars().containsKey(entry.getKey())) {
				final String id = SmtUtils.removeSmtQuoteCharacters(entry.getKey().getGloballyUniqueId());
				final TermVariable inVar = script.constructFreshTermVariable(id, entry.getValue().getSort());
				tf.addOutVar(entry.getKey(), inVar);
			}
		}
	}

	/**
	 * Return true iff we have an ourVar for each inVar. At the moment this holds by convention. We might drop this
	 * convention in the future. Then this class also has to introduce new outVars. TODO: Maybe we want to use this
	 * method as a check after all preprocessing steps.
	 */
	private static boolean eachInVarHasOutVar(final ModifiableTransFormula tf) {
		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			if (!tf.getOutVars().containsKey(entry.getKey())) {
				assert false : "no outVar for inVar " + entry.getKey();
				return false;
			}
		}
		return true;
	}
}
