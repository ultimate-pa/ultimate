/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Replaces variables that have a used defined type by variables that have type Int. We detect these variables by their
 * Sort. If a term does not have an "internal" Sort, it originates from a user defined type.
 * 
 * @author Matthias Heizmann
 */
public class RewriteUserDefinedTypes extends RewriteTermVariables {
	public static final String DESCRIPTION = "Replace variables that have a used defined type";

	private static final String TERM_VARIABLE_SUFFIX = "udt";
	private static final String REP_VAR_SORT_NAME = "Int";

	/**
	 * Create a new RewriteBooleans preprocessor
	 * 
	 * @param rankVarCollector
	 *            collecting the new in- and outVars
	 * @param script
	 *            the Script for creating new variables
	 */
	public RewriteUserDefinedTypes(final ReplacementVarFactory varFactory, final ManagedScript script) {
		super(varFactory, script);
	}

	@Override
	protected String getTermVariableSuffix() {
		return TERM_VARIABLE_SUFFIX;
	}

	@Override
	protected String getRepVarSortName() {
		return REP_VAR_SORT_NAME;
	}

	@Override
	protected boolean hasToBeReplaced(final Term term) {
		return hasNonInternalSort(term);
	}

	/**
	 * return true iff sort of term is not an internal sort
	 */
	private static final boolean hasNonInternalSort(final Term term) {
		return !term.getSort().getRealSort().isInternal();
	}

	@Override
	protected Term constructReplacementTerm(final TermVariable newTv) {
		// return the new Tv
		return newTv;
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	/**
	 * TODO: at the moment we us the old definition. This is a problem if the variable indeed occurs in a ranking
	 * function. Solution: For each type we have to introduce an auxiliary uninterpreted function toInt(). We will then
	 * return toInt(definition).
	 * 
	 */
	@Override
	protected Term constructNewDefinitionForRankVar(final IProgramVar oldRankVar) {
		final Term definition = ReplacementVarUtils.getDefinition(oldRankVar);
		return definition;
	}

}
