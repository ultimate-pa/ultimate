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

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Replaces booleans variables b by integer replacement variables rep_b whose semantics is rep_b = (ite b 1 0)
 *
 * @author Jan Leike
 * @author Matthias Heizmann
 */
public class RewriteBooleans extends RewriteTermVariables {
	public static final String DESCRIPTION = "Replace boolean variables by integer variables";

	private static final String TERM_VARIABLE_SUFFIX = "bool";

	// FIXME: this should depend on the logic
	private static final String REP_VAR_SORT_NAME = "Int";

	@Override
	protected String getTermVariableSuffix() {
		return TERM_VARIABLE_SUFFIX;
	}

	@Override
	protected String getRepVarSortName() {
		return REP_VAR_SORT_NAME;
	}

	/**
	 * Create a new RewriteBooleans preprocessor
	 *
	 * @param rankVarCollector
	 *            collecting the new in- and outVars
	 * @param script
	 *            the Script for creating new variables
	 */
	public RewriteBooleans(final ReplacementVarFactory varFactory, final ManagedScript script) {
		super(varFactory, script);
	}

	@Override
	protected boolean hasToBeReplaced(final Term term) {
		return isBool(term);
	}

	private static final boolean isBool(final Term term) {
		return SmtSortUtils.isBoolSort(term.getSort());
	}

	@Override
	protected Term constructReplacementTerm(final TermVariable tv) {
		final Term one = SmtUtils.constructIntValue(mScript.getScript(), BigInteger.ONE);
		final Term repTerm = mScript.getScript().term(">=", tv, one);
		return repTerm;
	}

	@Override
	public String getDescription() {
		return DESCRIPTION;
	}

	/**
	 * Given the Term booleanTerm whose Sort is "Bool" return the term (ite booleanTerm one zero)
	 */
	@Override
	protected Term constructNewDefinitionForRankVar(final IProgramVar oldRankVar) {
		final Term booleanTerm = ReplacementVarUtils.getDefinition(oldRankVar);
		assert isBool(booleanTerm);
		final Term one = SmtUtils.constructIntValue(mScript.getScript(), BigInteger.ONE);
		final Term zero = SmtUtils.constructIntValue(mScript.getScript(), BigInteger.ZERO);
		return mScript.getScript().term("ite", booleanTerm, one, zero);
	}

}
