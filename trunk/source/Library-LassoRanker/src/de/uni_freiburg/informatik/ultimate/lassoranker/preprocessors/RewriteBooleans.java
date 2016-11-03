/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;


/**
 * Replaces booleans variables b by integer replacement variables rep_b whose
 * semantics is rep_b = (ite b 1 0) 
 * 
 * @author Jan Leike 
 * @author Matthias Heizmann
 */
public class RewriteBooleans extends RewriteTermVariables {
	public static final String s_Description = "Replace boolean variables by integer variables";
	
	private static final String s_TermVariableSuffix = "bool";
	private static final String s_repVarSortName = "Int"; // FIXME: this should depend on the logic
	
	@Override
	protected String getTermVariableSuffix() {
		return s_TermVariableSuffix;
	}
	@Override
	protected String getRepVarSortName() {
		return s_repVarSortName;
	}
	
	/**
	 * Create a new RewriteBooleans preprocessor
	 * @param rankVarCollector collecting the new in- and outVars
	 * @param script the Script for creating new variables
	 */
	public RewriteBooleans(final ReplacementVarFactory varFactory, final ManagedScript script) {
		super(varFactory, script);
	}
	
	@Override
	protected boolean hasToBeReplaced(final Term term) {
		return isBool(term);
	}

	/**
	 * return true iff sort of term is Bool.
	 */
	private static final boolean isBool(final Term term) {
		return term.getSort().getName().equals("Bool");
	}
	
	@Override
	protected Term constructReplacementTerm(final TermVariable tv) {
		final Term one = mScript.getScript().numeral(BigInteger.ONE);
		final Term repTerm = mScript.getScript().term(">=", tv, one);
		return repTerm;
	}

	
	@Override
	public String getDescription() {
		return s_Description;
	}
	
	/**
	 * Given the Term booleanTerm whose Sort is "Bool" return the term
	 * (ite booleanTerm one zero)
	 */
	@Override
	protected Term constructNewDefinitionForRankVar(final IProgramVar oldRankVar) {
		final Term booleanTerm = ReplacementVarUtils.getDefinition(oldRankVar);
		assert booleanTerm.getSort().getName().equals("Bool");
		final Term one = mScript.getScript().numeral(BigInteger.ONE);
		final Term zero = mScript.getScript().numeral(BigInteger.ZERO);
		return mScript.getScript().term("ite", booleanTerm, one, zero);
	}
	

}
