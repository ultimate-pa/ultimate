/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Arrays;
import java.util.Comparator;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;


/**
 * Brings Terms into a normal form where all parameters that of commutative
 * functions (resp. functions for that this class knows that they are
 * commutative) are sorted according to their hash code.
 * Furthermore all AffineRelations are transformed into positive normal form.
 * 
 * This can simplify terms, e.g., (or (and A B) (and B A)) will be simplified
 * to (and A B) (except in the very rare case where the hash code of A and B
 * coincides).
 * 
 * Note that this is still experimental.
 * Problems: AffineRelations are not yet sorted according to hash code.
 * We do not want this, because it is a problem for legibility, we do not want
 * to have terms like (+ x*2 1 3*y), instead we would prefer (+ 2*x 3*y 1):
 * coefficient before variable, constant term at last position.
 * @author Matthias Heizmann
 *
 */
public class CommuhashNormalForm {

	private final IUltimateServiceProvider m_Services;
	private final Script m_Script;
	
	public CommuhashNormalForm(IUltimateServiceProvider services, Script script) {
		super();
		m_Services = services;
		m_Script = script;
	}
	
	public Term transform(Term term) {
		Logger logger = m_Services.getLoggingService().getLogger(ModelCheckerUtils.sPluginID);
		logger.debug(new DebugMessage(
				"applying CommuhashNormalForm to formula of DAG size {0}", 
				new DagSizePrinter(term)));
		Term result = (new CommuhashNormalFormHelper()).transform(term);
		logger.debug(new DebugMessage(
				"DAG size before CommuhashNormalForm {0}, DAG size after CommuhashNormalForm {1}", 
				new DagSizePrinter(term), new DagSizePrinter(result)));
		assert (Util.checkSat(m_Script, m_Script.term("distinct", term, result)) != LBool.SAT) : "CommuhashNormalForm transformation unsound";
		return result;
	}
	
	
	private boolean isKnownToBeCommutative(String applicationString) {
		switch (applicationString) {
		case "and":
		case "or":
		case "=":
		case "distinct":
		case "+":
		case "*":
			return true;
		default:
			return false;
		}
	}

	private class CommuhashNormalFormHelper extends TermTransformer {

		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			String funcname = appTerm.getFunction().getApplicationString();
			if (isKnownToBeCommutative(funcname)) {
				Term simplified = constructTermWithSortedParams(funcname, newArgs);
				setResult(simplified);
			} else {
				super.convertApplicationTerm(appTerm, newArgs);
			}
		}

		@Override
		protected void convert(Term term) {
			try {
				Term result = tryToTransformToPositiveNormalForm(term);
				setResult(result);
			} catch (NotAffineException e) {
				// descent, input is no AffineRelation
				super.convert(term);
			} 
		}

		private Term tryToTransformToPositiveNormalForm(Term simplified) throws NotAffineException {
			AffineRelation affRel = new AffineRelation(simplified, TransformInequality.STRICT2NONSTRICT);
			Term pnf = affRel.positiveNormalForm(m_Script);
			return pnf;
		}

		private Term[] sortByHashCode(final Term[] params) {
			Term[] sortedParams = params.clone();
			Comparator<Term> hashBasedComperator = new Comparator<Term>() {
				@Override
				public int compare(Term arg0, Term arg1) {
					return Integer.compare(arg0.hashCode(), arg1.hashCode());
				}
			};
			Arrays.sort(sortedParams, hashBasedComperator);
			return sortedParams;
		}
		
		private Term constructTermWithSortedParams(String funcname, Term[] params) {
			Term[] sortedParams = sortByHashCode(params);
			Term simplified = SmtUtils.termWithLocalSimplification(
					m_Script, funcname, sortedParams);
			return simplified;
		}

	}
}
