/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * Transform Boolean Term into conjunctive normal form.
 * @author heizmann@informatik.uni-freiburg.de
 */

public class Cnf extends Xnf {
	
	public Cnf(Script script, IUltimateServiceProvider services, 
			IFreshTermVariableConstructor freshTermVariableConstructor) {
		super(script,services, freshTermVariableConstructor);
	}
	
	
	@Override
	protected NnfTransformerHelper getNnfTransformerHelper(IUltimateServiceProvider services) {
		return new CnfTransformerHelper(services);
	}



	protected class CnfTransformerHelper extends XnfTransformerHelper {
		
		protected CnfTransformerHelper(IUltimateServiceProvider services) {
			super(services);
		}

		@Override
		public String innerConnectiveSymbol() {
			return "or";
		}

		@Override
		public String outerConnectiveSymbol() {
			return "and";
		}
		
		@Override
		public String innerJunctionName() {
			return "disjunction";
		}

		@Override
		public String outerJunctionName() {
			return "conjuction";
		}

		@Override
		public Term innerConnective(Script script, List<Term> params) {
			Term result = SmtUtils.or(m_Script, params);
			return result;
		}

		@Override
		public Term outerConnective(Script script, List<Term> params) {
			Term result = SmtUtils.and(m_Script, params);
			return result;
		}

		@Override
		public Term[] getOuterJuncts(Term term) {
			return SmtUtils.getConjuncts(term);
		}

	}

}
