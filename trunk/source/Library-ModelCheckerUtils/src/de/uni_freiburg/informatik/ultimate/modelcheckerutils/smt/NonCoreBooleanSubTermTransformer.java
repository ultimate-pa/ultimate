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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * Transform non-CoreBoolean subterms of a term. Here, we call a term 
 * non-CoreBoolean if it is not an ApplicationTerm whose connective is defined
 * by the core theory and whose parameters dot not all have sort Bool.
 * 
 * @author Matthias Heizmann
 *
 */
public abstract class NonCoreBooleanSubTermTransformer {
	
	private NonCoreBooleanSubtermTransformerHelper m_TransformerHelper;
	
	public Term transform(Term term) {
		if (!term.getSort().getName().equals("Bool")) {
			throw new IllegalArgumentException("Input term of sort Bool");
		}
		m_TransformerHelper = new NonCoreBooleanSubtermTransformerHelper();
		Term result = m_TransformerHelper.transform(term);
		return result;
	}

	private static boolean hasBooleanParams(Term[] parameters) {
		for (Term term : parameters) {
			if (!term.getSort().getName().equals("Bool")) {
				return false;
			}
		}
		return true;
	}

	private static boolean isCoreBooleanConnective(String fun) {
		if (fun.equals("=")) {
			return true;
		} else if (fun.equals("and")) {
			return true;
		} else if (fun.equals("or")) {
			return true;
		} else if (fun.equals("=>")) {
			return true;
		} else if (fun.equals("xor")) {
			return true;
		} else if (fun.equals("distinct")) {
			return true;
		} else if (fun.equals("ite")) {
			return true;
		} else {
			return false;
		}
	}


	private class NonCoreBooleanSubtermTransformerHelper extends TermTransformer {

		@Override
		protected void convert(Term term) {
			assert term.getSort().getName().equals("Bool") : "not Bool";
			if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				String funName = appTerm.getFunction().getName();
				if (isCoreBooleanConnective(funName) && 
						hasBooleanParams(appTerm.getParameters())) {
					super.convert(term);
				} else {
					Term transformed = transformNonCoreBooleanSubterm(term);
					setResult(transformed);
					return;
				}
			}
			super.convert(term);
		}
		
	}


	protected abstract Term transformNonCoreBooleanSubterm(Term term);

}
