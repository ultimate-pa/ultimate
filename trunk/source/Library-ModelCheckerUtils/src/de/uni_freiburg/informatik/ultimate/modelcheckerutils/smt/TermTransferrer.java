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

import java.math.BigInteger;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermTransferrer extends TermTransformer {
	
	public enum TransferMode { ASSUME_DECLARED, DECLARE, UNSUPPORTED_LOGIC }
	
	private final Script m_Script;
	private Set<Sort> m_DeclaredSorts = new HashSet<>();
	
	public TermTransferrer(Script script) {
		m_Script = script;
	}

	@Override
	protected void convert(Term term) {
		declareSortIfNeeded(term);
		if (term instanceof TermVariable) {
			TermVariable tv = (TermVariable) term;
			Term result = m_Script.variable(tv.getName(), tv.getSort());
			setResult(result);
		} else if (term instanceof ConstantTerm) {
			ConstantTerm ct = (ConstantTerm) term;
			if (ct.getValue() instanceof BigInteger) {
				Term result = m_Script.numeral((BigInteger) ct.getValue());
				setResult(result);
			} else {
				throw new AssertionError("unexpected lkjebs");
			}
		} else {
			super.convert(term);
		}
	}

	private void declareSortIfNeeded(Term term) {
		if (!term.getSort().isInternal()) {
			if (m_DeclaredSorts .contains(term.getSort())) {
				m_Script.declareSort(term.getSort().getName(), term.getSort().getIndices().length);
			}
		}
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		Term result = m_Script.term(appTerm.getFunction().getName(), newArgs);
		setResult(result);
	}

	@Override
	public void postConvertLet(LetTerm oldLet, Term[] newValues, Term newBody) {
		throw new UnsupportedOperationException("not yet implemented");
		//Term result = m_Script.let(vars, newValues, newBody);
	}

	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void postConvertAnnotation(AnnotatedTerm old,
			Annotation[] newAnnots, Term newBody) {
		throw new UnsupportedOperationException("not yet implemented");
	}
	
	
	
	

}
