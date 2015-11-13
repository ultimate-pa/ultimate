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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermTransferrer extends TermTransformer {
	
	public enum TransferMode { ASSUME_DECLARED, DECLARE, UNSUPPORTED_LOGIC }
	
	protected final Script m_Script;
	private Set<Sort> m_DeclaredSorts = new HashSet<>();

	protected final Map<Term, Term> m_BacktransferMapping = new HashMap<Term,Term>();
	protected final Map<Term, Term> m_TransferMapping;
	
	
	public Map<Term, Term> getBacktranferMapping() {
		return m_BacktransferMapping;
	}


	public TermTransferrer(Script script) {
		m_Script = script;
		m_TransferMapping = Collections.emptyMap();
	}
	
	public TermTransferrer(Script script, Map<Term, Term> transferMapping) {
		m_Script = script;
		m_TransferMapping = transferMapping;
	}

	@Override
	protected void convert(Term term) {
		Term mappingResult = m_TransferMapping.get(term);
		if (mappingResult != null) {
			setResult(mappingResult);
			return;
		}
		if (term instanceof TermVariable) {
			Term result = transferTermVariable((TermVariable) term);
			setResult(result);
		} else if (term instanceof ConstantTerm) {
			Sort sort = transferSort(term.getSort());
			ConstantTerm ct = (ConstantTerm) term;
			final Term result;
			if (ct.getValue() instanceof BigInteger) {
				result = m_Script.numeral((BigInteger) ct.getValue());
			} else if (ct.getValue() instanceof BigDecimal) {
				result = m_Script.decimal((BigDecimal) ct.getValue());
			} else if (ct.getValue() instanceof Rational) {
				result = ((Rational) ct.getValue()).toTerm(sort);
			} else if (ct.getValue() instanceof String) {
				String value = (String) ct.getValue();
				if (value.startsWith("#x")) {
					result = m_Script.hexadecimal(value);
				} else if (value.startsWith("#b")) {
					result = m_Script.binary(value);
				} else {
					throw new AssertionError("unexpected ConstantTerm (maybe not yet implemented)" + term);
				}
			} else {
				throw new AssertionError("unexpected ConstantTerm (maybe not yet implemented)" + term);
			}
			setResult(result);
		} else {
			super.convert(term);
		}
	}
	
	TermVariable transferTermVariable(TermVariable tv) {
//		final Term mappingResult = m_TransferMapping.get(tv);
		final TermVariable transferResult;
//		if (mappingResult == null) {
			Sort sort = transferSort(tv.getSort());
			transferResult = m_Script.variable(tv.getName(), sort);
//			m_TransferMapping.put(tv, transferResult);
//		} else {
//			transferResult = (TermVariable) mappingResult;
//		}
		return transferResult;
	}

	private Sort declareSortIfNeeded(Sort sort) {
		if (!sort.isInternal()) {
			if (!m_DeclaredSorts.contains(sort)) {
				m_Script.declareSort(sort.getName(), sort.getIndices().length);
				m_DeclaredSorts.add(sort);
			}
		}
		if (sort.getArguments().length > 0) {
			throw new UnsupportedOperationException("not yet implemented");
		}
		return m_Script.sort(sort.getName());
	}
	
	private Sort transferSort(Sort sort) {
		Sort[] arguments = transferSorts(sort.getArguments());
		BigInteger[] indices = sort.getIndices();
		Sort result;
		try {
			result = m_Script.sort(sort.getName(), indices, arguments);
		} catch (SMTLIBException e) {
			if (e.getMessage().equals("Sort " + sort.getName() + " not declared")) {
				m_Script.declareSort(sort.getName(), sort.getArguments().length);
				result = m_Script.sort(sort.getName(), arguments);
			} else {
				throw e;
			}
		}
		return result;
	}
	
	private Sort[] transferSorts(Sort[] sorts) {
		Sort[] result = new Sort[sorts.length];
		for (int i=0; i<sorts.length; i++) {
			result[i] = transferSort(sorts[i]);
		}
		return result;
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		Term result;
		try {
			BigInteger[] indices = appTerm.getFunction().getIndices();
			result = m_Script.term(appTerm.getFunction().getName(), indices, null, newArgs);
		} catch (SMTLIBException e) {
			if (e.getMessage().startsWith("Undeclared function symbol")) {
				FunctionSymbol fsymb = appTerm.getFunction();
				Sort[] paramSorts = transferSorts(fsymb.getParameterSorts());
				Sort resultSort = transferSort(fsymb.getReturnSort());
				m_Script.declareFun(fsymb.getName(), paramSorts, resultSort);
				result = m_Script.term(appTerm.getFunction().getName(), newArgs);
			} else {
				throw e;
			}
		}
		setResult(result);
	}

	@Override
	public void postConvertLet(LetTerm oldLet, Term[] newValues, Term newBody) {
		throw new UnsupportedOperationException("not yet implemented");
		//Term result = m_Script.let(vars, newValues, newBody);
	}

	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		TermVariable[] vars = new TermVariable[old.getVariables().length];
		for (int i=0; i<old.getVariables().length; i++) {
			vars[i] = transferTermVariable(old.getVariables()[i]);
		}
		Term result = m_Script.quantifier(old.getQuantifier(), vars, newBody);
		setResult(result);
	}

	@Override
	public void postConvertAnnotation(AnnotatedTerm old,
			Annotation[] newAnnots, Term newBody) {
		throw new UnsupportedOperationException("not yet implemented");
	}
	
	
	
	

}
