/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.NonCoreBooleanSubTermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierSequence.QuantifiedVariables;

/**
 * Transform a Term into prenex normal form (quantifiers outside).
 * 
 * @author Matthias Heizmann
 * 
 */
public class PrenexNormalForm extends TermTransformer {
	
	private final Script m_Script;
	private final IFreshTermVariableConstructor m_FreshTermVariableConstructor;

	public PrenexNormalForm(Script script, 
			IFreshTermVariableConstructor freshTermVariableConstructor) {
		m_Script = script;
		m_FreshTermVariableConstructor = freshTermVariableConstructor;
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		if (NonCoreBooleanSubTermTransformer.isCoreBoolean(appTerm)) {
			String fun = appTerm.getFunction().getName();
			if (fun.equals("=")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else if (fun.equals("not")) {
				final Term result = pullQuantifiersNot(newArgs);
				setResult(result);
			} else if (fun.equals("and")) {
				final Term result = pullQuantifiers(appTerm, newArgs);
				setResult(result);
			} else if (fun.equals("or")) {
				final Term result = pullQuantifiers(appTerm, newArgs);
				setResult(result);
			} else if (fun.equals("=>")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else if (fun.equals("xor")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else if (fun.equals("distinct")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else if (fun.equals("ite")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else {
				throw new AssertionError("unknown core boolean term");
			}
		} else {
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}

	private Term pullQuantifiersNot(Term[] newArgs) {
		assert newArgs.length == 1 : "no not";
		final Term notArg = newArgs[0];
		final QuantifierSequence quantifierSequence = new QuantifierSequence(m_Script);
		final Term inner = quantifierSequence.extractQuantifiers(notArg, true, m_FreshTermVariableConstructor);
		final List<QuantifiedVariables> qVarSeq = quantifierSequence.getQuantifiedVariableSequence();
		Term result = Util.not(m_Script, inner);
		for (int i = qVarSeq.size()-1; i>=0; i--) {
			final QuantifiedVariables quantifiedVars = qVarSeq.get(i);
			final int resultQuantifier = (quantifiedVars.getQuantifier() + 1) % 2;
			result = SmtUtils.quantifier(m_Script, resultQuantifier, 
					quantifiedVars.getVariables(), result, m_FreshTermVariableConstructor);
		}
		return result;
	}

	private Term pullQuantifiers(ApplicationTerm appTerm, Term[] newArgs) {
		QuantifierSequence quantifierSequence = new QuantifierSequence(m_Script);
		Term[] resultArgs = new Term[newArgs.length];
		for (int i=0; i<newArgs.length; i++) {
			Term resultArg = newArgs[i];
			resultArgs[i] = quantifierSequence.extractQuantifiers(resultArg, true, m_FreshTermVariableConstructor);
		}
		Term resultBody = m_Script.term(appTerm.getFunction().getName(), resultArgs);
		Term result = quantifierSequence.prependQuantifierSequence(resultBody);
		return result;
	}

	@Override
	public void postConvertLet(LetTerm oldLet, Term[] newValues, Term newBody) {
		throw new UnsupportedOperationException("not yet implemented, we need term without let");
	}
	
	

	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		if (SmtUtils.isQuantifiedFormulaWithSameQuantifier(old.getQuantifier(), newBody) != null) {
			final Term result = SmtUtils.quantifier(m_Script, old.getQuantifier(), 
					Arrays.asList(old.getVariables()), newBody, m_FreshTermVariableConstructor);
			setResult(result);
		} else {
			super.postConvertQuantifier(old, newBody);
		}
	}

	@Override
	public void postConvertAnnotation(AnnotatedTerm old, Annotation[] newAnnots, Term newBody) {
		setResult(newBody);
//		Term result = m_Script.annotate(newBody, newAnnots);
//		setResult(result);
//		throw new UnsupportedOperationException("not yet implemented: annotations");
	}
}
