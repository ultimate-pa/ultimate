/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * An evaluator for terms against the current model.
 * @author Juergen Christ
 */
public class ModelEvaluator extends NonRecursive {
	
	/**
	 * A helper to enqueue either the true or the false branch of an ite.
	 * @author Juergen Christ
	 */
	private static class ITESelector implements Walker {

		private final ApplicationTerm m_Ite;
		
		public ITESelector(ApplicationTerm ite) {
			m_Ite = ite;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			ModelEvaluator eval = (ModelEvaluator) engine;
			ExecTerm execSelector = eval.getConverted();
			if (execSelector.isUndefined())
				eval.setResult(
						new Undefined(m_Ite.getFunction().getReturnSort()));
			else {
				boolean selector = 
						execSelector.toSMTLIB(m_Ite.getTheory(), null) == 
						m_Ite.getTheory().TRUE;
				eval.pushTerm(m_Ite.getParameters()[selector ? 1 : 2]);
			}
		}
		
	}
	
	private static class AddToCache implements Walker {
		
		private Term m_Term;
		public AddToCache(Term t) {
			m_Term = t;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			ModelEvaluator eval = (ModelEvaluator) engine;
			eval.m_Cache.put(m_Term, eval.m_Evaluated.peekLast());
		}
		
	}
	
	private static class Evaluator implements Walker {

		private ApplicationTerm m_Term;
		public Evaluator(ApplicationTerm term) {
			m_Term = term;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			ModelEvaluator eval = (ModelEvaluator) engine;
			ExecTerm[] args = eval.getConvertedArgs(
					m_Term.getParameters().length);
			eval.setResult(eval.m_Model.getValue(m_Term.getFunction(), args));
		}
		
	}
	
	private static class CachedEvaluator extends TermWalker {

		public CachedEvaluator(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker) {
			ModelEvaluator eval = (ModelEvaluator) walker;
			ExecTerm cached = eval.m_Cache.get(m_Term);
			if (cached != null)
				eval.setResult(cached);
			else {
				eval.enqueueWalker(new AddToCache(m_Term));
				super.walk(walker);
			}
		}
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			ModelEvaluator eval = (ModelEvaluator) walker;
			if (term.getValue() instanceof BigInteger) {
				Rational rat = Rational.valueOf(
						(BigInteger) term.getValue(), BigInteger.ONE); 
				eval.setResult(new Value(rat.toTerm(term.getSort())));
			} else if (term.getValue() instanceof BigDecimal) {
				BigDecimal decimal = (BigDecimal) term.getValue();
				Rational rat;
				if (decimal.scale() <= 0) {
					BigInteger num = decimal.toBigInteger();
					rat = Rational.valueOf(num, BigInteger.ONE);
				} else {
					BigInteger num = decimal.unscaledValue();
					BigInteger denom = BigInteger.TEN.pow(decimal.scale());
					rat = Rational.valueOf(num, denom);
				}
				eval.setResult(new Value(rat.toTerm(term.getSort())));
			} else
				eval.setResult(new Value(term));
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			ModelEvaluator eval = (ModelEvaluator) walker;
			eval.enqueueWalker(new CachedEvaluator(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			ModelEvaluator eval = (ModelEvaluator) walker;
			if (term.getFunction().getName().equals("ite")) {
				eval.enqueueWalker(new ITESelector(term));
				eval.pushTerm(term.getParameters()[0]);
			} else {
				eval.enqueueWalker(new Evaluator(term));
				eval.pushTerms(term.getParameters());			
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new InternalError(
					"Let-Terms should not be in model evaluation");
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			throw new SMTLIBException(
					"Quantifiers not supported in model evaluation");
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			throw new SMTLIBException("Terms to evaluate must be closed");
		}
		
	}
	
	HashMap<Term, ExecTerm> m_Cache = new HashMap<Term, ExecTerm>();
	
	ArrayDeque<ExecTerm> m_Evaluated = new ArrayDeque<ExecTerm>();
	
	private ExecTerm getConverted() {
		return m_Evaluated.removeLast();
	}
	
	public void pushTerms(Term[] terms) {
		for (int i = terms.length-1; i >= 0; i--)
			pushTerm(terms[i]);
	}

	public ExecTerm[] getConvertedArgs(int length) {
		ExecTerm[] result = new ExecTerm[length];
		while (--length >= 0)
			result[length] = getConverted();
		return result;
	}

	public void pushTerm(Term term) {
		enqueueWalker(new CachedEvaluator(term));
	}

	private void setResult(ExecTerm t) {
		m_Evaluated.addLast(t);
	}
	
	private final Model m_Model;

	public ModelEvaluator(Model model) {
		m_Model = model;
	}

	public Term evaluate(Term input) {
		try {
			run(new CachedEvaluator(input));
			return getConverted().toSMTLIB(input.getTheory(), null);
		} finally {
			reset();
		}
	}
	
}
