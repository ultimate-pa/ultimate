/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link VPDomainState} for the given Statement.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPDomainStatementProcessor extends NonRecursive {

	private VPDomainState mOldState;
	private List<VPDomainState> mNewState;
	private VPDomainState mCurrentNewState;
	
	private final Set<ApplicationTerm> termSet = new HashSet<>();

	private final IUltimateServiceProvider mServices;

	IEvaluatorFactory<Values, VPDomainState, CodeBlock, IBoogieVar> mEvaluatorFactory;
	ExpressionEvaluator<Values, VPDomainState, CodeBlock, IBoogieVar> mExpressionEvaluator;

	private String mLhsVariable;

	protected VPDomainStatementProcessor(IUltimateServiceProvider services) {
		mServices = services;
	}

	protected List<VPDomainState> process(VPDomainState oldState, CodeBlock transition) {

		assert oldState != null;
		assert transition != null;

		mOldState = oldState;
		mNewState = new ArrayList<>();
		mCurrentNewState = oldState.copy();
		mCurrentNewState.getPtrReadintMap().clear();
		
		mLhsVariable = null;

		// Process the current statement and alter mNewState
		termSet.addAll(processTerm(transition.getTransitionFormula().getFormula()));

		return mNewState;
	}

	private class  VPDomainTermWalker extends TermWalker {
		VPDomainTermWalker(Term term) { super(term); }
		
		@Override
		public void walk(NonRecursive walker) {
			if (m_Visited.contains(getTerm())) {
				// do nothing
			} else {
				m_Visited.add(getTerm());
				super.walk(walker);
			}
		}
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// do nothing
		}
		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new VPDomainTermWalker(term.getSubterm()));
		}
		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			if (term.getFunction().getName() == "=") {
				m_Result.add(term);
			}
			for (Term t : term.getParameters()) {
				walker.enqueueWalker(new VPDomainTermWalker(t));
			}
		}
		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new UnsupportedOperationException();
		}
		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new VPDomainTermWalker(term.getSubformula()));
		}
		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// do nothing
		}
	}
	

	private Set<ApplicationTerm> m_Result;
	private Set<Term> m_Visited;
	
	public Set<ApplicationTerm> processTerm(Term term) {
		if (term == null) {
			throw new NullPointerException();
		}
		m_Visited = new HashSet<>();
		m_Result = new HashSet<ApplicationTerm>();
		run(new VPDomainTermWalker(term));
		m_Visited = null;
		return m_Result;
	}
	
	
//	protected void visit(HavocStatement statement) {
//		
//		final VPDomainState retState = mCurrentNewState.copy();
//		Set<Expression> exprSet;
//		
//		final VariableLHS[] vars = statement.getIdentifiers();
//		for (final VariableLHS var : vars) {
//			
//			if (retState.getExpressionMap().containsKey(var.getIdentifier())) {
//				retState.getExpressionMap().clear();
//				retState.getExpressionMap().get(var.getIdentifier()).addAll(retState.getExprSet());
//			} else {
//				exprSet = new HashSet<Expression>();
//				exprSet.addAll(retState.getExprSet());
//				retState.getExpressionMap().put(var.getIdentifier(), exprSet);
//			}
//		}
//		mNewState.add(retState);
//	}
//
//	protected void visit(AssignmentStatement statement) {
////		mEvaluatorFactory = new VPEvaluatorFactory(mServices);
//		
//		final LeftHandSide[] lhs = statement.getLhs();
//		final Expression[] rhs = statement.getRhs();
//		final VPDomainState retState = mCurrentNewState.copy();
//		
//		for (int i = 0; i < lhs.length; i++) {
////			mExpressionEvaluator = new ExpressionEvaluator<Values, VPDomainState, CodeBlock, IBoogieVar>();
//
//			assert mLhsVariable == null;
//			processLeftHandSide(lhs[i]);	// determine mLhsVariable
//			
//			assert mLhsVariable != null;
//			final String varName = mLhsVariable;
//			mLhsVariable = null;
//
//			processExpression(rhs[i]);
////			assert mExpressionEvaluator.isFinished();
//			
//			retState.getExprSet().add(rhs[i]);
//			if (retState.getVarExprMap().containsKey(varName)) {
//				retState.getVarExprMap().get(varName).clear();
//				retState.getVarExprMap().get(varName).add(rhs[i]);
//			} else {
//				Set<Expression> exprSet = new HashSet<Expression>();
//				exprSet.add(rhs[i]);
//				retState.getVarExprMap().put(varName, exprSet);
//			}
//			mCurrentNewState = retState.copy();
//		}
//		mNewState.add(retState);
//	}
	
}
