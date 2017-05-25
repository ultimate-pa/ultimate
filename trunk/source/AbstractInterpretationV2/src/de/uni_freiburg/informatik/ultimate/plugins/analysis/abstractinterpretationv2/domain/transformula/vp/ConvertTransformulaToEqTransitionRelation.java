package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqTransitionRelation;

public class ConvertTransformulaToEqTransitionRelation<ACTION extends IIcfgTransition<IcfgLocation>> 
		extends NonRecursive {

	private final TransFormula mTf;
	private EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> mResultConstraint;
	
	private final EqConstraintFactory<ACTION, EqNode, EqFunction> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private ManagedScript mMgdScript;
	private IUltimateServiceProvider mServices;

	/**
	 * stores intermediate results of the "recursion"
	 */
	private final ArrayDeque<EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>> mResultStack = new ArrayDeque<>();
	
	public ConvertTransformulaToEqTransitionRelation(TransFormula tf, 
			EqConstraintFactory<ACTION, EqNode, EqFunction> eqConstraintFactory, 
			EqNodeAndFunctionFactory eqNodeAndFunctionFactory) {
		mTf = tf;
		mEqConstraintFactory = eqConstraintFactory;
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;
		computeResult();
	}
	
	private void computeResult() {
		final Term transFormulaInNnf = 
				new Nnf(mMgdScript, mServices, QuantifierHandling.CRASH).transform(mTf.getFormula());
		run(new ConvertTfToEqDisjConsWalker(transFormulaInNnf));
		assert mResultStack.size() == 1;
		mResultConstraint = mResultStack.pop();
	}

//	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> getResult() {
	public EqTransitionRelation<ACTION> getResult() {
		assert mResultConstraint != null;
		return new EqTransitionRelation<>(mResultConstraint, mTf);
	}
	
	class ConvertTfToEqDisjConsWalker extends TermWalker {

		public ConvertTfToEqDisjConsWalker(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			if ("Bool".equals(term.getSort().getName())) {
				assert false : "TODO: implement";
			} else {
				assert false : "we should have caught this before, right?";
			}
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new ConvertTfToEqDisjConsWalker(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			if ("=".equals(term.getFunction().getName())) {
				handleXquality(term.getParameters()[0], term.getParameters()[1], true);
			} else if ("distinct".equals(term.getFunction())) {
				handleXquality(term.getParameters()[0], term.getParameters()[1], false);
			} else if ("!".equals(term.getFunction()) 
							&& term.getParameters()[0] instanceof ApplicationTerm
							&& "=".equals(((ApplicationTerm) term.getParameters()[0]).getFunction().getName())) {
				final ApplicationTerm innerEqualsTerm = (ApplicationTerm) term.getParameters()[0];
				handleXquality(innerEqualsTerm.getParameters()[0], innerEqualsTerm.getParameters()[1], false);
			} else if ("or".equals(term.getFunction())) {
				for (Term param : term.getParameters()) {
					walker.enqueueWalker(new ConvertTfToEqDisjConsWalker(param));
				}
				
				walker.enqueueWalker(new MakeDisjunctionWalker(term.getParameters().length));
			} else if ("and".equals(term.getFunction())) {
				for (Term param : term.getParameters()) {
					walker.enqueueWalker(new ConvertTfToEqDisjConsWalker(param));
				}
				
				walker.enqueueWalker(new MakeConjunctionWalker(term.getParameters().length));

			} else {
				assert false : "TODO";
			}
			
		}

		private void handleXquality(Term arg1, Term arg2, boolean polarity) {
			
			final EqConstraint<ACTION, EqNode, EqFunction> emptyConstraint = 
					mEqConstraintFactory.getEmptyConstraint();
			final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> emptyDisjunctiveConstraint = 
					mEqConstraintFactory.getDisjunctiveConstraint(
							Collections.singleton(emptyConstraint));
			
			if (arg1.getSort().isArraySort()) {
				// we have an array equality
				final EqFunction func1 = mEqNodeAndFunctionFactory.getOrConstructEqFunction(arg1);
				final EqFunction func2 = mEqNodeAndFunctionFactory.getOrConstructEqFunction(arg2);
				
				if (func1 == null || func2 == null) {
					// we don't track both sides of the equation --> return an empty constraint
					mResultStack.push(emptyDisjunctiveConstraint);
					return;
				}
				
				final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> newConstraint;
				if (polarity) {
					newConstraint = 
							mEqConstraintFactory.addFunctionEquality(func1, func2, emptyConstraint);
				} else {
					newConstraint = 
							mEqConstraintFactory.addFunctionDisequality(func1, func2, emptyConstraint);
				}
				
				mResultStack.push(newConstraint);
				return;
			} else {
				// we have an "normal", element equality
				final EqNode node1 = mEqNodeAndFunctionFactory.getOrConstructEqNode(arg1);
				final EqNode node2 = mEqNodeAndFunctionFactory.getOrConstructEqNode(arg2);
				
				if (node1 == null || node2 == null) {
					// we don't track both sides of the equation --> return an empty constraint
					mResultStack.push(emptyDisjunctiveConstraint);
					return;
				}


				final EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> newConstraint;
				if (polarity) {
					newConstraint = 
							mEqConstraintFactory.addEquality(node1, node2, emptyConstraint);
				} else {
					newConstraint = 
							mEqConstraintFactory.addDisequality(node1, node2, emptyConstraint);
				}

				mResultStack.push(newConstraint);
				return;
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			assert false : "TODO unlet first (or implement let handling..)";
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			throw new UnsupportedOperationException("quantifiers in Transformulas are currently not supported in the"
					+ " equality domain");
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			if ("Bool".equals(term.getSort().getName())) {
				assert false : "TODO: implement";
			} else {
				assert false : "we should have caught this before, right?";
			}
		}
		
	}
	
	class MakeDisjunctionWalker implements Walker {
		/**
		 * arity of the disjunction (i.e. how many elements to pop from result stack
		 */
		private int mArity;

		public MakeDisjunctionWalker(int arity) {
			mArity = arity;
		}

		@Override
		public void walk(NonRecursive engine) {
			final Set<EqConstraint<ACTION, EqNode, EqFunction>> allConjunctiveConstraints = new HashSet<>();
			for (int i = 0; i < mArity; i++) {
				allConjunctiveConstraints.addAll(mResultStack.pop().getConstraints());
			}
			mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(allConjunctiveConstraints));
		}
		
	}
	
	class MakeConjunctionWalker implements Walker {
		/**
		 * arity of the disjunction (i.e. how many elements to pop from result stack
		 */
		private int mArity;

		public MakeConjunctionWalker(int arity) {
			mArity = arity;
		}

		@Override
		public void walk(NonRecursive engine) {
			final ArrayList<EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>> conjuncts = new ArrayList<>();
			for (int i = 0; i < mArity; i++) {
				conjuncts.add(mResultStack.pop());
			}
			mResultStack.push(mEqConstraintFactory.conjoinDisjunctiveConstraints(conjuncts));
		}
	}
}
