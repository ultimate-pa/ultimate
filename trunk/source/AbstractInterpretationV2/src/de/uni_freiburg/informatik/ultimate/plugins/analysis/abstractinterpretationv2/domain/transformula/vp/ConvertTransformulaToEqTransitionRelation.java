/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqConstraintFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqDisjunctiveConstraint;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.EqTransitionRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
public class ConvertTransformulaToEqTransitionRelation<ACTION extends IIcfgTransition<IcfgLocation>>
		extends NonRecursive {

	private final TransFormula mTf;
	private EqDisjunctiveConstraint<ACTION, EqNode> mResultConstraint;

	private final EqConstraintFactory<ACTION, EqNode> mEqConstraintFactory;
	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;

	private final VPDomainPreanalysis mPreAnalysis;

	private final Term mTrueTerm;
	private final Term mFalseTerm;

	/**
	 * stores intermediate results of the "recursion"
	 */
	private final ArrayDeque<EqDisjunctiveConstraint<ACTION, EqNode>> mResultStack = new ArrayDeque<>();

	public ConvertTransformulaToEqTransitionRelation(final TransFormula tf,
			final EqConstraintFactory<ACTION, EqNode> eqConstraintFactory,
			final EqNodeAndFunctionFactory eqNodeAndFunctionFactory, final VPDomainPreanalysis preAnalysis) {
		mTf = tf;
		mEqConstraintFactory = eqConstraintFactory;
		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;

		mPreAnalysis = preAnalysis;
		mMgdScript = preAnalysis.getManagedScript();
		mServices = preAnalysis.getServices();

		mMgdScript.lock(this);
		mTrueTerm = mMgdScript.term(this, "true");
		mFalseTerm = mMgdScript.term(this, "false");
		mMgdScript.unlock(this);

		computeResult();
	}

	private void computeResult() {
		final Term transFormulaInNnf =
				new NnfTransformer(mMgdScript, mServices, QuantifierHandling.CRASH).transform(mTf.getFormula());

		final StoreChainSquisher scs = new StoreChainSquisher();
		final List<Term> conjunction = new ArrayList<>();
		conjunction.add(scs.transform(transFormulaInNnf));
		conjunction.addAll(scs.getReplacementEquations());
		final Term transFormulaWithSquishedStoreChains = SmtUtils.and(mMgdScript.getScript(), conjunction);

		run(new ConvertTfToEqDisjConsWalker(transFormulaWithSquishedStoreChains));

		assert mResultStack.size() == 1;
		final EqDisjunctiveConstraint<ACTION, EqNode> processedTf = mResultStack.pop();
		mResultConstraint = processedTf.projectExistentially(scs.getReplacementTermVariables());

		assert transformulaImpliesResultConstraint();
	}

	private boolean transformulaImpliesResultConstraint() {
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		final Map<Term, Term> sub = new HashMap<>();
		for (final TermVariable tv : mTf.getFormula().getFreeVars()) {

			final String constName = "tf2EqTR_" + tv.getName();
			mMgdScript.declareFun(this, constName, new Sort[0], tv.getSort());
			sub.put(tv, mMgdScript.term(this, constName));
		}

		final Substitution substitution = new Substitution(mMgdScript, sub);
		final Term tfSubs = substitution.transform(mTf.getFormula());
		mMgdScript.assertTerm(this, tfSubs);
		final Term eqConsSubs = Util.not(mMgdScript.getScript(),
				substitution.transform(mResultConstraint.getTerm(mMgdScript.getScript())));
		mMgdScript.assertTerm(this, eqConsSubs);

		final LBool result = mMgdScript.checkSat(this);
		mMgdScript.pop(this, 1);
		mMgdScript.unlock(this);
		if (result != LBool.UNSAT) {
			assert false;
		}
		return result == LBool.UNSAT;
	}

	public EqTransitionRelation<ACTION> getResult() {
		assert mResultConstraint != null;
		return new EqTransitionRelation<>(mResultConstraint, mTf);
	}

	class ConvertTfToEqDisjConsWalker extends TermWalker {


		public ConvertTfToEqDisjConsWalker(final Term term) {
			super(term);
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			if ("Bool".equals(term.getSort().getName())) {
				assert false : "TODO: implement";
			} else {
				assert false : "we should have caught this before, right?";
			}
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			walker.enqueueWalker(new ConvertTfToEqDisjConsWalker(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			if ("=".equals(term.getFunction().getName())) {
				handleXquality(term.getParameters()[0], term.getParameters()[1], true);
			} else if ("distinct".equals(term.getFunction().getName())) {
				handleXquality(term.getParameters()[0], term.getParameters()[1], false);
			} else if ("not".equals(term.getFunction().getName())
					&& SmtUtils.isFunctionApplication(term.getParameters()[0], "=")) {
				final ApplicationTerm innerEqualsTerm = (ApplicationTerm) term.getParameters()[0];
				handleXquality(innerEqualsTerm.getParameters()[0], innerEqualsTerm.getParameters()[1], false);
			} else if ("not".equals(term.getFunction().getName())) {
				handleBooleanTerm(term.getParameters()[0], false);
			} else if ("or".equals(term.getFunction().getName())) {
				walker.enqueueWalker(new MakeDisjunctionWalker(term.getParameters().length));

				for (final Term param : term.getParameters()) {
					walker.enqueueWalker(new ConvertTfToEqDisjConsWalker(param));
				}

			} else if ("and".equals(term.getFunction().getName())) {
				walker.enqueueWalker(new MakeConjunctionWalker(term.getParameters().length));

				for (final Term param : term.getParameters()) {
					walker.enqueueWalker(new ConvertTfToEqDisjConsWalker(param));
				}


			} else if ("false".equals(term.getFunction().getName())) {
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.emptySet()));
			} else if ("true".equals(term.getFunction().getName())) {
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.singleton(mEqConstraintFactory.getEmptyConstraint())));
			} else {
				// we don't recognize this function symbol -- overapproximating its effects by "top"
				// TODO: perhaps we could make some checks here if it is trivially bottom or something like that..
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.singleton(mEqConstraintFactory.getEmptyConstraint())));
			}

		}

		private void handleBooleanTerm(final Term term, final boolean polarity) {
			assert "Bool".equals(term.getSort().getName());
			final EqConstraint<ACTION, EqNode> emptyConstraint =
					mEqConstraintFactory.getEmptyConstraint();
			final EqNode tvNode = mEqNodeAndFunctionFactory.getOrConstructNode(term);
			if (polarity) {
				final EqNode trueNode = mEqNodeAndFunctionFactory.getOrConstructNode(mTrueTerm);
				final EqConstraint<ACTION, EqNode> tvEqualsTrue =
						mEqConstraintFactory.addEqualityFlat(tvNode, trueNode, emptyConstraint);
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.singleton(tvEqualsTrue)));
			} else {
				final EqNode falseNode = mEqNodeAndFunctionFactory.getOrConstructNode(mFalseTerm);
				final EqConstraint<ACTION, EqNode> tvEqualsFalse =
						mEqConstraintFactory.addEqualityFlat(tvNode, falseNode, emptyConstraint);
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(
						Collections.singleton(tvEqualsFalse)));
			}
		}

		private void handleXquality(final Term arg1, final Term arg2, final boolean polarity) {

			final EqConstraint<ACTION, EqNode> emptyConstraint =
					mEqConstraintFactory.getEmptyConstraint();
			final EqDisjunctiveConstraint<ACTION, EqNode> emptyDisjunctiveConstraint =
					mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(emptyConstraint));

			if (arg1.getSort().isArraySort()) {
				// we have an array equality

				if (!isFunctionTracked(arg1) || !isFunctionTracked(arg2)) {
					// we don't track both sides of the equation --> return an empty constraint
					mResultStack.push(emptyDisjunctiveConstraint);
					return;
				}

//				MultiDimensionalStore mds;
				ApplicationTerm storeTerm;
				EqNode simpleArray;
				EqNode otherSimpleArray;

				if (SmtUtils.isFunctionApplication(arg1, "store")) {
					assert !SmtUtils.isFunctionApplication(arg2, "store");
//					mds = new MultiDimensionalStore(arg1);
					storeTerm = (ApplicationTerm) arg1;
//					simpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(arg2);
					simpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(arg2);
//					assert !SmtUtils.isFunctionApplication(mds.getArray(), "store");
//					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(mds.getArray());
					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(storeTerm.getParameters()[0]);
				} else if (SmtUtils.isFunctionApplication(arg2, "store")) {
					assert !SmtUtils.isFunctionApplication(arg1, "store");
//					mds = new MultiDimensionalStore(arg2);
					storeTerm = (ApplicationTerm) arg2;
//					simpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(arg1);
					simpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(arg1);
//					assert !SmtUtils.isFunctionApplication(mds.getArray(), "store");
//					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(mds.getArray());
					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(storeTerm.getParameters()[0]);
				} else {
//					mds = null;
					storeTerm = null;
//					simpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(arg1);
					simpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(arg1);
//					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructFunction(arg2);
					otherSimpleArray = mEqNodeAndFunctionFactory.getOrConstructNode(arg2);
				}



				final EqConstraint<ACTION, EqNode> newConstraint;
				if (polarity) {
					if (storeTerm == null) {
						// we have a strong equivalence
//						newConstraint = mEqConstraintFactory.addFunctionEqualityFlat(simpleArray,
						newConstraint = mEqConstraintFactory.addEqualityFlat(simpleArray,
								otherSimpleArray, emptyConstraint);
					} else {

//						final List<EqNode> storeIndex = mds.getIndex().stream()
//								.map(mEqNodeAndFunctionFactory::getOrConstructNode)
//								.collect(Collectors.toList());
						final EqNode storeIndex = mEqNodeAndFunctionFactory.getOrConstructNode(
								storeTerm.getParameters()[1]);
//						final EqNode storeValue = mEqNodeAndFunctionFactory.getOrConstructNode(mds.getValue());
						final EqNode storeValue = mEqNodeAndFunctionFactory.getOrConstructNode(
								storeTerm.getParameters()[2]);

						// we have a weak equivalence ..
						final EqConstraint<ACTION, EqNode> intermediateConstraint =
								mEqConstraintFactory.addWeakEquivalence(simpleArray, otherSimpleArray, storeIndex,
										emptyConstraint);
						// .. and an equality on the stored position
//						final Term selectTerm = SmtUtils.multiDimensionalSelect(mMgdScript.getScript(),
//								simpleArray.getTerm(), mds.getIndex());
						mMgdScript.lock(this);
						final Term selectTerm = mMgdScript.term(this, "select", simpleArray.getTerm(),
								storeTerm.getParameters()[1]);
						mMgdScript.unlock(this);
						final EqNode selectEqNode = mEqNodeAndFunctionFactory.getOrConstructNode(selectTerm);
						newConstraint = mEqConstraintFactory.addEqualityFlat(selectEqNode, storeValue,
								intermediateConstraint);
					}
				} else {
//					if (mds == null) {
					if (storeTerm == null) {
//						newConstraint = mEqConstraintFactory.addFunctionDisequalityFlat(simpleArray,
						newConstraint = mEqConstraintFactory.addDisequalityFlat(simpleArray, otherSimpleArray,
								emptyConstraint);
					} else {
						// "true" is only marginally than the negation of a -- i -- b /\ a[i] = x ..
						newConstraint = emptyConstraint;
					}
				}

				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(newConstraint)));
				return;
			} else {
				// we have an "normal", element equality

				if (!isElementTracked(arg1) || !isElementTracked(arg2)) {
					// we don't track both sides of the equation --> return an empty constraint
					mResultStack.push(emptyDisjunctiveConstraint);
					return;
				}

				final EqNode node1 = mEqNodeAndFunctionFactory.getOrConstructNode(arg1);
				final EqNode node2 = mEqNodeAndFunctionFactory.getOrConstructNode(arg2);

				final EqConstraint<ACTION, EqNode> newConstraint;
				if (polarity) {
					newConstraint =
							mEqConstraintFactory.addEqualityFlat(node1, node2, emptyConstraint);
				} else {
					newConstraint =
							mEqConstraintFactory.addDisequalityFlat(node1, node2, emptyConstraint);
				}
				mResultStack.push(mEqConstraintFactory.getDisjunctiveConstraint(Collections.singleton(newConstraint)));
				return;
			}
		}

		private boolean isElementTracked(final Term term) {
			return mPreAnalysis.isElementTracked(term, mTf);
		}

		private boolean isFunctionTracked(final Term term) {
			return mPreAnalysis.isArrayTracked(term, mTf.getInVars(), mTf.getOutVars());
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			assert false : "TODO unlet first (or implement let handling..)";
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			throw new UnsupportedOperationException("quantifiers in Transformulas are currently not supported in the"
					+ " equality domain");
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			if ("Bool".equals(term.getSort().getName())) {
				handleBooleanTerm(term, true);
				return;
			}
			throw new AssertionError("we should have caught this before, right?");
		}
	}

	class MakeDisjunctionWalker implements Walker {
		/**
		 * arity of the disjunction (i.e. how many elements to pop from result stack
		 */
		private final int mArity;

		public MakeDisjunctionWalker(final int arity) {
			mArity = arity;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final Set<EqConstraint<ACTION, EqNode>> allConjunctiveConstraints = new HashSet<>();
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
		private final int mArity;

		public MakeConjunctionWalker(final int arity) {
			mArity = arity;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ArrayList<EqDisjunctiveConstraint<ACTION, EqNode>> conjuncts = new ArrayList<>();
			for (int i = 0; i < mArity; i++) {
				conjuncts.add(mResultStack.pop());
			}
			mResultStack.push(mEqConstraintFactory.conjoinDisjunctiveConstraints(conjuncts));
		}
	}

	/**
	 * Transforms a given Term into an equivalent term where every atom contains at most one application of the store
	 * function.
	 * (Multidimensional store terms count as one application.)
	 *
	 * Right now the result is not equivalent. However it is equivalent to the original when conjoined with the
	 * equalities from getReplacementEquations, and the replacement variables are existentially quantified.
	 *
	 * removes the following from the formula
	 * <ul>
	 *  <li> store chains, i.e., every (store s i x) where s is another store term is eliminated
	 *  <li> multidimensional stores, explicit or not, i.e., every (store s i x) where x is another store term is
	 *  	eliminated
	 *  <li> stores on both sides of an equality, for example the term (= (store a i x) (store b j y)) would be
	 *     transformed such that it contains at most one store
	 *  <li> stores inside selects, for example (select (store a i x) j) would be transformed
	 * </ul>
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	class StoreChainSquisher extends TermTransformer {

		Script mScript = mMgdScript.getScript();

		private final List<Term> mReplacementEquations = new ArrayList<>();

//		private final BidirectionalMap<TermVariable, Term> mReplacementTvToReplacedTerm = new BidirectionalMap<>();
		private final Map<Term, TermVariable> mReplacedTermToReplacementTv = new BidirectionalMap<>();

		public Collection<Term> getReplacementEquations() {
			final Collection<Term> result = new ArrayList<>();
			for (final Entry<Term, TermVariable> en : mReplacedTermToReplacementTv.entrySet()) {
				final Term replacementEquation = SmtUtils.binaryEquality(mScript, en.getValue(), en.getKey());
				result.add(replacementEquation);
			}
			return result;
		}

		public Collection<TermVariable> getReplacementTermVariables() {
			return new ArrayList<>(mReplacedTermToReplacementTv.values());
		}

		@Override
		protected void convert(final Term term) {
			if (SmtUtils.isFunctionApplication(term, "store")) {
				enqueueWalker(new SquishStoreWalker((ApplicationTerm) term));
				pushTerms(((ApplicationTerm) term).getParameters());
			} else if (SmtUtils.isFunctionApplication(term, "select")) {
				enqueueWalker(new SquishStoreInsideSelectWalker());
				pushTerms(((ApplicationTerm) term).getParameters());
			} else if (SmtUtils.isFunctionApplication(term, "=")
					&& SmtUtils.isFunctionApplication(((ApplicationTerm) term).getParameters()[0], "store")
					&& SmtUtils.isFunctionApplication(((ApplicationTerm) term).getParameters()[1], "store")) {
				enqueueWalker(new SquishFirstOfTwoArgumentStoresWalker((ApplicationTerm) term));
				assert ((ApplicationTerm) term).getParameters().length == 2;
				pushTerms(((ApplicationTerm) term).getParameters());
			} else {
				super.convert(term);
			}
		}

		/**
		 * Obtains the replacement TermVariable for the given term.
		 *
		 * If the same term has been replaced before, the same variable is returned.
		 *
		 * The map that is used to manage the replacement variables will also be used to return the of equations between
		 * the replacement variables and their corresponding terms.
		 *
		 * @param term
		 * @return
		 */
		private TermVariable getReplacementTv(final Term term) {
			TermVariable res = mReplacedTermToReplacementTv.get(term);
			if (res == null) {
				res = mMgdScript.constructFreshTermVariable("rep", term.getSort());
				mReplacedTermToReplacementTv.put(term, res);
			}
			return res;
		}

		/**
		 * only used to make getConverted visible to the walker.
		 *
		 * @param oldArgs
		 * @return
		 */
		Term[] getConvertedArray(final Term[] oldArgs) {
			return getConverted(oldArgs);
		}

		class SquishFirstOfTwoArgumentStoresWalker implements Walker {

			private final ApplicationTerm mAppTerm;

			public SquishFirstOfTwoArgumentStoresWalker(final ApplicationTerm term) {
				mAppTerm = term;
				assert term.getParameters().length == 2;
			}

			@Override
			public void walk(final NonRecursive engine) {

				final Term arg2 = getConverted();
				final Term arg1 = getConverted();
				assert SmtUtils.isFunctionApplication(arg1, "store");
				assert SmtUtils.isFunctionApplication(arg2, "store");

				final Term innerStoreTerm = arg1;
				final TermVariable replacmentTv = getReplacementTv(innerStoreTerm);
				setResult(mScript.term(mAppTerm.getFunction().getName(), replacmentTv, arg2));
			}

		}

		/**
		 * removes stores inside selects
		 */
		class SquishStoreInsideSelectWalker implements Walker {

			@Override
			public void walk(final NonRecursive engine) {

				final Term arg2 = getConverted();
				final Term arg1 = getConverted();

				if (SmtUtils.isFunctionApplication(arg1, "store")) {
					final Term innerStoreTerm = arg1;
					final TermVariable replacmentTv = getReplacementTv(innerStoreTerm);
					setResult(mScript.term("select", replacmentTv, arg2));
				} else {
					setResult(mScript.term("select", arg1, arg2));
				}
			}

		}

		/**
		 * removes store chains
		 */
		class SquishStoreWalker implements Walker {
			/** the application term to convert. */
			private final ApplicationTerm mAppTerm;

			public SquishStoreWalker(final ApplicationTerm term) {
				mAppTerm = term;
			}

			@Override
			public void walk(final NonRecursive engine) {
				final StoreChainSquisher transformer = (StoreChainSquisher) engine;
				/* collect args and check if they have been changed */
				final Term[] oldArgs = mAppTerm.getParameters();
				final Term[] newArgs = transformer.getConvertedArray(oldArgs);
				assert newArgs.length == 3;

//				final Term innerStoreAtArrayPosition;
//				final Term innerStoreAtValuePosition;

				final Term replacedArray;
				if (SmtUtils.isFunctionApplication(newArgs[0], "store")) {
					replacedArray =  getReplacementTv(newArgs[0]);
				} else {
					replacedArray = newArgs[0];
				}

				final Term replacedValue;
				if (SmtUtils.isFunctionApplication(newArgs[2], "store")) {
					replacedValue =  getReplacementTv(newArgs[2]);
				} else {
					replacedValue = newArgs[2];
				}

				setResult(mScript.term("store", replacedArray, newArgs[1], replacedValue));

//				if (SmtUtils.isFunctionApplication(newArgs[0], "store")) {
//					final Term innerStoreTerm = newArgs[0];
//					final TermVariable replacmentTv = getReplacementTv(innerStoreTerm);
//					setResult(mScript.term("store", replacmentTv, newArgs[1], newArgs[2]));
//				} else {
//					// the array argument of the store that we enqueued this walker for is a variable
//					// --> we do no further transformation
//					setResult(mScript.term("store", newArgs[0], newArgs[1], newArgs[2]));
//				}
			}

			@Override
			public String toString() {
				return "StoreTermSquisher: " + mReplacementEquations;
			}

		}
	}
}
