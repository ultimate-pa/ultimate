/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Literal.Polarity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.XJunction.AtomAndNegationException;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Common abstract superclass of Cnf and Dnf. In order to understand the variable names and the documentation replace
 * "outer" by "conjunct" and "inner" by "disjunct" for CNF, and replace "outer" by "disjunct" and "inner" by "conjunct"
 * for DNF. In documentation we use the Greek letter iota 'ι' to denote the inner connective and we use the Greek letter
 * omikron 'o' to denote the outer connective.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public abstract class XnfTransformer extends NnfTransformer {

	public static final boolean POSET_SIMPLIFICATION = true;

	public XnfTransformer(final ManagedScript script, final IUltimateServiceProvider services,
			final boolean omitSoundnessCheck) {
		super(script, services, QuantifierHandling.IS_ATOM, omitSoundnessCheck);
	}

	public XnfTransformer(final ManagedScript script, final IUltimateServiceProvider services,
			final boolean omitSoundnessCheck, final Function<Integer, Boolean> funAbortIfExponential) {
		super(script, services, QuantifierHandling.IS_ATOM, omitSoundnessCheck, funAbortIfExponential);
	}

	protected abstract class XnfTransformerHelper extends NnfTransformerHelper {

		protected XnfTransformerHelper(final IUltimateServiceProvider services) {
			super(services);
		}

		public abstract String innerConnectiveSymbol();

		public abstract String outerConnectiveSymbol();

		public abstract String innerJunctionName();

		public abstract String outerJunctionName();

		public abstract Term innerConnective(Script script, List<Term> params);

		public abstract Term outerConnective(Script script, List<Term> params);

		public abstract Term[] getOuterJuncts(Term term);

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			final String functionSymbolName = appTerm.getFunction().getName();
			Term result;
			if (functionSymbolName.equals(innerConnectiveSymbol())) {
				// case where the connective of the formula is inner connective
				// of the normal form.
				final Term[] resOuterJuncts = applyDistributivityAndOr(newArgs);
				result = outerConnective(mScript, Arrays.asList(resOuterJuncts));
			} else if (functionSymbolName.equals(outerConnectiveSymbol())) {
				result = outerConnective(mScript, Arrays.asList(newArgs));
			} else {
				throw new AssertionError();
			}
			setResult(result);
		}

		/**
		 * Uses Distributivity to transform an innerJunction (given as an array of innerJuncts) to an equivalent
		 * outerJunction (given as an array of outerJuncts). E.g., ((A o B) ι (C ο D)) is transformed to (A ι C) o (A ι
		 * D) o (B ι C) o (B ι D) In order to keep the result small optimizations are applied.
		 *
		 * @param inputInnerJunction
		 * @return
		 */
		private Term[] applyDistributivityAndOr(final Term[] inputInnerJunction) {

			final ResultInnerJunctions first;

			try {
				first = new ResultInnerJunctions(convertInnerJunctionOfOuterJunctionsToSet(inputInnerJunction));
			} catch (final AtomAndNegationException e1) {
				// innerJunctionOfOuterJunctions contains the singleton {φ}
				// and the singleton {¬φ}.
				// Hence the result is equivalent to the annihilator of the
				// innerJunction resp. the neutral element of the
				// outerJunction (true for ∧, false for ∨)
				return new Term[0];
			}

			final int inputSize = first.numberOfUnprocessedOuterJunctions();
			if (inputSize > 5) {
				if (mFunAbortIfExponential.apply(inputSize)) {
					mLogger.warn("aborting because of expected exponential blowup for input size " + inputSize);
					throw new AbortBeforeBlowup();
				}
				mLogger.warn("expecting exponential blowup for input size " + inputSize);
			}

			// iteratively apply distributivity until we have a set of innerJunctions.
			final Set<XJunction> resOuterJunction = new HashSet<>();
			final Deque<ResultInnerJunctions> todoStack = new ArrayDeque<>();
			todoStack.add(first);
			while (!todoStack.isEmpty()) {
				final ResultInnerJunctions top = todoStack.pop();
				if (top.isProcessedToInnerJunction()) {
					resOuterJunction.add(top.getInnerJunction());
				} else {
					todoStack.addAll(top.processOneOuterJunction());
				}
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(),
							"transforming " + inputSize + " " + innerJunctionName());
				}
			}

			final Set<XJunction> elems = simplifyWithPosetMinimalElements(resOuterJunction);

			// Construct terms.
			final Term[] resInnerTerms = new Term[elems.size()];
			int i = 0;
			for (final XJunction resInnerSet : elems) {
				resInnerTerms[i] = innerConnective(mScript, resInnerSet.toTermList(mScript));
				i++;
			}
			assert i == resInnerTerms.length;
			return resInnerTerms;
		}

		private Set<XJunction> simplifyWithPosetMinimalElements(final Set<XJunction> resOuterJunction) {
			if (!POSET_SIMPLIFICATION) {
				return resOuterJunction;
			}
			final boolean timeConsumingSimplification = (resOuterJunction.size() > 5000);
			if (timeConsumingSimplification) {
				mLogger.warn("Simplifying " + outerJunctionName() + " of " + resOuterJunction.size() + " "
						+ innerJunctionName() + "s. " + "This might take some time...");
			}

			// Simplify by keeping only minimal (with respect to set inclusion)
			// outerJunctions.
			final XJunctionPosetMinimalElements pme = new XJunctionPosetMinimalElements();
			for (final XJunction resInnerSet : resOuterJunction) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(), "XNF transformer was simplifying "
							+ resOuterJunction.size() + " " + innerJunctionName() + "s. ");
				}
				pme.add(resInnerSet);
			}

			if (timeConsumingSimplification) {
				mLogger.info("Simplified to " + outerJunctionName() + " of " + pme.getElements().size() + " "
						+ innerJunctionName() + "s. ");
			}

			return pme.getElements();
		}

		/**
		 * Convert an innerJunction of outerJunctions given as an array of terms into a Set of XJunctions.
		 */
		private Set<XJunction> convertInnerJunctionOfOuterJunctionsToSet(final Term[] inputInnerJunction) {
			final Set<XJunction> result = new HashSet<>();
			for (final Term inputInnerJunct : inputInnerJunction) {
				final Term[] inputOuterJunction = getOuterJuncts(inputInnerJunct);
				try {
					result.add(new XJunction(inputOuterJunction));
				} catch (final AtomAndNegationException e) {
					// do nothing, we omit this outerJunction because it is
					// equivalent to the neutral element of the inner connective
					// (true for ∧, false for ∨)
				}
			}
			return result;
		}

		/**
		 * Represents a an innerJunction of outerJunctions using
		 * <ul>
		 * <li>one innerJunction given as an XJunction (mInnerJuncts) and
		 * <li>one innerJunction of outerJunctions given as a set of XJunctions
		 * (mUnprocessedInnerJunctionOfOuterJunctions).
		 * </ul>
		 * (mInnerJuncts ι (outerJunction_1 ι ... ι outerJunction_n)) This class can be used to successively apply
		 * distributivity to get rid of the outerJunctions. Therefore objects of this class are split into a set of such
		 * objects, one for each outerJunct.
		 *
		 * @author Matthias Heizmann
		 *
		 */
		private class ResultInnerJunctions {
			private final XJunction mInnerJuncts;
			private final Set<XJunction> mUnprocessedInnerJunctionOfOuterJunctions;

			public ResultInnerJunctions(final Set<XJunction> innerJunctionOfOuterJunctions)
					throws AtomAndNegationException {
				final XJunction innerJuncts = new XJunction();
				mUnprocessedInnerJunctionOfOuterJunctions =
						moveOutwardsAbsorbeAndMpsimplify(innerJuncts, innerJunctionOfOuterJunctions);
				mInnerJuncts = innerJuncts;
			}

			public ResultInnerJunctions(final XJunction innerJuncts, final Set<XJunction> innerJunctionOfOuterJunctions)
					throws AtomAndNegationException {
				final XJunction newInnerJuncts = new XJunction();
				mUnprocessedInnerJunctionOfOuterJunctions =
						moveOutwardsAbsorbeAndMpsimplify(newInnerJuncts, innerJunctionOfOuterJunctions);
				mInnerJuncts = XJunction.disjointUnion(innerJuncts, newInnerJuncts);
			}

			public boolean isProcessedToInnerJunction() {
				return mUnprocessedInnerJunctionOfOuterJunctions.isEmpty();
			}

			public int numberOfUnprocessedOuterJunctions() {
				return mUnprocessedInnerJunctionOfOuterJunctions.size();
			}

			public XJunction getInnerJunction() {
				return mInnerJuncts;
			}

			public List<ResultInnerJunctions> processOneOuterJunction() {
				final Iterator<XJunction> it = mUnprocessedInnerJunctionOfOuterJunctions.iterator();
				final XJunction next = it.next();
				it.remove();
				final ArrayList<ResultInnerJunctions> result = new ArrayList<>(next.size());
				for (final Entry<Term, Polarity> entry : next.entrySet()) {
					final XJunction singletonInnerJunct = new XJunction(entry.getKey(), entry.getValue());
					final Set<XJunction> innerJunctionOfOuterJunctions =
							new HashSet<>(mUnprocessedInnerJunctionOfOuterJunctions);
					innerJunctionOfOuterJunctions.add(singletonInnerJunct);
					final XJunction innerJunctions = new XJunction(mInnerJuncts);
					try {
						final ResultInnerJunctions rij =
								new ResultInnerJunctions(innerJunctions, innerJunctionOfOuterJunctions);
						result.add(rij);
					} catch (final AtomAndNegationException e) {
						// omit this ResultInnerJunctions it is equivalent to true/false
					}
				}
				return result;
			}

			/**
			 * Given an innerJunction and an innerJunction of outerJunctions, we consider this an an innerJunction
			 * (innerJunction ι (outerJunction_1 ι ... ι outerJunction_n)) and move as many elements as possible to
			 * innerJunction by applying equivalence transformations.
			 *
			 * @param innerJunction
			 *            input and output of this method. This method adds new elements to this XJunction.
			 * @param innerJunctionOfOuterJunctions
			 *            input of this method, but also used to store intermediate data. It is modified and should not
			 *            be used by the caller after calling this method. However the XJunction contained in this set
			 *            are not modified.
			 * @return and innerJunction of outerJunction that is together with the modified innerJunction equivalent to
			 *         the input.
			 * @throws AtomAndNegationException
			 *             thrown if we detect that the input is equivalent to the annihilating element of the inner
			 *             connective
			 */
			private Set<XJunction> moveOutwardsAbsorbeAndMpsimplify(final XJunction innerJunction,
					Set<XJunction> innerJunctionOfOuterJunctions) throws AtomAndNegationException {
				while (true) {
					final boolean modified = moveSingletonsOutwards(innerJunction, innerJunctionOfOuterJunctions);
					if (!modified) {
						return innerJunctionOfOuterJunctions;
					}
					final Set<XJunction> newinnerJunctionOfOuterJunctions =
							applyAbsorbeAndMpsimplify(innerJunction, innerJunctionOfOuterJunctions);
					if (newinnerJunctionOfOuterJunctions == innerJunctionOfOuterJunctions) {
						return innerJunctionOfOuterJunctions;
					}
					innerJunctionOfOuterJunctions = newinnerJunctionOfOuterJunctions;
				}
			}

			/**
			 * Remove from innerJunctionOfOuterJunctions all XJunctions that are singletons and move their elements to
			 * innerJunction.
			 *
			 * @param innerJunction
			 *            is modified and used as input and output of this method
			 * @param innerJunctionOfOuterJunctions
			 *            is modified and input and output of this method
			 * @return true iff innerJunctionOfOuterJunctions contained a singleton (note that if the result is false
			 *         this means especially that the inputs were not modified)
			 * @throws AtomAndNegationException
			 *             the resulting innerJunction would be equivalent to the annihilating element of the inner
			 *             connective.
			 */
			private boolean moveSingletonsOutwards(final XJunction innerJunction,
					final Set<XJunction> innerJunctionOfOuterJunctions) throws AtomAndNegationException {
				boolean someSingletonContained = false;
				final Iterator<XJunction> it = innerJunctionOfOuterJunctions.iterator();
				while (it.hasNext()) {
					final XJunction outerJunction = it.next();
					if (outerJunction.size() == 1) {
						final Entry<Term, Polarity> singleton = outerJunction.entrySet().iterator().next();
						innerJunction.add(singleton.getKey(), singleton.getValue());
						someSingletonContained = true;
						it.remove();
					}
				}
				return someSingletonContained;
			}

			/**
			 * Given an innerJunction and an innerJunction of outerJunctions, we consider this an an innerJunction
			 * (innerJunction ι (outerJunction_1 ι ... ι outerJunction_n)) and simplify the innerJunction of
			 * outerJunctions by applying two simplification rules.
			 * <ul>
			 * <li>1. Absorption. If innerJunction and outerJunction_i share a common element, we drop outerJunction_i
			 * from the innerJunction of outerJuncts.
			 * <li>2. Mpsimplify. If innerJunction contains a formula φ and one outerJunction of outerJunction_i is ¬φ
			 * we remove this outerJunction from outerJunction_i.
			 * </ul>
			 *
			 * @param innerJunction
			 *            above mentioned innerJunction, not modified by this methods
			 * @param innerJunctionOfOuterJunctions
			 *            above mentioned innerJunction of outerJunctions, not modified by this method
			 * @return innerJunction of outerJunctions which is simplified with respect to innerJunction as mentioned
			 *         above. If no simplification was possible innerJunctionOfOuterJunctions (same Object) is returned
			 *         otherwise a new HashSet is returned.
			 */
			private Set<XJunction> applyAbsorbeAndMpsimplify(final XJunction innerJunction,
					final Set<XJunction> innerJunctionOfOuterJunctions) {
				final HashSet<XJunction> newInnerJunctionOfOuterJunctions = new HashSet<>();
				boolean modified = false;
				for (final XJunction outerJunction : innerJunctionOfOuterJunctions) {
					final XJunction newOuterJunction = applyAbsorbeAndMpsimplify(innerJunction, outerJunction);
					if (newOuterJunction == null) {
						// do not add, absorbed by innerJunction
						modified = true;
					} else if (outerJunction == newOuterJunction) {
						// nothing was simplified
						newInnerJunctionOfOuterJunctions.add(newOuterJunction);
					} else {
						// some elements were removed
						assert (outerJunction.size() > newOuterJunction.size());
						newInnerJunctionOfOuterJunctions.add(newOuterJunction);
					}
				}
				if (modified) {
					return newInnerJunctionOfOuterJunctions;
				}
				return innerJunctionOfOuterJunctions;
			}

			/**
			 * Given an innerJunction and an outerJunction, we consider this as an inner Junction (innerJunction ι
			 * outerJunction) and simplify outerJunction with respect to innerJunction. If innerJunction and
			 * outerJunction share a common literal we simplify outerJunction to the neutral element of the
			 * innerJunction (absorption) and return null to indicate that. If there is a literal in outerJunction that
			 * occurs with the opposite polarity in innerJunction, we remove it from the outerJunction (mpsimplify,
			 * reminiscent to modus ponens). In fact, outerJunction is never modified, if we have to modify it, we
			 * return a new XJunction instead. If we do not have to modify it, we return the input outerJunction.
			 */
			private XJunction applyAbsorbeAndMpsimplify(final XJunction innerJunction, final XJunction outerJunction) {
				XJunction resultOuterJunction = outerJunction;
				for (final Entry<Term, Polarity> literal : innerJunction.entrySet()) {
					if (outerJunction.contains(literal.getKey(), literal.getValue())) {
						return null;
					} else if (outerJunction.containsNegation(literal.getKey(), literal.getValue())) {
						// remove negation
						if (resultOuterJunction == outerJunction) {
							resultOuterJunction = new XJunction(outerJunction);
						}
						resultOuterJunction.remove(literal.getKey());
					}
				}
				return resultOuterJunction;
			}
		}

		/**
		 * Represents a Set of XJunction with the following property. The set cannot contain two elements that are
		 * comparable via inclusion. Whenever we add an element xjunction_new such that for some existing xjunction
		 * xjunction_old the inclusion xjunction_old ⊆ xjunction_new the new element xjunction_new is discarded.
		 * Whenever we add an element xjunction_new we remove all existing xjunctions xjunction_old for which the
		 * inclusion xjunction_new ⊆ xjunction_old hols.
		 *
		 * @author Matthias Heizmann
		 *
		 */
		class XJunctionPosetMinimalElements {
			private final Set<XJunction> mElements = new HashSet<>();

			public void add(final XJunction xjunction) {
				final Iterator<XJunction> it = mElements.iterator();
				while (it.hasNext()) {
					final XJunction existing = it.next();
					if (existing.isSubset(xjunction)) {
						// add nothing
						return;
					}
					if (xjunction.isSubset(existing)) {
						it.remove();
					}
				}
				mElements.add(xjunction);
			}

			public Set<XJunction> getElements() {
				return mElements;
			}

			public int size() {
				return mElements.size();
			}
		}

	}

	public class AbortBeforeBlowup extends RuntimeException {

		private static final long serialVersionUID = 1L;

	}
}
