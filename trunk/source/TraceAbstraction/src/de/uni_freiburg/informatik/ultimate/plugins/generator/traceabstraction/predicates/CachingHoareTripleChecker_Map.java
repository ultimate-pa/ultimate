/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 * CachingHoareTripleChecker that does not directly iterate over covered 
 * predicates and covering predicates in order to do an exteded cache check
 * (like {@link CachingHoareTripleChecker_Iterative}) but also takes the
 * current cache into account.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class CachingHoareTripleChecker_Map extends CachingHoareTripleChecker implements IHoareTripleChecker {
	
	private final NestedMap3<IInternalAction, IPredicate, IPredicate, Validity> mInternalCache =
			new NestedMap3<>();
	
	public CachingHoareTripleChecker_Map(
			final IUltimateServiceProvider services, final IHoareTripleChecker protectedHoareTripleChecker,
			final PredicateUnifier predicateUnifer) {
		super(services, protectedHoareTripleChecker, predicateUnifer);
	}

	@Override
	public Validity getFromInternalCache(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		return mInternalCache.get(act, pre, succ);
	}

	@Override
	public void addToInternalCache(final IPredicate pre, final IInternalAction act, final IPredicate succ,
			final Validity result) {
		mInternalCache.put(act, pre, succ, result);
	}

	@Override
	protected Validity extendedCacheCheckInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		boolean someResultWasUnknown = false;
		final NestedMap2<IPredicate, IPredicate, Validity> pred2succ = mInternalCache.get(act);
		if (pred2succ == null) {
			// cannot get any information from cache
			return null;
		}
		{
			final Set<IPredicate> strongerThanPre = mPredicateUnifer.getCoverageRelation().getCoveredPredicates(pre);
			final Set<IPredicate> weakerThanSucc = mPredicateUnifer.getCoverageRelation().getCoveringPredicates(succ);
			final Validity validity = new PreIterator(strongerThanPre, pred2succ, weakerThanSucc, 
					this::evaluteResult_StrongerThanPreAndWeakerThanSucc).iterate();
			if (validity != null) {
				switch (validity) {
				case VALID:
					throw new AssertionError("case must nor occur");
				case UNKNOWN:
					someResultWasUnknown = true;
					break;
				case INVALID:
					return validity;
				case NOT_CHECKED:
					throw new AssertionError("case must nor occur");
				default:
					throw new AssertionError("unknown case");
				}
			}
			
		}
		{
			final Set<IPredicate> weakerThanPre = mPredicateUnifer.getCoverageRelation().getCoveringPredicates(pre);
			final Set<IPredicate> strongerThanSucc = mPredicateUnifer.getCoverageRelation().getCoveredPredicates(succ);
			final Validity validity = new PreIterator(weakerThanPre, pred2succ, strongerThanSucc, 
					this::evaluteResult_WeakerThanPreAndStrongerThanSucc).iterate();
			if (validity != null) {
				switch (validity) {
				case VALID:
					return validity;
				case UNKNOWN:
					someResultWasUnknown = true;
					break;
				case INVALID:
					break;
				case NOT_CHECKED:
					throw new AssertionError("case must nor occur");
				default:
					throw new AssertionError("unknown case");
				}
			}
		}
		if (mUnknownIfSomeExtendedCacheCheckIsUnknown && someResultWasUnknown) {
			// we pass this result as a warning that the corresponding check might be expensive
			return Validity.UNKNOWN;
		} else {
			return null;
		}
	}
	
	private static class PreIterator extends IntersectionIterator<IPredicate, Validity> {
		
		private final IResultEvaluator mResultEvaluator;
		private final NestedMap2<IPredicate, IPredicate, Validity> mPre2Succ2Validity;
		private final Set<IPredicate> mWeakerThenSucc;

		public PreIterator(final Set<IPredicate> set1, final NestedMap2<IPredicate, IPredicate, Validity> map, 
				final Set<IPredicate> weakerThanSucc, final IResultEvaluator resultEvaluator) {
			super(set1, map.keySet());
			mPre2Succ2Validity = map;
			mWeakerThenSucc = weakerThanSucc;
			mResultEvaluator = resultEvaluator;
		}

		@Override
		protected boolean doOneIteration(final IPredicate strengthenedPre) {
			final Validity validity = new SuccIterator(mWeakerThenSucc, 
					mPre2Succ2Validity.get(strengthenedPre), mResultEvaluator).iterate();
			mResult = mResultEvaluator.evaluateResult(validity);
			return (mResult != null && mResult != Validity.UNKNOWN);
		}

	}

	private Validity evaluteResult_WeakerThanPreAndStrongerThanSucc(final Validity validity) {
		if (validity == null) {
			return validity;
		} else {
			switch (validity) {
			case VALID:
				// pass result, if Hoare triple holds for weaker pre and for stronger succ, 
				// it also does not hold for original pre/succ
				return validity;
			case UNKNOWN:
				// we pass this result as a warning that the corresponding check might be expensive
				return validity;
			case INVALID:
				// information does not help
				return null;
			case NOT_CHECKED:
				return null;
			default:
				throw new AssertionError("unknown case");
			}
		}
	}
	
	

	private Validity evaluteResult_StrongerThanPreAndWeakerThanSucc(final Validity validity) {
		if (validity == null) {
			return validity;
		} else {
			switch (validity) {
			case VALID:
				// information does not help
				return null;
			case UNKNOWN:
				// we pass this result as a warning that the corresponding check might be expensive
				return validity;
			case INVALID:
				// pass result, if Hoare triple does not hold for stronger pre and for weaker succ, 
				// it also does not hold for original pre/succ
				return validity;
			case NOT_CHECKED:
				return null;
			default:
				throw new AssertionError("unknown case");
			}
		}
	}
	
	private static class SuccIterator extends IntersectionIterator<IPredicate, Validity> {
		
		private final IResultEvaluator mResultEvaluator;
		private final Map<IPredicate, Validity> mSucc2Validity;

		public SuccIterator(final Set<IPredicate> set1, final Map<IPredicate, Validity> map, 
				final IResultEvaluator resultEvaluator) {
			super(set1, map.keySet());
			mSucc2Validity = map;
			mResultEvaluator = resultEvaluator;
		}

		@Override
		protected boolean doOneIteration(final IPredicate weakerThanSucc) {
			final Validity validity = mSucc2Validity.get(weakerThanSucc);
			mResult = mResultEvaluator.evaluateResult(validity);
			return (mResult != null && mResult != Validity.UNKNOWN);

		}

	}
	
	
	
	@FunctionalInterface
	public interface IResultEvaluator {
		public Validity evaluateResult(Validity validity);
	} 
	
	/**
	 * Allows iteration over intersection of two sets.
	 * Does the iteration efficiently over the smaller set.
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 *
	 * @param <E> type of set elements
	 */
	private static abstract class IntersectionIterator<E, R> {
		private final Set<E> mSmallerSet;
		private final Set<E> mLargerSet;
		protected R mResult;

		public IntersectionIterator(final Set<E> set1, final Set<E> set2) {
			super();
			if (set1.size() >= set2.size()) {
				mSmallerSet = set2;
				mLargerSet = set1;
			} else {
				mSmallerSet = set1;
				mLargerSet = set2;
			}

		}
		protected abstract boolean doOneIteration(E e);
		
		protected final R iterate() {
			for (final E e : mSmallerSet) {
				if (mLargerSet.contains(e)) {
					final boolean stop = doOneIteration(e);
					if (stop) {
						return mResult;
					}
				}
			}
			return mResult;
			
		}
		
	}

}
