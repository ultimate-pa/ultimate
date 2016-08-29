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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;

/**
 * CachingHoareTripleChecker that iterates over covered predicates and covering
 * predicates in order to do an exteded cache check
 * @author Matthias Heizmann
 *
 */
public class CachingHoareTripleChecker_Iterative extends CachingHoareTripleChecker implements IHoareTripleChecker {
	
	private final NestedMap3<IPredicate, IInternalAction, IPredicate, Validity> mInternalCache =
			new NestedMap3<>();
	private final NestedMap3<IPredicate, CodeBlock, IPredicate, Validity> mCallCache =
			new NestedMap3<>();
	private final NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, Validity> mReturnCache =
			new NestedMap4<>();
	private final boolean mUnknownIfSomeExtendedCacheCheckIsUnknown = true;
	
	public CachingHoareTripleChecker_Iterative(
			final IUltimateServiceProvider services, final IHoareTripleChecker protectedHoareTripleChecker,
			final PredicateUnifier predicateUnifer) {
		super(services, protectedHoareTripleChecker, predicateUnifer);
	}

	@Override
	public Validity getFromInternalCache(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		return mInternalCache.get(pre, act, succ);
	}

	@Override
	public void addToInternalCache(final IPredicate pre, final IInternalAction act, final IPredicate succ,
			final Validity result) {
		mInternalCache.put(pre, act, succ, result);
	}

	@Override
	protected Validity extendedCacheCheckInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		boolean someResultWasUnknown = false;
		{
			final Set<IPredicate> strongerThanPre = mPredicateUnifer.getCoverageRelation().getCoveredPredicates(pre);
			final Set<IPredicate> weakerThanSucc = mPredicateUnifer.getCoverageRelation().getCoveringPredicates(succ);
			if (strongerThanPre.size() * weakerThanSucc.size() > 100) {
				mLogger.warn("costly cache lookup: " + strongerThanPre.size() * weakerThanSucc.size());
			}
			for (final IPredicate strengthenedPre : strongerThanPre) {
				for (final IPredicate weakenedSucc : weakerThanSucc) {
					final Validity result = mInternalCache.get(strengthenedPre, act, weakenedSucc);
					if (result != null) {
						switch (result) {
						case VALID:
							break;
						case UNKNOWN:
							someResultWasUnknown = true;
							break;
						case INVALID:
							return result;
						case NOT_CHECKED:
							break;
//						throw new IllegalStateException("use protective Hoare triple checker");
						default:
							throw new AssertionError("unknown case");
						}
					}
				}
			}
		}
		{
			final Set<IPredicate> weakerThanPre = mPredicateUnifer.getCoverageRelation().getCoveringPredicates(pre);
			final Set<IPredicate> strongerThanSucc = mPredicateUnifer.getCoverageRelation().getCoveredPredicates(succ);
			if (weakerThanPre.size() * strongerThanSucc.size() > 100) {
				mLogger.warn("costly cache lookup: " + weakerThanPre.size() * strongerThanSucc.size());
			}
			for (final IPredicate weakenedPre : weakerThanPre) {
				for (final IPredicate strengthenedSucc : strongerThanSucc) {
					final Validity result = mInternalCache.get(weakenedPre, act, strengthenedSucc);
					if (result != null) {
						switch (result) {
						case VALID:
							return result;
						case UNKNOWN:
							someResultWasUnknown = true;
							break;
						case INVALID:
							break;
						case NOT_CHECKED:
							break;
//						throw new IllegalStateException("use protective Hoare triple checker");
						default:
							throw new AssertionError("unknown case");
						}
					}
				}
			}
		}
		if (mUnknownIfSomeExtendedCacheCheckIsUnknown && someResultWasUnknown) {
			return Validity.UNKNOWN;
		} else {
			return null;
		}
	}

}
