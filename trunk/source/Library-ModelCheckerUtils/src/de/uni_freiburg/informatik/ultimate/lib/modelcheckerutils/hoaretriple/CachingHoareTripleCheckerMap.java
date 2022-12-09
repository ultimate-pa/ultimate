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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.datastructures.IterableIntersection;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 * {@link CachingHoareTripleChecker} that does not directly iterate over covered
 * predicates and covering predicates in order to do an extended cache check
 * (like {@link CachingHoareTripleCheckerIterative}) but also takes the current
 * cache into account. If in doubt which {@link CachingHoareTripleChecker} you
 * should use, use this one.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class CachingHoareTripleCheckerMap extends CachingHoareTripleChecker {

	private static final String UNKNOWN_CASE = "unknown case";
	private static final String CASE_MUST_NOT_OCCUR = "case must not occur";

	public CachingHoareTripleCheckerMap(final IUltimateServiceProvider services,
			final IHoareTripleChecker protectedHoareTripleChecker, final IPredicateUnifier predicateUnifer) {
		super(services, protectedHoareTripleChecker, predicateUnifer);
	}

	public CachingHoareTripleCheckerMap(final IUltimateServiceProvider services,
			final IHoareTripleChecker protectedHoareTripleChecker, final IPredicateUnifier predicateUnifier,
			final HoareTripleCheckerCache initialCache) {
		super(services, protectedHoareTripleChecker, predicateUnifier, initialCache);
	}

	@Override
	protected Validity extendedBinaryCacheCheck(final IPredicate pre, final IAction act, final IPredicate succ,
			final NestedMap3<IAction, IPredicate, IPredicate, Validity> binaryCache) {

		final NestedMap2<IPredicate, IPredicate, Validity> pred2succ = binaryCache.get(act);
		if (pred2succ == null) {
			// cache does not store information for our action
			return null;
		}

		boolean someResultWasUnknown = false;
		{
			final Set<IPredicate> strongerThanPre = mPredicateUnifier.getCoverageRelation().getCoveredPredicates(pre);
			final Set<IPredicate> weakerThanSucc = mPredicateUnifier.getCoverageRelation().getCoveringPredicates(succ);

			final Iterable<IPredicate> preds = new IterableIntersection<>(pred2succ.keySet(), strongerThanPre);
			for (final IPredicate strongP : preds) {
				final Map<IPredicate, Validity> succ2Val = pred2succ.get(strongP);
				final Iterable<IPredicate> succs = new IterableIntersection<>(succ2Val.keySet(), weakerThanSucc);
				for (final IPredicate weakS : succs) {
					final Validity validity = evaluteResultStrongerThanPreAndWeakerThanSucc(succ2Val.get(weakS));
					if (validity == null) {
						continue;
					}
					switch (validity) {
					case INVALID:
						return Validity.INVALID;
					case UNKNOWN:
						someResultWasUnknown = true;
						break;
					case NOT_CHECKED:
					case VALID:
						throw new AssertionError(CASE_MUST_NOT_OCCUR);
					default:
						throw new AssertionError(UNKNOWN_CASE);
					}
				}
			}
		}
		{
			final Set<IPredicate> weakerThanPre = mPredicateUnifier.getCoverageRelation().getCoveringPredicates(pre);
			final Set<IPredicate> strongerThanSucc = mPredicateUnifier.getCoverageRelation().getCoveredPredicates(succ);

			final Iterable<IPredicate> preds = new IterableIntersection<>(pred2succ.keySet(), weakerThanPre);
			for (final IPredicate weakP : preds) {
				final Map<IPredicate, Validity> succ2Val = pred2succ.get(weakP);
				final Iterable<IPredicate> succs = new IterableIntersection<>(succ2Val.keySet(), strongerThanSucc);
				for (final IPredicate strongS : succs) {
					final Validity validity = evaluteResultWeakerThanPreAndStrongerThanSucc(succ2Val.get(strongS));
					if (validity == null) {
						continue;
					}
					switch (validity) {
					case VALID:
						return Validity.VALID;
					case UNKNOWN:
						someResultWasUnknown = true;
						break;
					case NOT_CHECKED:
					case INVALID:
						throw new AssertionError(CASE_MUST_NOT_OCCUR);
					default:
						throw new AssertionError(UNKNOWN_CASE);
					}
				}
			}
		}
		if (UNKNOWN_IF_SOME_EXTENDED_CHECK_IS_UNKNOWN && someResultWasUnknown) {
			// we pass this result as a warning that the corresponding check might be
			// expensive
			return Validity.UNKNOWN;
		}
		return null;
	}

	private Validity evaluteResultWeakerThanPreAndStrongerThanSucc(final Validity validity) {
		if (validity == null) {
			return validity;
		}
		switch (validity) {
		case VALID:
			// pass result, if Hoare triple holds for weaker pre and for stronger succ,
			// it also does not hold for original pre/succ
			return validity;
		case UNKNOWN:
			// we pass this result as a warning that the corresponding check might be
			// expensive
			return validity;
		case INVALID:
			// information does not help
			return null;
		case NOT_CHECKED:
			return null;
		default:
			throw new AssertionError(UNKNOWN_CASE);
		}
	}

	private Validity evaluteResultStrongerThanPreAndWeakerThanSucc(final Validity validity) {
		if (validity == null) {
			return validity;
		}
		switch (validity) {
		case VALID:
			// information does not help
			return null;
		case UNKNOWN:
			// we pass this result as a warning that the corresponding check might be
			// expensive
			return validity;
		case INVALID:
			// pass result, if Hoare triple does not hold for stronger pre and for weaker
			// succ,
			// it also does not hold for original pre/succ
			return validity;
		case NOT_CHECKED:
			return null;
		default:
			throw new AssertionError(UNKNOWN_CASE);
		}
	}

}
