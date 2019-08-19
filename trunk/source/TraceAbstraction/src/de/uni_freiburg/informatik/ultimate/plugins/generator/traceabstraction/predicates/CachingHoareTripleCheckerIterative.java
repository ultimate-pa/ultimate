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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;

/**
 * {@link CachingHoareTripleChecker} that iterates over covered predicates and covering predicates in order to do an
 * extended cache check. If in doubt which caching checker you should use, use {@link CachingHoareTripleCheckerMap}.
 *
 * @author Matthias Heizmann
 *
 */
public class CachingHoareTripleCheckerIterative extends CachingHoareTripleChecker implements IHoareTripleChecker {

	public CachingHoareTripleCheckerIterative(final IUltimateServiceProvider services,
			final IHoareTripleChecker protectedHoareTripleChecker, final IPredicateUnifier predicateUnifer) {
		super(services, protectedHoareTripleChecker, predicateUnifer);
	}

	@Override
	protected Validity extendedBinaryCacheCheck(final IPredicate pre, final IAction act, final IPredicate succ,
			final NestedMap3<IAction, IPredicate, IPredicate, Validity> binaryCache) {
		boolean someResultWasUnknown = false;
		{
			final Set<IPredicate> strongerThanPre = mPredicateUnifer.getCoverageRelation().getCoveredPredicates(pre);
			final Set<IPredicate> weakerThanSucc = mPredicateUnifer.getCoverageRelation().getCoveringPredicates(succ);
			if (strongerThanPre.size() * weakerThanSucc.size() > 100) {
				mLogger.warn("costly cache lookup: " + strongerThanPre.size() * weakerThanSucc.size());
			}
			for (final IPredicate strengthenedPre : strongerThanPre) {
				for (final IPredicate weakenedSucc : weakerThanSucc) {
					final Validity result = binaryCache.get(act, strengthenedPre, weakenedSucc);
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
						// throw new IllegalStateException("use protective Hoare triple checker");
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
					final Validity result = binaryCache.get(act, weakenedPre, strengthenedSucc);
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
						// throw new IllegalStateException("use protective Hoare triple checker");
						default:
							throw new AssertionError("unknown case");
						}
					}
				}
			}
		}
		if (UNKNOWN_IF_SOME_EXTENDED_CHECK_IS_UNKNOWN && someResultWasUnknown) {
			return Validity.UNKNOWN;
		}
		return null;
	}
}
