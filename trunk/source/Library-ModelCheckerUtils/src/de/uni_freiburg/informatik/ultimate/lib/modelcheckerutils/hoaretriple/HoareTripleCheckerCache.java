/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;

/**
 * A cache for results of Hoare triple checks.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class HoareTripleCheckerCache {
	private final NestedMap3<IAction, IPredicate, IPredicate, Validity> mInternalCache = new NestedMap3<>();
	private final NestedMap3<IAction, IPredicate, IPredicate, Validity> mCallCache = new NestedMap3<>();
	/**
	 * The second component is the hierarchical predecessor, the third component is
	 * the linear predecessor. We presume that this order is better because we
	 * typically have fewer hierarchical predecessors than linear predecessors.
	 */
	private final NestedMap4<IAction, IPredicate, IPredicate, IPredicate, Validity> mReturnCache = new NestedMap4<>();

	/**
	 * Gets the cache result of the given Hoare triple (for an internal action).
	 *
	 * @param pre
	 *            the precondition of the Hoare triple
	 * @param act
	 *            the action (or statement) of the Hoare triple
	 * @param post
	 *            the postcondition of the Hoare triple
	 *
	 * @return the result of the given triple, if it is cached. Otherwise returns {@code null}.
	 */
	public Validity getInternal(final IPredicate pre, final IInternalAction act, final IPredicate post) {
		return mInternalCache.get(act, pre, post);
	}

	/**
	 * Caches the result of a Hoare triple check (for an internal action).
	 *
	 * @param pre
	 *            the precondition of the Hoare triple
	 * @param act
	 *            the action (or statement) of the Hoare triple
	 * @param post
	 *            the postcondition of the Hoare triple
	 * @param result
	 *            the result of the check
	 */
	public void putInternal(final IPredicate pre, final IInternalAction act, final IPredicate post,
			final Validity result) {
		mInternalCache.put(act, pre, post, result);
	}

	/**
	 * Gets the cache result of the given Hoare triple (for a call action).
	 *
	 * @param pre
	 *            the precondition of the Hoare triple
	 * @param act
	 *            the action (or statement) of the Hoare triple
	 * @param post
	 *            the postcondition of the Hoare triple
	 *
	 * @return the result of the given triple, if it is cached. Otherwise returns {@code null}.
	 */
	public Validity getCall(final IPredicate pre, final ICallAction act, final IPredicate post) {
		return mCallCache.get(act, pre, post);
	}

	/**
	 * Caches the result of a Hoare triple check (for a call action).
	 *
	 * @param pre
	 *            the precondition of the Hoare triple
	 * @param act
	 *            the action (or statement) of the Hoare triple
	 * @param post
	 *            the postcondition of the Hoare triple
	 * @param result
	 *            the result of the check
	 */
	public void putCall(final IPredicate pre, final ICallAction act, final IPredicate post, final Validity result) {
		mCallCache.put(act, pre, post, result);
	}

	/**
	 * Gets the cache result of the given Hoare quadruple (for a return action).
	 *
	 * @param preLin
	 *            the linear precondition of the Hoare quadruple
	 * @param preHier
	 *            the hierarchical precondition of the Hoare quadruple
	 * @param act
	 *            the action (or statement) of the Hoare quadruple
	 * @param post
	 *            the postcondition of the Hoare quadruple
	 *
	 * @return the result of the given quadruple, if it is cached. Otherwise returns {@code null}.
	 */
	public Validity getReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate post) {
		return mReturnCache.get(act, preHier, preLin, post);
	}

	/**
	 * Caches the result of a Hoare quadruple check (for a return action).
	 *
	 * @param preLin
	 *            the linear precondition of the Hoare quadruple
	 * @param preHier
	 *            the hierarchical precondition of the Hoare quadruple
	 * @param act
	 *            the action (or statement) of the Hoare quadruple
	 * @param post
	 *            the postcondition of the Hoare quadruple
	 * @param result
	 *            the result of the check
	 */
	public void putReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate post, final Validity result) {
		mReturnCache.put(act, preHier, preLin, post, result);
	}

	NestedMap3<IAction, IPredicate, IPredicate, Validity> getInternalCache() {
		return mInternalCache;
	}

	NestedMap3<IAction, IPredicate, IPredicate, Validity> getCallCache() {
		return mCallCache;
	}

	public NestedMap4<IAction, IPredicate, IPredicate, IPredicate, Validity> getReturnCache() {
		return mReturnCache;
	}



}
