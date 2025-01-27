/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SmtFreePredicateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

public class PredicateTransferrer {
	private final TransferrerWithVariableCache mTransferrer;

	// Predicate factory used for predicates that belong to the target script.
	private final SmtFreePredicateFactory mTargetFactory;

	// Predicate factory used for backtransferring predicates to the source script.
	private final SmtFreePredicateFactory mSourceFactory;

	private final BidirectionalMap<IPredicate, IPredicate> mPredicateCache = new BidirectionalMap<>();

	public PredicateTransferrer(final TransferrerWithVariableCache transferrer,
			final SmtFreePredicateFactory sourceFactory, final SmtFreePredicateFactory targetFactory) {
		mTransferrer = transferrer;
		mSourceFactory = sourceFactory;
		mTargetFactory = targetFactory;
	}

	public IPredicate transferPredicate(final IPredicate predicate) {
		return mPredicateCache.computeIfAbsent(predicate, this::transferPredicateHelper);
	}

	private BasicPredicate transferPredicateHelper(final IPredicate predicate) {
		if (!predicate.getFuns().isEmpty()) {
			throw new UnsupportedOperationException("Implement support for transferring functions");
		}
		final Set<IProgramVar> variables = mTransferrer.transferVariables(predicate.getVars());
		final Term transferredFormula = mTransferrer.transferTerm(predicate.getFormula());
		final Term transferredClosed = mTransferrer.transferTerm(predicate.getClosedFormula());
		return mTargetFactory.construct(serial -> new BasicPredicate(serial, transferredFormula, variables,
				Collections.emptySet(), transferredClosed));
	}

	public IPredicate backTransferPredicate(final IPredicate predicate) {
		return mPredicateCache.inverse().computeIfAbsent(predicate, this::backTransferPredicateHelper);
	}

	private BasicPredicate backTransferPredicateHelper(final IPredicate predicate) {
		if (!predicate.getFuns().isEmpty()) {
			throw new UnsupportedOperationException("Implement support for transferring functions");
		}
		final Set<IProgramVar> variables = backTransferVariables(predicate.getVars());
		final Term transferredFormula = mTransferrer.backTransferTerm(predicate.getFormula());
		final Term transferredClosed = mTransferrer.backTransferTerm(predicate.getClosedFormula());
		return mSourceFactory.construct(serial -> new BasicPredicate(serial, transferredFormula, variables,
				Collections.emptySet(), transferredClosed));
	}

	private Set<IProgramVar> backTransferVariables(final Set<IProgramVar> vars) {
		return vars.stream().map(mTransferrer::getOriginalProgramVar).collect(Collectors.toSet());
	}
}
