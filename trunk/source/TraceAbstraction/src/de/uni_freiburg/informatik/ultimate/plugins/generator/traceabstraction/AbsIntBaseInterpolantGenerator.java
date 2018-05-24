/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.CachingHoareTripleChecker;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class AbsIntBaseInterpolantGenerator<LETTER extends IAction> implements IInterpolantGenerator<LETTER> {

	private final IPredicateUnifier mPredicateUnifier;
	private final Word<LETTER> mCex;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final InterpolantComputationStatus mStatus;

	AbsIntBaseInterpolantGenerator(final IPredicateUnifier predicateUnifier, final Word<LETTER> cex,
			final AbsIntPredicate<?> precondition, final AbsIntPredicate<?> postcondition,
			final InterpolantComputationStatus status) {
		mPredicateUnifier = Objects.requireNonNull(predicateUnifier);
		mCex = cex;
		mStatus = Objects.requireNonNull(status);
		mPrecondition = precondition;
		mPostcondition = postcondition;
	}

	@Override
	public List<LETTER> getTrace() {
		return mCex.asList();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return mStatus;
	}

	public abstract CachingHoareTripleChecker getHoareTripleChecker();
}