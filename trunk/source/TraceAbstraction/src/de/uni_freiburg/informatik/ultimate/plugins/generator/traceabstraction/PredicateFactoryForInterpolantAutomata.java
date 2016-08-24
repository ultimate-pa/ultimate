/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class PredicateFactoryForInterpolantAutomata extends StateFactory<IPredicate> {

	final protected boolean mComputeHoareAnnotation;
//	final protected TAPreferences mPref;
	private final IPredicate memtpyStack;
	protected final SmtManager mSmtManager;

	public PredicateFactoryForInterpolantAutomata(final SmtManager smtManager, final boolean computeHoareAnnotation) {
		mComputeHoareAnnotation = computeHoareAnnotation;
		mSmtManager = smtManager;
		memtpyStack = mSmtManager.getPredicateFactory().newEmptyStackPredicate();
	}

	@Override
	public IPredicate intersection(final IPredicate p1, final IPredicate p2) {
		throw new AssertionError(
				"intersect is only required for refinement, not for construction of interpolant automaton");
	}

	@Override
	public IPredicate determinize(final Map<IPredicate, Set<IPredicate>> down2up) {
		if (mComputeHoareAnnotation) {
			final List<IPredicate> upPredicates = new ArrayList<IPredicate>();
			for (final IPredicate caller : down2up.keySet()) {
				for (final IPredicate current : down2up.get(caller)) {
					if (mSmtManager.getPredicateFactory().isDontCare(current)) {
						return mSmtManager.getPredicateFactory().newDontCarePredicate(null);
					}
					upPredicates.add(current);
				}
			}
			final Term conjunction = mSmtManager.getPredicateFactory().and(upPredicates);
			final IPredicate result = mSmtManager.getPredicateFactory().newPredicate(conjunction);
			return result;
		} else {
			return mSmtManager.getPredicateFactory().newDontCarePredicate(null);
		}
	}

	@Override
	public IPredicate createSinkStateContent() {
		return mSmtManager.getPredicateFactory().newPredicate(mSmtManager.getScript().term("true"));
	}

	@Override
	public IPredicate createEmptyStackState() {
		return memtpyStack;
	}

	@Override
	public IPredicate createDoubleDeckerContent(final IPredicate down, final IPredicate up) {
		throw new UnsupportedOperationException();
	}

	@Override
	public IPredicate minimize(final Collection<IPredicate> states) {
		final Term disjunction = mSmtManager.getPredicateFactory().or(false, states);
		final IPredicate result = mSmtManager.getPredicateFactory().newPredicate(disjunction);
		return result;
	}

	@Override
	public IPredicate senwa(final IPredicate entry, final IPredicate state) {
		assert false : "still used?";
		return mSmtManager.getPredicateFactory().newDontCarePredicate(((SPredicate) state).getProgramPoint());
	}

	@Override
	public IPredicate buchiComplementFKV(final LevelRankingState<?, IPredicate> compl) {
		return mSmtManager.getPredicateFactory().newDebugPredicate(compl.toString());
	}

	@Override
	public IPredicate buchiComplementNCSB(final LevelRankingState<?, IPredicate> compl) {
		return buchiComplementFKV(compl);
	}

	@Override
	public IPredicate intersectBuchi(final IPredicate s1, final IPredicate s2, final int track) {
		throw new AssertionError(
				"intersect is only required for refinement, not for construction of interpolant automaton");
	}

	@Override
	public IPredicate getContentOnConcurrentProduct(final IPredicate c1, final IPredicate c2) {
		if (!(c2 instanceof ISLPredicate)) {
			throw new IllegalArgumentException("has to be predicate with single location");
		}
		ProgramPoint[] programPoints;
		if (c1 instanceof ISLPredicate) {
			programPoints = new ProgramPoint[2];
			programPoints[0] = ((ISLPredicate) c1).getProgramPoint();
		} else if (c1 instanceof IMLPredicate) {
			final IMLPredicate mlpred = (IMLPredicate) c1;
			final int newLength = mlpred.getProgramPoints().length + 1;
			programPoints = Arrays.copyOf(mlpred.getProgramPoints(), newLength);
		} else {
			throw new UnsupportedOperationException();
		}
		final ProgramPoint c2PP = ((ISLPredicate) c2).getProgramPoint();
		programPoints[programPoints.length - 1] = c2PP;
		final Term conjunction = mSmtManager.getPredicateFactory().and(c1, c2);
		final IMLPredicate result = mSmtManager.getPredicateFactory().newMLPredicate(programPoints, conjunction);
		return result;
	}

}
