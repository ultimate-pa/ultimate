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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IIncrementalInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationCheckResultStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IConcurrentProductStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISenwaStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;

public class PredicateFactoryForInterpolantAutomata
		implements ISenwaStateFactory<IPredicate>, IBlackWhiteStateFactory<IPredicate>,
		IBuchiComplementNcsbStateFactory<IPredicate>, IConcurrentProductStateFactory<IPredicate>,
		IPetriNet2FiniteAutomatonStateFactory<IPredicate>, IIncrementalInclusionStateFactory<IPredicate>,
		IMinimizationStateFactory<IPredicate>, IMinimizationCheckResultStateFactory<IPredicate> {

	protected final boolean mComputeHoareAnnotation;
	private final IPredicate mEmtpyStack;
	protected final ManagedScript mMgdScript;
	protected final PredicateFactory mPredicateFactory;

	public PredicateFactoryForInterpolantAutomata(final ManagedScript mgdScript,
			final PredicateFactory predicateFactory, final boolean computeHoareAnnotation) {
		mComputeHoareAnnotation = computeHoareAnnotation;
		mMgdScript = mgdScript;
		mPredicateFactory = predicateFactory;
		mEmtpyStack = mPredicateFactory.newEmptyStackPredicate();
	}

	@Override
	public IPredicate intersection(final IPredicate p1, final IPredicate p2) {
		throw new AssertionError(
				"intersect is only required for refinement, not for construction of interpolant automaton");
	}

	@Override
	public IPredicate determinize(final Map<IPredicate, Set<IPredicate>> down2up) {
		if (mComputeHoareAnnotation) {
			final List<IPredicate> upPredicates = new ArrayList<>();
			for (final IPredicate caller : down2up.keySet()) {
				for (final IPredicate current : down2up.get(caller)) {
					if (mPredicateFactory.isDontCare(current)) {
						return mPredicateFactory.newDontCarePredicate(null);
					}
					upPredicates.add(current);
				}
			}
			final IPredicate result = mPredicateFactory.and(upPredicates);
			return result;
		}
		return mPredicateFactory.newDontCarePredicate(null);
	}

	@Override
	public IPredicate createSinkStateContent() {
		return mPredicateFactory.newPredicate(mMgdScript.getScript().term("true"));
	}

	@Override
	public IPredicate createEmptyStackState() {
		return mEmtpyStack;
	}

	@Override
	public IPredicate merge(final Collection<IPredicate> states) {
		return mPredicateFactory.or(states);
	}

	@Override
	public IPredicate senwa(final IPredicate entry, final IPredicate state) {
		assert false : "still used?";
		return mPredicateFactory.newDontCarePredicate(((SPredicate) state).getProgramPoint());
	}

	@Override
	public IPredicate buchiComplementFkv(final LevelRankingState<?, IPredicate> compl) {
		return mPredicateFactory.newDebugPredicate(compl.toString());
	}

	@Override
	public IPredicate buchiComplementNcsb(final LevelRankingState<?, IPredicate> compl) {
		return buchiComplementFkv(compl);
	}

	@Override
	public IPredicate intersectBuchi(final IPredicate s1, final IPredicate s2, final int track) {
		throw new AssertionError(
				"intersect is only required for refinement, not for construction of interpolant automaton");
	}

	@Override
	public IPredicate concurrentProduct(final IPredicate c1, final IPredicate c2) {
		if (!(c2 instanceof ISLPredicate)) {
			throw new IllegalArgumentException("has to be predicate with single location");
		}
		IcfgLocation[] programPoints;
		if (c1 instanceof ISLPredicate) {
			programPoints = new BoogieIcfgLocation[2];
			programPoints[0] = ((ISLPredicate) c1).getProgramPoint();
		} else if (c1 instanceof IMLPredicate) {
			final IMLPredicate mlpred = (IMLPredicate) c1;
			final int newLength = mlpred.getProgramPoints().length + 1;
			programPoints = Arrays.copyOf(mlpred.getProgramPoints(), newLength);
		} else {
			throw new UnsupportedOperationException();
		}
		final IcfgLocation c2PP = ((ISLPredicate) c2).getProgramPoint();
		programPoints[programPoints.length - 1] = c2PP;
		final Term conjunction = mPredicateFactory.and(c1, c2).getFormula();
		final IMLPredicate result = mPredicateFactory.newMLPredicate(programPoints, conjunction);
		return result;
	}

	@Override
	public IPredicate getContentOnPetriNet2FiniteAutomaton(final Marking<?, IPredicate> marking) {
		/*
		 * TODO Christian 2017-02-15 This method was not implemented although it was used by class CegarLoopJulian in
		 * method acceptsPetriViaFA().
		 */
		throw new UnsupportedOperationException("State factory operation not implemented!");
	}

	@Override
	public IPredicate getBlackContent(final IPredicate content) {
		return mPredicateFactory.newDebugPredicate("Black: " + content);
	}

}
