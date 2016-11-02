/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateWithHistory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;

public class PredicateFactoryRefinement extends PredicateFactoryForInterpolantAutomata {
	
	private static final boolean s_DebugComputeHistory = false;
	
	protected final Map<String,Map<String,ProgramPoint>> mlocNodes;
	protected int mIteration;
	protected final HoareAnnotationFragments mHoareAnnotationFragments;
	private final boolean mMaintainHoareAnnotationFragments = false;
	private final HashSet<ProgramPoint> mHoareAnnotationProgramPoints;
	private final HoareAnnotationPositions mHoareAnnotationPositions;
	
	
	public PredicateFactoryRefinement(final Map<String,Map<String,ProgramPoint>> locNodes,
							final CfgSmtToolkit smtManager, final PredicateFactory predicateFactory,
							final boolean computeHoareAnnoation, 
							final HoareAnnotationFragments haf, 
							final HashSet<ProgramPoint> hoareAnnotationProgramPoints, 
							final HoareAnnotationPositions hoareAnnoationPositions) {
		super(smtManager, predicateFactory, computeHoareAnnoation);
		mlocNodes = locNodes;
//		mMaintainHoareAnnotationFragments = maintainHoareAnnotationFragments;
		mHoareAnnotationFragments = haf;
		mHoareAnnotationProgramPoints = hoareAnnotationProgramPoints;
		mHoareAnnotationPositions = hoareAnnoationPositions;
	}

	
	@Override
	public IPredicate intersection(final IPredicate p1, final IPredicate p2) {
		if (p1 instanceof IMLPredicate) {
//			assert mSmtManager.isDontCare(p2);
			assert !mComputeHoareAnnotation;
			return mPredicateFactory.newMLDontCarePredicate(((IMLPredicate) p1).getProgramPoints());
		}
		
		assert (p1 instanceof ISLPredicate);

		final ProgramPoint pp = ((ISLPredicate) p1).getProgramPoint();

		if (omitComputationOfHoareAnnotation(pp, p1, p2)) {
			return mPredicateFactory.newDontCarePredicate(pp);
		}
		final Term conjunction = mPredicateFactory.and(p1, p2);
		IPredicate result;
		if (s_DebugComputeHistory) {
			assert (p1 instanceof PredicateWithHistory);
			final Map<Integer, Term> history = 
					((PredicateWithHistory) p1).getCopyOfHistory();
				history.put(mIteration,p2.getFormula());
			result = mPredicateFactory.newPredicateWithHistory(
					pp, conjunction, history);
		} else {
			result = mPredicateFactory.newSPredicate(pp, conjunction);
		}
		
		if (mMaintainHoareAnnotationFragments) {
//			mHoareAnnotationFragments.announceReplacement(p1, result);
		}
		return result;
	}
	
	private boolean omitComputationOfHoareAnnotation(final ProgramPoint pp, final IPredicate p1, final IPredicate p2) {
		if (!mComputeHoareAnnotation || mPredicateFactory.isDontCare(p1) || mPredicateFactory.isDontCare(p2)) {
			return true;
		}
		if (mHoareAnnotationPositions == HoareAnnotationPositions.LoopsAndPotentialCycles) {
			assert mHoareAnnotationProgramPoints != null : "we need this for HoareAnnotationPositions.LoopInvariantsAndEnsures";
			return !mHoareAnnotationProgramPoints.contains(pp);
		} else {
			return false;
		}
	}
	


	@Override
	public IPredicate determinize(final Map<IPredicate, Set<IPredicate>> down2up) {
		throw new AssertionError(
				"determinize is only required for construction of interpolant automaton, not for refinement");
	}

	@Override
	public IPredicate minimize(final Collection<IPredicate> states) {
		assert sameProgramPoints(states);
		final IPredicate someElement = states.iterator().next();
		if (someElement instanceof ISLPredicate) {
			final ProgramPoint pp = ((ISLPredicate) someElement).getProgramPoint();
			if (states.isEmpty()) {
				assert false : "minimize empty set???";
			return mPredicateFactory.newDontCarePredicate(pp);
			}
			final Term disjuntion = mPredicateFactory.or(false, states);
			if (mPredicateFactory.isDontCare(disjuntion)) {
				return mPredicateFactory.newDontCarePredicate(pp);
			} else {
				return mPredicateFactory.newSPredicate(pp, disjuntion);
			}
		} else if (someElement instanceof IMLPredicate) {
			final ProgramPoint[] pps = ((IMLPredicate) someElement).getProgramPoints();
			if (states.isEmpty()) {
				assert false : "minimize empty set???";
				return mPredicateFactory.newMLDontCarePredicate(pps);
			}
			final Term disjunction = mPredicateFactory.or(false, states);
			return mPredicateFactory.newMLPredicate(pps, disjunction);
		} else {
			throw new AssertionError("unknown predicate");
		}
	}
	
	
	private static boolean sameProgramPoints(final Collection<IPredicate> states) {
		final Iterator<IPredicate> it = states.iterator();
		final IPredicate firstPredicate = it.next();
		if (firstPredicate instanceof ISLPredicate) {
			final ProgramPoint firstProgramPoint = ((ISLPredicate) firstPredicate).getProgramPoint();
			while (it.hasNext()) {
				final ProgramPoint pp = ((ISLPredicate) it.next()).getProgramPoint();
				if (pp != firstProgramPoint) {
					return false;
				}
			}
		} else if (firstPredicate instanceof IMLPredicate) {
			System.out.println("Warning, check not implemented");
		} else {
			throw new AssertionError("unsupported predicate");
		}
		return true;
	}
	

	@Override
	public IPredicate senwa(final IPredicate entry, final IPredicate state) {
		return mPredicateFactory.newDontCarePredicate(((SPredicate) state).getProgramPoint());
	}
	
	@Override
	public IPredicate intersectBuchi(final IPredicate s1, final IPredicate s2, final int track) {
		return intersection(s1, s2);
	}


	public void setIteration(final int i) {
		mIteration = i;
	}
	

}
