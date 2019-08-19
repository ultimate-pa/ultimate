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
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateWithHistory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;

public class PredicateFactoryRefinement extends PredicateFactoryForInterpolantAutomata {

	private static final boolean DEBUG_COMPUTE_HISTORY = false;

	protected final IUltimateServiceProvider mServices;
	protected int mIteration;
	private final Set<? extends IcfgLocation> mHoareAnnotationProgramPoints;

	public PredicateFactoryRefinement(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final PredicateFactory predicateFactory, final boolean computeHoareAnnoation,
			final Set<? extends IcfgLocation> hoareAnnotationLocations) {
		super(mgdScript, predicateFactory, computeHoareAnnoation);
		mServices = services;
		mHoareAnnotationProgramPoints = hoareAnnotationLocations;
	}

	@Override
	public IPredicate intersection(final IPredicate p1, final IPredicate p2) {
		if (p1 instanceof IMLPredicate) {
			// assert mCsToolkit.isDontCare(p2);
			assert !mComputeHoareAnnotation;
			return mPredicateFactory.newMLDontCarePredicate(((IMLPredicate) p1).getProgramPoints());
		} else if (p1 instanceof ISLPredicate) {
			final IcfgLocation pp = ((ISLPredicate) p1).getProgramPoint();
			if (mHoareAnnotationProgramPoints.contains(pp)) {
				Term conjunction = mPredicateFactory.and(p1, p2).getFormula();
				conjunction = new CommuhashNormalForm(mServices, mMgdScript.getScript()).transform(conjunction);
				final IPredicate result;
				if (DEBUG_COMPUTE_HISTORY) {
					assert p1 instanceof PredicateWithHistory;
					final Map<Integer, Term> history = ((PredicateWithHistory) p1).getCopyOfHistory();
					history.put(mIteration, p2.getFormula());
					result = mPredicateFactory.newPredicateWithHistory(pp, conjunction, history);
				} else {
					result = mPredicateFactory.newSPredicate(pp, conjunction);
				}
				return result;
			}
			return mPredicateFactory.newDontCarePredicate(pp);

		} else {
			throw new AssertionError("unknown predicate");
		}
	}

	@Override
	public IPredicate determinize(final Map<IPredicate, Set<IPredicate>> down2up) {
		throw new AssertionError(
				"determinize is only required for construction of interpolant automaton, not for refinement");
	}

	@Override
	public IPredicate merge(final Collection<IPredicate> states) {
		assert !states.isEmpty() : "minimize empty set???";
		assert sameProgramPoints(states) : "states do not have same program points";
		final IPredicate someElement = states.iterator().next();
		if (someElement instanceof ISLPredicate) {
			final IcfgLocation pp = ((ISLPredicate) someElement).getProgramPoint();
			if (mHoareAnnotationProgramPoints.contains(pp)) {
				Term disjuntion = mPredicateFactory.or(states).getFormula();
				disjuntion = new CommuhashNormalForm(mServices, mMgdScript.getScript()).transform(disjuntion);
				return mPredicateFactory.newSPredicate(pp, disjuntion);
			}
			return mPredicateFactory.newDontCarePredicate(pp);
		} else if (someElement instanceof IMLPredicate) {
			final IcfgLocation[] pps = ((IMLPredicate) someElement).getProgramPoints();
			if (states.isEmpty()) {
				assert false : "minimize empty set???";
				return mPredicateFactory.newMLDontCarePredicate(pps);
			}
			final Term disjunction = mPredicateFactory.or(states).getFormula();
			return mPredicateFactory.newMLPredicate(pps, disjunction);
		} else {
			throw new AssertionError("unknown predicate");
		}
	}

	private boolean sameProgramPoints(final Collection<IPredicate> states) {
		final Iterator<IPredicate> it = states.iterator();
		final IPredicate firstPredicate = it.next();
		if (firstPredicate instanceof ISLPredicate) {
			final IcfgLocation firstProgramPoint = ((ISLPredicate) firstPredicate).getProgramPoint();
			while (it.hasNext()) {
				final IcfgLocation pp = ((ISLPredicate) it.next()).getProgramPoint();
				if (pp != firstProgramPoint) {
					return false;
				}
			}
		} else if (firstPredicate instanceof IMLPredicate) {
			mServices.getLoggingService().getLogger(Activator.PLUGIN_ID).warn("Check not implemented");
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

	@Override
	public IPredicate getContentOnPetriNet2FiniteAutomaton(final Marking<?, IPredicate> marking) {
		final IcfgLocation[] programPoints =
				marking.stream().map(x -> ((SPredicate) x).getProgramPoint()).toArray(IcfgLocation[]::new);
		return mPredicateFactory.newMLDontCarePredicate(programPoints);
	}

}
