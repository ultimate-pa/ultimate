/*
 * Copyright (C) 2018 Jonas Werner (jonaswerner95@gmail.com)
 *
 * This file is part of the ULTIMATE PDR library .
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PDR library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PDR library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pdr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */
public class Pdr<LOC extends IcfgLocation> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final Map<IcfgLocation, ArrayList<Term>> mFrames;
	private ManagedScript mScript;
	private BasicPredicateFactory mPredicateFac;
	private PredicateTransformer<Term, IPredicate, TransFormula> mPredTrans;

	public Pdr(final ILogger logger, final IUltimateServiceProvider services, final Object settings) {
		mLogger = logger;
		mServices = services;
		mFrames = new HashMap<>();
		mScript = null;
		mPredicateFac = null;
		mPredTrans = null;
	}

	PdrResult computePdr(final IIcfg<LOC> icfg, final IPredicateUnifier predicateUnifier) {
		final CfgSmtToolkit csToolkit = icfg.getCfgSmtToolkit();

		mScript = csToolkit.getManagedScript();
		mPredicateFac = predicateUnifier.getPredicateFactory();
		mPredTrans = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));

		final Set<LOC> init = icfg.getInitialNodes();
		final Set<LOC> error = IcfgUtils.getErrorLocations(icfg);

		/**
		 * Check for 0-Counter-Example
		 */
		for (final IcfgLocation initNode : init) {
			if (error.contains(initNode)) {
				return null;
			}
		}

		/**
		 * Initialize level 0.
		 */
		final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(icfg);
		while (iter.hasNext()) {
			final IcfgLocation loc = iter.next();
			mFrames.put(loc, new ArrayList<>());
			if (init.contains(loc)) {
				mFrames.get(loc).add(mScript.getScript().term("true"));
			} else {
				mFrames.get(loc).add(mScript.getScript().term("false"));
			}
		}

		Integer level = 1;

		while (true) {
			/**
			 * Initialize new level.
			 */
			for (final Entry<IcfgLocation, ArrayList<Term>> trace : mFrames.entrySet()) {
				trace.getValue().add(mScript.getScript().term("true"));
			}

			level += 1;

			final ArrayList<Triple<Term, IcfgLocation, Integer>> proofObligations = new ArrayList<>();

			/**
			 * Generate the initial proof-obligations
			 */
			for (final IcfgEdge edge : error.iterator().next().getIncomingEdges()) {
				final Term proofObligationTerm = edge.getTransformula().getFormula();
				final Triple<Term, IcfgLocation, Integer> initialProofObligation =
						new Triple<>(proofObligationTerm, edge.getSource(), level);
				proofObligations.add(initialProofObligation);
			}

			/**
			 * Generated proof-obligation on level 0 -> error is reachable
			 */
			if (!blockingPhase(proofObligations)) {
				final PdrResult result = new PdrResult();
				return result;
			}

			/**
			 * Found invariant -> error is not reachable
			 */
			if (propagationPhase()) {
				final PdrResult result = new PdrResult();
				return result;
			}
		}
	}

	/**
	 * Blocking-phase, for blocking proof-obligations.
	 *
	 * @return false, if proof-obligation on level 0 is created true, if there is no proof-obligation left
	 */
	@SuppressWarnings("unchecked")
	private boolean blockingPhase(final ArrayList<Triple<Term, IcfgLocation, Integer>> initialProofObligations) {

		final Deque<Triple<Term, IcfgLocation, Integer>> proofObligations = new ArrayDeque<>(initialProofObligations);
		while (!proofObligations.isEmpty()) {
			final Triple<Term, IcfgLocation, Integer> proofObligation = proofObligations.pop();
			final Term toBeBlocked = proofObligation.getFirst();
			final IcfgLocation location = proofObligation.getSecond();
			final int level = proofObligation.getThird();

			for (final IcfgEdge predecessorTransition : location.getIncomingEdges()) {
				final IcfgLocation predecessor = predecessorTransition.getSource();
				final Term predecessorFrame = mFrames.get(predecessor).get(level - 1);
				final Term transition = predecessorTransition.getTransformula().getFormula();
				final Term primedtoBeBlocked = getPrimedTerm(toBeBlocked);
				final LBool result = SmtUtils.checkSatTerm(mScript.getScript(),
						SmtUtils.and(mScript.getScript(), predecessorFrame, transition, primedtoBeBlocked));
				// TODO: Handle result
				if (result == LBool.SAT) {
					/**
					 * Found Error trace
					 */
					if (level - 1 == 0) {
						return false;
					}

					final BasicPredicate pred = mPredicateFac.newPredicate(primedtoBeBlocked);
					/*
					 * How does the weakest Precondition work?
					 */
					final Term preCondition;
					if (predecessorTransition instanceof IIcfgInternalTransition) {
						preCondition = mPredTrans.weakestPrecondition(pred, predecessorTransition.getTransformula());
					} else if (predecessorTransition instanceof IIcfgCallTransition) {
						// TODO: get the stuff from the Icfg
						final TransFormula globalVarsAssignments = null;
						final TransFormula oldVarAssignments = null;
						final Set<IProgramNonOldVar> modifiableGlobals = null;
						preCondition = mPredTrans.weakestPreconditionCall(pred, predecessorTransition.getTransformula(),
								globalVarsAssignments, oldVarAssignments, modifiableGlobals);
					} else if (predecessorTransition instanceof IIcfgReturnTransition) {
						throw new UnsupportedOperationException();
					} else {
						throw new UnsupportedOperationException(
								"Unknown transition type: " + predecessorTransition.getClass().toString());
					}

					final Triple<Term, IcfgLocation, Integer> newProofObligation =
							new Triple<>(preCondition, predecessor, level - 1);
					proofObligations.addFirst(newProofObligation);
				}
			}
		}
		return true;
	}

	/**
	 * Propagation-Phase, for finding invariants
	 */
	private boolean propagationPhase() {
		for (final Entry<IcfgLocation, ArrayList<Term>> locationTrace : mFrames.entrySet()) {
			final ArrayList<Term> frames = locationTrace.getValue();
			for (int i = 0; i < frames.size(); i++) {
				for (int k = i + 1; k < frames.size(); k++) {
					if (frames.get(i) == frames.get(k)) {
						return true;
					}
				}
			}
		}
		return false;
	}

	private Term getPrimedTerm(final Term term) {
		return term;
	}

	private final class PdrResult {
		Map<LOC, Map<LOC, IPredicate>> mPredicates;
		Map<LOC, IcfgProgramExecution> mCounterexamples;
	}

}
