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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
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
	private final Map<IcfgLocation, List<Term>> mFrames;
	private final ManagedScript mScript;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTrans;
	private final IIcfg<LOC> mIcfg;
	private final CfgSmtToolkit mCsToolkit;
	private final IHoareTripleChecker mHtc;
	private final IPredicateUnifier mPredicateUnifier;

	public Pdr(final ILogger logger, final IUltimateServiceProvider services, final IIcfg<LOC> icfg,
			final IPredicateUnifier predicateUnifier, final IHoareTripleChecker htc, final Object settings) {
		mLogger = logger;
		mServices = services;
		mFrames = new HashMap<>();
		mCsToolkit = icfg.getCfgSmtToolkit();
		mScript = mCsToolkit.getManagedScript();
		mPredicateUnifier = predicateUnifier;
		mPredTrans = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));
		mIcfg = icfg;
		mHtc = htc;
		computePdr();
	}

	private PdrResult computePdr() {

		final Set<LOC> init = mIcfg.getInitialNodes();
		final Set<LOC> error = IcfgUtils.getErrorLocations(mIcfg);

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
		final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(mIcfg);
		while (iter.hasNext()) {
			final IcfgLocation loc = iter.next();
			mFrames.put(loc, new ArrayList<>());
			if (init.contains(loc)) {
				mFrames.get(loc).add(mScript.getScript().term("true"));
			} else {
				mFrames.get(loc).add(mScript.getScript().term("false"));
			}
		}

		Integer level = 0;

		while (true) {
			/**
			 * Initialize new level.
			 */
			for (final Entry<IcfgLocation, List<Term>> trace : mFrames.entrySet()) {
				trace.getValue().add(mScript.getScript().term("true"));
			}

			level += 1;

			final List<Triple<Term, IcfgLocation, Integer>> proofObligations = new ArrayList<>();

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
	private boolean blockingPhase(final List<Triple<Term, IcfgLocation, Integer>> initialProofObligations) {

		final Deque<Triple<Term, IcfgLocation, Integer>> proofObligations = new ArrayDeque<>(initialProofObligations);
		final BasicPredicateFactory prefac = mPredicateUnifier.getPredicateFactory();
		while (!proofObligations.isEmpty()) {
			final Triple<Term, IcfgLocation, Integer> proofObligation = proofObligations.pop();
			final Term toBeBlocked = proofObligation.getFirst();
			final IcfgLocation location = proofObligation.getSecond();
			final int level = proofObligation.getThird();

			for (final IcfgEdge predecessorTransition : location.getIncomingEdges()) {
				final IcfgLocation predecessor = predecessorTransition.getSource();
				final Term predecessorFrame = mFrames.get(predecessor).get(level - 1);
				final Term transition = predecessorTransition.getTransformula().getFormula();

				// convert all terms that should be used in htc to predicates
				// Note: HTC checks P && S && !Q, so we have to negate the postcondition
				// negate postcondition with notP=mPredicateUnifier.getPredicateFactory().not(p) and
				// mPredicateUnifier.getOrConstruct(notP)
				//
				final Validity result = mHtc.checkInternal((IPredicate) predecessorFrame,
						(IInternalAction) predecessorTransition, (IPredicate) toBeBlocked);
				// final LBool result = SmtUtils.checkSatTerm(mScript.getScript(),
				// SmtUtils.and(mScript.getScript(), predecessorFrame, transition, primedtoBeBlocked));
				/**
				 * If Sat generate new proof-obligation
				 */
				if (result == Validity.INVALID) {
					/**
					 * Found Error trace
					 */
					if (level - 1 == 0) {
						return false;
					}

					final BasicPredicate pred = prefac.newPredicate(toBeBlocked);

					final Term preCondition;

					if (predecessorTransition instanceof IIcfgInternalTransition) {
						preCondition = mPredTrans.weakestPrecondition(pred, predecessorTransition.getTransformula());

					} else if (predecessorTransition instanceof IIcfgCallTransition) {
						final TransFormula globalVarsAssignments = mCsToolkit.getOldVarsAssignmentCache()
								.getGlobalVarsAssignment(predecessorTransition.getSucceedingProcedure());
						final TransFormula oldVarAssignments = mCsToolkit.getOldVarsAssignmentCache()
								.getOldVarsAssignment(predecessorTransition.getSucceedingProcedure());
						final Set<IProgramNonOldVar> modifiableGlobals = mCsToolkit.getModifiableGlobalsTable()
								.getModifiedBoogieVars(predecessorTransition.getSucceedingProcedure());
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

					/**
					 * If Unsat strengthen the frames of the location
					 */
				} else if (result == Validity.VALID) {
					for (int i = 0; i <= level; i++) {
						Term fTerm = mFrames.get(location).get(i);
						final Term negToBeBlocked = SmtUtils.neg(mScript.getScript(), toBeBlocked);
						fTerm = SmtUtils.and(mScript.getScript(), fTerm, negToBeBlocked);
						mFrames.get(location).set(i, fTerm);
					}
				} else {
					/**
					 * What do if unknown?
					 *
					 */
					throw new UnsupportedOperationException("what to do with unknown?");
				}
			}
		}
		return true;
	}

	/**
	 * Propagation-Phase, for finding invariants
	 */
	private boolean propagationPhase() {
		for (final Entry<IcfgLocation, List<Term>> locationTrace : mFrames.entrySet()) {
			final List<Term> frames = locationTrace.getValue();
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

	private final class PdrResult {
		Map<LOC, Map<LOC, IPredicate>> mPredicates;
		Map<LOC, IcfgProgramExecution> mCounterexamples;
	}

}
