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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
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

	public Pdr(final ILogger logger, final IUltimateServiceProvider services, final Object settings) {
		mLogger = logger;
		mServices = services;
		mFrames = new HashMap<>();
		mScript = null;
	}

	PdrResult computePdr(final IIcfg<LOC> icfg, final IPredicateUnifier predicateUnifier) {
		final CfgSmtToolkit csToolkit = icfg.getCfgSmtToolkit();
		final BasicPredicateFactory predicateFac = predicateUnifier.getPredicateFactory();

		mScript = csToolkit.getManagedScript();

		final PredicateTransformer predTrans = new PredicateTransformer<>(mScript,
				new TermDomainOperationProvider(mServices, mScript));

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
			IcfgLocation loc = iter.next();
			mFrames.put(loc, new ArrayList<>());
			if (init.contains(loc)) {
				mFrames.get(loc).add(mScript.getScript().term("true"));
			} else {
				mFrames.get(loc).add(mScript.getScript().term("false"));
			}
		}

		while (true) {
			/**
			 * Initialize new level.
			 */
			for (Entry<IcfgLocation, ArrayList<Term>> trace : mFrames.entrySet()) {
				trace.getValue().add(mScript.getScript().term("true"));
			}

			final ArrayList<Triple<Term, IcfgLocation, Integer>> proofObligations = new ArrayList<>();

			/**
			 * Error Access violation:
			 */
//			for (final IcfgEdge edge : error.iterator().next().getIncomingEdges()) {
//				Term proofObligationTerm = edge.getTransformula().getFormula();
//			}

			/**
			 * Generated proof-obligation on level 0 -> error is reachable
			 */
			if (!blockingPhase(proofObligations)) {
				PdrResult result = new PdrResult();
				return result;
			}

			/**
			 * Found invariant -> error is not reachable
			 */
			if (propagationPhase()) {
				PdrResult result = new PdrResult();
				return result;
			}
		}
	}

	/**
	 * Blocking-phase, for blocking proof-obligations.
	 * 
	 * @return false, if proof-obligation on level 0 is created true, if there
	 *         is no proof-obligation left
	 */
	private boolean blockingPhase(final ArrayList<Triple<Term, IcfgLocation, Integer>> initialProofObligations) {
		Deque<Triple<Term, IcfgLocation, Integer>> proofObligations = new ArrayDeque<>(initialProofObligations);

		while (!proofObligations.isEmpty()) {
			Triple<Term, IcfgLocation, Integer> proofObligation = proofObligations.pop();
			final Term toBeBlocked = proofObligation.getFirst();
			final IcfgLocation location = proofObligation.getSecond();
			final int level = proofObligation.getThird();

			/**
			 * for (final IcfgLocation predecessor :
			 * location.getIncomingNodes()) {
			 * 
			 * }
			 */

		}

		return false;
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

	private final class PdrResult {
		Map<LOC, Map<LOC, IPredicate>> mPredicates;
		Map<LOC, IcfgProgramExecution> mCounterexamples;
	}

}
