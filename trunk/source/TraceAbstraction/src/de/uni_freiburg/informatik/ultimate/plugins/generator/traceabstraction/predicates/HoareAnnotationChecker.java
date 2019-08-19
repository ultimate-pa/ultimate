/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;

/**
 * Check inductivity of a CFG's Hoare annotation.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class HoareAnnotationChecker {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final IIcfg<?> mRootNode;
	private final boolean mIsInductive;

	public HoareAnnotationChecker(final IUltimateServiceProvider services, final IIcfg<?> rootNode,
			final CfgSmtToolkit csToolkit) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRootNode = rootNode;
		mHoareTripleChecker = new MonolithicHoareTripleChecker(csToolkit);
		mIsInductive = cfgInductive(mRootNode);
	}

	private boolean cfgInductive(final IIcfg<?> rootNode) {
		boolean result = true;
		// yield[0] is the number of edges whose inductiveness could be
		// proven
		// yield[1] is the number of edges whose inductiveness could be
		// refuted
		// yield[2] is the number of edges whose inductiveness could be
		// neither proven nor refuted because theorem prover too weak
		// yield[3] is the number of edges whose inductiveness could be
		// neither proven nor refuted because there were no interpolants
		final int[] yield = new int[4];

		final List<IcfgLocation> initialNodes = new ArrayList<>(rootNode.getProcedureEntryNodes().values());
		final Set<IcfgLocation> visited = new HashSet<>();
		final Deque<IcfgLocation> worklist = new ArrayDeque<>();

		if (initialNodes.isEmpty()) {
			mLogger.warn("There was no procedure with an implementation");
		}

		for (final IcfgLocation initialNode : initialNodes) {
			visited.add(initialNode);
			worklist.add(initialNode);
		}

		while (!worklist.isEmpty()) {
			final IcfgLocation sourceLoc = worklist.removeFirst();
			for (final IcfgEdge outEdge : sourceLoc.getOutgoingEdges()) {
				final IcfgLocation targetLoc = outEdge.getTarget();
				if (visited.add(targetLoc)) {
					worklist.add(targetLoc);
				}

				final IPredicate pre = HoareAnnotation.getAnnotation(sourceLoc);
				if (pre == null) {
					warnNoAnnotation(sourceLoc);
					continue;
				}

				final IPredicate post = HoareAnnotation.getAnnotation(targetLoc);
				if (post == null) {
					warnNoAnnotation(targetLoc);
					continue;
				}

				final Validity inductivity;
				if (outEdge instanceof IIcfgInternalTransition<?>) {
					if (outEdge instanceof Summary && ((Summary) outEdge).calledProcedureHasImplementation()) {
						continue;
					}
					inductivity = mHoareTripleChecker.checkInternal(pre, (IInternalAction) outEdge, post);
				} else if (outEdge instanceof ICallAction) {
					inductivity = mHoareTripleChecker.checkCall(pre, (ICallAction) outEdge, post);
				} else if (outEdge instanceof IIcfgReturnTransition<?, ?>) {
					final IcfgLocation callerNode = ((IIcfgReturnTransition<?, ?>) outEdge).getCallerProgramPoint();
					final IPredicate hierPre = HoareAnnotation.getAnnotation(callerNode);
					if (hierPre == null) {
						warnNoAnnotation(callerNode);
						continue;
					}
					inductivity = mHoareTripleChecker.checkReturn(pre, hierPre, (IReturnAction) outEdge, post);
				} else {
					continue;
				}

				switch (inductivity) {
				case VALID:
					yield[0]++;
					break;
				case INVALID:
					yield[1]++;
					mLogger.warn(
							"Transition   " + outEdge + "   from   " + pre + "   to   " + post + "   not inductive");
					result = false;
					break;
				case UNKNOWN:
					yield[2]++;
					break;
				default:
					throw new IllegalArgumentException();
				}
			}
		}
		mLogger.info("CFG has " + (yield[0] + yield[1] + yield[2] + yield[3]) + " edges. " + yield[0] + " inductive. "
				+ yield[1] + " not inductive. " + yield[2] + " times theorem prover too"
				+ " weak to decide inductivity. " + yield[3] + " times interpolants" + " missing.");
		return result;
	}

	private void warnNoAnnotation(final IcfgLocation sourceLoc) {
		mLogger.warn(sourceLoc + " has no Hoare annotation");
	}

	public boolean isInductive() {
		return mIsInductive;
	}

}
