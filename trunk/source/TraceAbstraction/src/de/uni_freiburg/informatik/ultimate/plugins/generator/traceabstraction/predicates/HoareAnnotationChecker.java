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

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;

/**
 * Check inductivity of a CFG's Hoare annotation.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class HoareAnnotationChecker {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final RootNode mRootNode;
	private final boolean mIsInductive;
	
	

	public HoareAnnotationChecker(IUltimateServiceProvider services, RootNode rootNode, CfgSmtToolkit csToolkit) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRootNode = rootNode;
		mHoareTripleChecker = new MonolithicHoareTripleChecker(csToolkit.getManagedScript(), 
				csToolkit.getModifiableGlobals());
		mIsInductive = cfgInductive(mRootNode);
	}

	private boolean cfgInductive(RootNode rootNode) {
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

		final List<RCFGNode> initialNodes = rootNode.getOutgoingNodes();
		final Set<ProgramPoint> visited = new HashSet<ProgramPoint>();
		final List<ProgramPoint> worklist = new LinkedList<ProgramPoint>();

		if (initialNodes != null) {
			for (final RCFGNode initINode : initialNodes) {
				final ProgramPoint initNode = (ProgramPoint) initINode;
				visited.add(initNode);
				worklist.add(initNode);
			}
		} else {
			mLogger.warn("There was no procedure with an implementation");
		}
		while (!worklist.isEmpty()) {
			final ProgramPoint locNode = worklist.remove(0);
			for (final RCFGEdge iEdge : locNode.getOutgoingEdges()) {

				final RCFGNode iSuccLoc = iEdge.getTarget();
				final ProgramPoint succLoc = (ProgramPoint) iSuccLoc;
				if (!visited.contains(succLoc)) {
					visited.add(succLoc);
					worklist.add(succLoc);
				}

				final IPredicate sf1 = HoareAnnotation.getAnnotation(locNode);
				if (sf1 == null) {
					mLogger.warn(locNode + " has no Hoare annotation");
					continue;
				}

				final IPredicate sf2 = HoareAnnotation.getAnnotation(succLoc);
				if (sf2 == null) {
					mLogger.warn(succLoc + " has no Hoare annotation");
					continue;
				}

				final Validity inductivity;
				final IAction action;
				if (iEdge instanceof ICallAction) {
					action = ((ICallAction) iEdge);
					inductivity = mHoareTripleChecker.checkCall(sf1, (ICallAction) action, sf2);
				} else if (iEdge instanceof Return) {
					final ProgramPoint callerNode = ((Return) iEdge).getCallerProgramPoint();
					final IPredicate sfk = HoareAnnotation.getAnnotation(callerNode);
					if (sfk == null) {
						mLogger.warn(callerNode + " has no Hoare annotation");
						continue;
					}
					action = ((IReturnAction) iEdge);
					inductivity = mHoareTripleChecker.checkReturn(sf1, sfk, (IReturnAction) action, sf2);
				} else if (iEdge instanceof Summary) {
					action = ((Summary) iEdge);
					if (((Summary) action).calledProcedureHasImplementation()) {
						continue;
					} else {
						inductivity = mHoareTripleChecker.checkInternal(sf1, (IInternalAction) action, sf2);
					}
				} else if (iEdge instanceof CodeBlock) {
					action = ((CodeBlock) iEdge);
					inductivity = mHoareTripleChecker.checkInternal(sf1, (IInternalAction) action, sf2);
				} else {
					continue;
				}

				switch (inductivity) {
				case VALID: {
					yield[0]++;
					break;
				}
				case INVALID: {
					yield[1]++;
					mLogger.warn("Transition   " + action + "   from   " + sf1 + "   to   " + sf2
							+ "   not inductive");
					result = false;
					break;
				}
				case UNKNOWN: {
					yield[2]++;
					// s_Logger.warn("Theorem prover too weak to decide inductiveness");
					break;
				}
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

	public boolean isInductive() {
		return mIsInductive;
	}
	
}
