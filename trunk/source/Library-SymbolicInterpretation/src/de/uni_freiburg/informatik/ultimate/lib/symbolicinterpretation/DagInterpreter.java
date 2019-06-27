/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing.CallReturnSummary;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.IDagOverlay;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagNode;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Interprets the dag of a single procedure.
 * Entered calls are processed by a given {@link IcfgInterpreter}.
 * Call summaries are computed by a given {@link ICallSummarizer}.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 */
public class DagInterpreter {

	private final ILogger mLogger;
	private final SymbolicTools mTools;
	private final IDomain mDomain;
	private final IFluid mFluid;
	private final InterpreterResources mInterpreterResources;
	private final TopsortCache mTopsortCache = new TopsortCache();

	public DagInterpreter(final ILogger logger, final SymbolicTools tools, final IDomain domain, final IFluid fluid,
			final InterpreterResources resources) {
		mLogger = logger;
		mTools = tools;
		mDomain = domain;
		mFluid = fluid;
		mInterpreterResources = resources;
	}

	/**
	 * Interprets a dag starting from its source node.
	 * 
	 * @param dag         Dag to be interpreted
	 * @param overlay     Overlay for the dag allowing to ignore some edges
	 * @param initalInput Input for the dag's source node
	 * @return Last computed output.
	 *         If The overlay creates a dag with exactly one sink node
	 *         then the returned output is the output of that sink node.
	 */
	public IPredicate interpret(final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay, final IPredicate initalInput) {
		final List<RegexDagNode<IIcfgTransition<IcfgLocation>>> topologicalOrder = mTopsortCache.topsort(dag);
		final IWorklistWithInputs<RegexDagNode<IIcfgTransition<IcfgLocation>>, IPredicate> worklist =
				new PriorityWorklist<>(topologicalOrder, mDomain::join);
		worklist.add(dag.getSource(), initalInput);
		IPredicate lastOutput = initalInput;
		while (worklist.advance()) {
			final RegexDagNode<IIcfgTransition<IcfgLocation>> currentNode = worklist.getWork();
			final IPredicate currentOutput = interpretNode(currentNode, worklist.getInput());
			overlay.successorsOf(currentNode).forEach(successor -> worklist.add(successor, currentOutput));
			lastOutput = currentOutput;
		}
		return lastOutput;
	}

	private IPredicate interpretNode(final RegexDagNode<IIcfgTransition<IcfgLocation>> node, final IPredicate input) {
		final IRegex<IIcfgTransition<IcfgLocation>> regex = node.getContent();
		if (regex instanceof Epsilon) {
			// nothing to do
			return input;
		} else if (regex instanceof Literal) {
			return interpretTransition(((Literal<IIcfgTransition<IcfgLocation>>) regex).getLetter(), input);
		} else if (regex instanceof Star) {
			return mInterpreterResources.getLoopSummarizer()
					.summarize((Star<IIcfgTransition<IcfgLocation>>) regex, input);
		} else {
			throw new UnsupportedOperationException("Unexpected node type in dag: " + regex.getClass());
		}
	}

	private IPredicate interpretTransition(final IIcfgTransition<IcfgLocation> transition, IPredicate input) {
		// TODO move up? Also interpret before stars
		input = fluidAbstraction(input);
		logInterpretTransition(transition, input);
		if (transition instanceof CallReturnSummary) {
			return interpretCallReturnSummary((CallReturnSummary) transition, input);
		} else if (transition instanceof IIcfgCallTransition<?>) {
			return interpretEnterCall((IIcfgCallTransition<IcfgLocation>) transition, input);
		} else if (transition instanceof IIcfgInternalTransition) {
			return interpretInternal((IIcfgInternalTransition<IcfgLocation>) transition, input);
		} else {
			// This case also includes LocationMarkerTransition. Markers should not be reachable in the overlay.
			// Markers are only used to find nodes after compression and to construct the overlay.
			throw new UnsupportedOperationException("Unexpected transition type: " + transition.getClass());
		}
	}

	private IPredicate interpretCallReturnSummary(final CallReturnSummary transition, final IPredicate input) {
		final IPredicate summary = mInterpreterResources.getCallSummarzier().summarize(transition, input);
		return mTools.postReturn(input, summary, transition.correspondingReturn());
	}

	private IPredicate interpretEnterCall(final IIcfgCallTransition<IcfgLocation> transition, final IPredicate input) {
		final IPredicate calleeInput = mTools.postCall(input, transition);
		mInterpreterResources.getIcfgInterpreter().registerEnterCall(transition.getSucceedingProcedure(), calleeInput);
		// registerEnterCall() already stores predicates for LOIs
		return calleeInput;
	}

	private IPredicate interpretInternal(final IIcfgInternalTransition<IcfgLocation> transition, final IPredicate input) {
		final IPredicate output = mTools.post(input, transition);
		logInterpretInternal(output);
		mInterpreterResources.getIcfgInterpreter().storePredicateIfLoi(transition.getTarget(), output);
		return output;
	}

	private IPredicate fluidAbstraction(IPredicate predicate) {
		mLogger.debug("Asking fluid if we should abstract");
		if (mFluid.shallBeAbstracted(predicate)) {
			predicate = mDomain.alpha(predicate);
			mLogger.debug("Abstraction is %s", predicate);
		}
		return predicate;
	}

	// log messages -------------------------------------------------------------------------------

	private void logInterpretTransition(final IIcfgTransition<IcfgLocation> transition, final IPredicate input) {
		mLogger.debug("Interpreting transition %s with input %s", transition, input);
	}

	private void logInterpretInternal(final IPredicate output) {
		mLogger.debug("Internal transition's output is %s", output);
	}
}
