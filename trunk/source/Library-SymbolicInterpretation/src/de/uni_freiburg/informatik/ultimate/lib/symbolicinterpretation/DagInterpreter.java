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

import java.util.Collections;
import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
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
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagUtils;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.ILoopSummarizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Interprets the dag of a single procedure or loop.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class DagInterpreter {

	private final ILogger mLogger;
	private final SymbolicTools mTools;
	private final IDomain mDomain;
	private final IFluid mFluid;
	private final TopsortCache mTopsortCache = new TopsortCache();
	private final ILoopSummarizer mLoopSummarizer;
	private final ICallSummarizer mCallSummarizer;
	private final IProgressAwareTimer mTimer;

	public DagInterpreter(final ILogger logger, final IProgressAwareTimer timer, final SymbolicTools tools,
			final IDomain domain, final IFluid fluid,
			final Function<DagInterpreter, ILoopSummarizer> loopSumFactory,
			final Function<DagInterpreter, ICallSummarizer> callSumFactory) {
		mLogger = logger;
		mTimer = timer;
		mTools = tools;
		mDomain = domain;
		mFluid = fluid;
		mLoopSummarizer = loopSumFactory.apply(this);
		mCallSummarizer = callSumFactory.apply(this);
	}

	public IPredicate interpret(final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay, final IPredicate initalInput) {
		final MapBasedStorage sinkPredStorage = new MapBasedStorage(
				Collections.singleton(RegexDagUtils.singleSinkLocation(dag, overlay)), mDomain, mTools, mLogger);
		interpret(dag, overlay, initalInput, sinkPredStorage, new ErrorOnEnterCall());
		return sinkPredStorage.getMap().values().iterator().next();
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
	public void interpret(final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay, final IPredicate initalInput,
			final ILoiPredicateStorage loiStorage, final IEnterCallRegistrar enterCallRegr) {
		final List<RegexDagNode<IIcfgTransition<IcfgLocation>>> topoOrder = mTopsortCache.topsort(dag);
		final IWorklistWithInputs<RegexDagNode<IIcfgTransition<IcfgLocation>>, IPredicate> worklist =
				new PriorityWorklist<>(topoOrder, mDomain::join);
		worklist.add(dag.getSource(), initalInput);
		while (worklist.advance()) {
			respectTimeout();
			final RegexDagNode<IIcfgTransition<IcfgLocation>> curNode = worklist.getWork();
			final IPredicate curOutput = ipretNode(curNode, worklist.getInput(), loiStorage, enterCallRegr);
			overlay.successorsOf(curNode).forEach(successor -> worklist.add(successor, curOutput));
		}
	}

	private void respectTimeout() {
		if (!mTimer.continueProcessing()) {
			mLogger.warn("Timeout while interpreting dag");
			throw new ToolchainCanceledException(getClass());
		}
	}

	private IPredicate ipretNode(final RegexDagNode<IIcfgTransition<IcfgLocation>> node, final IPredicate input,
			final ILoiPredicateStorage loiStorage, final IEnterCallRegistrar enterCallRegr) {
		final IRegex<IIcfgTransition<IcfgLocation>> regex = node.getContent();
		if (regex instanceof Epsilon) {
			return input;
		} else if (regex instanceof Literal) {
			return ipretTrans(((Literal<IIcfgTransition<IcfgLocation>>) regex).getLetter(),
					input, loiStorage, enterCallRegr);
		} else if (regex instanceof Star) {
			return ipretLoop((Star<IIcfgTransition<IcfgLocation>>) regex, input, loiStorage);
		} else {
			throw new UnsupportedOperationException("Unexpected node type in dag: " + regex.getClass());
		}
	}

	private IPredicate ipretLoop(final Star<IIcfgTransition<IcfgLocation>> loop, final IPredicate input,
			final ILoiPredicateStorage loiStorage) {
		final IPredicate loopSummary = mLoopSummarizer.summarize(loop, input);
		registerLoiPredsForLoop(loop, loopSummary, loiStorage);
		return loopSummary;
	}

	private static void registerLoiPredsForLoop(final Star<IIcfgTransition<IcfgLocation>> loop,
			final IPredicate loopSummary, final ILoiPredicateStorage loiStorage) {
		final IcfgLocation loopPoint = loop.accept(new LoopPointVisitor());
		loiStorage.storePredicateIfLoi(loopPoint, loopSummary);
		// LOIs inside loops don't have to be considered.
		// For each LOI we compute a path ending at that LOI. A path cannot end inside a loop.
	}

	private IPredicate ipretTrans(final IIcfgTransition<IcfgLocation> trans, IPredicate input,
			final ILoiPredicateStorage loiStorage, final IEnterCallRegistrar enterCallRegistrar) {
		// TODO move abstraction up? Also abstract before stars?
		input = fluidAbstraction(input);
		logIpretTransition(trans, input);
		if (trans instanceof IIcfgCallTransition<?>) {
			return ipretEnterCall((IIcfgCallTransition<IcfgLocation>) trans, input, enterCallRegistrar);
		}
		return ipretTransAndStoreLoiPred(trans, input, loiStorage);
	}

	private IPredicate ipretEnterCall(final IIcfgCallTransition<IcfgLocation> trans, final IPredicate input,
			final IEnterCallRegistrar enterCallRegistrar) {
		final IPredicate calleeInput = mTools.postCall(input, trans);
		enterCallRegistrar.registerEnterCall(trans.getSucceedingProcedure(), calleeInput);
		// predicates for LOIs are stored once IcfgInterpreter enters the call
		return calleeInput;
	}

	private IPredicate ipretTransAndStoreLoiPred(final IIcfgTransition<IcfgLocation> trans, final IPredicate input,
			final ILoiPredicateStorage loiStorage) {
		final IPredicate output;
		if (trans instanceof CallReturnSummary) {
			output = ipretCallReturnSummary((CallReturnSummary) trans, input);
		} else if (trans instanceof IIcfgInternalTransition) {
			output = ipretInternal((IIcfgInternalTransition<IcfgLocation>) trans, input);
		} else {
			// This case also includes LocationMarkerTransition. Markers should not be reachable in the overlay.
			// Markers are only used to find nodes after compression and to construct the overlay.
			throw new UnsupportedOperationException("Unexpected transition type: " + trans.getClass());
		}
		loiStorage.storePredicateIfLoi(trans.getTarget(), output);
		return output;
	}

	private IPredicate ipretCallReturnSummary(final CallReturnSummary trans, final IPredicate input) {
		final IPredicate summary = mCallSummarizer.summarize(trans, input);
		final IPredicate output = mTools.postReturn(input, summary, trans.correspondingReturn());
		logIpretCallReturnSummary(summary, output);
		return output;
	}

	private IPredicate ipretInternal(final IIcfgInternalTransition<IcfgLocation> trans, final IPredicate input) {
		final IPredicate output = mTools.post(input, trans);
		logIpretInternal(output);
		return output;
	}

	private IPredicate fluidAbstraction(IPredicate pred) {
		logConsiderAbstraction();
		if (mFluid.shallBeAbstracted(pred)) {
			pred = mDomain.alpha(pred);
			logAbstractionDone(pred);
		}
		return pred;
	}

	// log messages -------------------------------------------------------------------------------

	private void logConsiderAbstraction() {
		mLogger.debug("Asking fluid if we should abstract");
	}

	private void logAbstractionDone(final IPredicate abstractedPred) {
		mLogger.debug("Abstraction is %s", abstractedPred);
	}

	private void logIpretTransition(final IIcfgTransition<IcfgLocation> transition, final IPredicate input) {
		mLogger.debug("Interpreting transition %s with input %s", transition, input);
	}

	private void logIpretInternal(final IPredicate output) {
		mLogger.debug("Internal transition's output is %s", output);
	}

	private void logIpretCallReturnSummary(final IPredicate summary, final IPredicate output) {
		mLogger.debug("Call return summary is %s", summary);
		mLogger.debug("After \"call … := …\" was applied output is %s", output);
	}
}
