/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.EmptySet;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.CallReturnSummary;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.LocationMarkerTransition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.IDagOverlay;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDag;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDagNode;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

/**
 * Interprets the DAG of a single procedure or loop.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class DagInterpreter {

	private final ILogger mLogger;
	private final SifaStats mStats;
	private final SymbolicTools mTools;
	private final IDomain mDomain;
	private final IFluid mFluid;
	private final TopsortCache mTopsortCache = new TopsortCache();
	private final ILoopSummarizer mLoopSummarizer;
	private final ICallSummarizer mCallSummarizer;
	private final IProgressAwareTimer mTimer;

	public DagInterpreter(final ILogger logger, final SifaStats stats, final IProgressAwareTimer timer,
			final SymbolicTools tools, final IDomain domain, final IFluid fluid,
			final Function<DagInterpreter, ILoopSummarizer> loopSumFactory,
			final Function<DagInterpreter, ICallSummarizer> callSumFactory) {
		mLogger = logger;
		mStats = stats;
		mTimer = timer;
		mTools = tools;
		mDomain = domain;
		mFluid = fluid;
		mLoopSummarizer = loopSumFactory.apply(this);
		mCallSummarizer = callSumFactory.apply(this);
	}

	/**
	 * Interprets a DAG with starting from its source node using only edges from the overlay
	 * and returns the computed predicate for the only marker in that overlay.
	 * Bottom is returned in case the overlay contained no marker or the marker was not reached.
	 * 
	 * @return Value of the sink location after interpreting the DAG
	 * @throws Exception The interpreter reached more than one marker in the overlay
	 */
	public IPredicate interpretForSingleMarker(final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay, final IPredicate initalInput) {
		final MapBasedStorage sinkPredStorage = new MapBasedStorage(mLogger);
		interpret(dag, overlay, initalInput, sinkPredStorage, ErrorOnEnterCall.instance());
		return sinkPredStorage.getSingletonOrDefault(mTools.bottom());
	}

	/**
	 * Interprets a DAG starting from its source node using only edges from the overlay.
	 * Results can be read from the given ILoiPredicateStorage.
	 * Calls are not entered but only registered in the given IEnterCallRegistrar.
	 * Registered calls should be processed after this function returns.
	 */
	public void interpret(final RegexDag<IIcfgTransition<IcfgLocation>> dag,
			final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay, final IPredicate initalInput,
			final ILoiPredicateStorage loiStorage, final IEnterCallRegistrar enterCallRegr) {

		// TODO should we use fluid and IDomain.alpha after join in worklist?
		final IWorklistWithInputs<RegexDagNode<IIcfgTransition<IcfgLocation>>, IPredicate> worklist =
				new PriorityWorklist<>(mTopsortCache.topsort(dag), mDomain::join);

		overlay.sources(dag).forEach(source -> worklist.add(source, initalInput));

		while (worklist.advance()) {
			respectTimeout();
			logWorklistEntry(worklist);
			final RegexDagNode<IIcfgTransition<IcfgLocation>> curNode = worklist.getWork();
			// TODO alternatively abstract outputs before putting them into the worklist
			final IPredicate curInput = fluidAbstraction(worklist.getInput());
			final IPredicate curOutput = ipretNode(curNode, curInput, loiStorage, enterCallRegr);
			logWorklistEntryDone(curOutput);
			if (earlyExitAfterStep(overlay, curNode, curOutput)) {
				continue;
			}
			overlay.successorsOf(curNode).forEach(successor -> worklist.add(successor, curOutput));
		}
	}

	private boolean earlyExitAfterStep(final IDagOverlay<IIcfgTransition<IcfgLocation>> overlay,
			final RegexDagNode<IIcfgTransition<IcfgLocation>> curNode, final IPredicate curOutput) {
		boolean earlyExit = mTools.isBottomLiteral(curOutput);
		// frequent non-trivial check would probably be more expensive than continued interpretation
		// ==> check only before branches
		if (!earlyExit && overlay.successorsOf(curNode).size() > 1) {
			mStats.increment(SifaStats.SifaMeasures.DAG_INTERPRETER_EARLY_EXIT_QUERIES_NONTRIVIAL);
			earlyExit = mDomain.isEqBottom(curOutput).isTrueForAbstraction();
		}
		if (earlyExit) {
			mStats.increment(SifaStats.SifaMeasures.DAG_INTERPRETER_EARLY_EXITS);
			logEarlyExitAfterStep();
		}
		return earlyExit;
	}

	private void respectTimeout() {
		// TODO return over-approximation instead of throwing an exception?
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
		} else if (regex instanceof EmptySet<?>) {
			// happens for instance when summarizing the procedure "f() { label: goto label; }"
			return mTools.bottom();
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
		logIpretLoop();
		final IPredicate loopSummary = mLoopSummarizer.summarize(loop, input);
		logIpretLoopDone();
		return loopSummary;
	}

	private IPredicate ipretTrans(final IIcfgTransition<IcfgLocation> trans, final IPredicate input,
			final ILoiPredicateStorage loiStorage, final IEnterCallRegistrar enterCallRegistrar) {
		if (trans instanceof IIcfgCallTransition<?>) {
			return ipretEnterCall((IIcfgCallTransition<IcfgLocation>) trans, input, enterCallRegistrar);
		}
		return ipretTransAndStoreLoiPred(trans, input, loiStorage);
	}

	private IPredicate ipretEnterCall(final IIcfgCallTransition<IcfgLocation> trans, final IPredicate input,
			final IEnterCallRegistrar enterCallRegistrar) {
		logRegisterEnterCall();
		final IPredicate calleeInput = mTools.postCall(input, trans);
		enterCallRegistrar.registerEnterCall(trans.getSucceedingProcedure(), calleeInput);
		// predicates for LOIs are stored once IcfgInterpreter enters the call
		logRegisterEnterCallDone();
		return calleeInput;
	}

	private IPredicate ipretTransAndStoreLoiPred(final IIcfgTransition<IcfgLocation> trans, final IPredicate input,
			final ILoiPredicateStorage loiStorage) {
		final IPredicate output;
		if (trans instanceof LocationMarkerTransition) {
			loiStorage.storePredicate(trans.getTarget(), input);
			output = input;
		} else if (trans instanceof CallReturnSummary) {
			output = ipretCallReturnSummary((CallReturnSummary) trans, input);
		} else if (trans instanceof IIcfgInternalTransition) {
			output = ipretInternal((IIcfgInternalTransition<IcfgLocation>) trans, input);
		} else {
			throw new UnsupportedOperationException("Unexpected transition type: " + trans.getClass());
		}
		return output;
	}

	private IPredicate ipretCallReturnSummary(final CallReturnSummary trans, final IPredicate input) {
		final IIcfgCallTransition<IcfgLocation> call = trans.correspondingCall();
		final IPredicate inputAfterCall = mTools.postCall(input, call);
		logIpretCallReturnQuery(inputAfterCall);
		final IPredicate summary = mCallSummarizer.summarize(call.getSucceedingProcedure(), inputAfterCall);
		logIpretCallReturnApply(summary);
		return mTools.postReturn(input, summary, trans.correspondingReturn());
	}

	private IPredicate ipretInternal(final IIcfgInternalTransition<IcfgLocation> trans, final IPredicate input) {
		logIpretInternal();
		final IPredicate output = mTools.post(input, trans);
		logIpretInternalDone();
		return output;
	}

	private IPredicate fluidAbstraction(IPredicate pred) {
		logConsiderAbstraction();
		if (mFluid.shallBeAbstracted(pred)) {
			logFluidAbstractionYes();
			pred = mDomain.alpha(pred);
			logFluidAbstractionDone(pred);
		} else {
			logFluidAbstractionNo();
		}
		return pred;
	}


	// log messages -------------------------------------------------------------------------------

	private void logWorklistEntry(
			final IWorklistWithInputs<RegexDagNode<IIcfgTransition<IcfgLocation>>, IPredicate> worklist) {
		mLogger.debug("●  Processing next worklist item %s with input %s",
				worklist.getWork().getContent(), worklist.getInput());
	}

	private void logWorklistEntryDone(final IPredicate curOutput) {
		mLogger.debug("Output of worklist entry is %s", curOutput);
	}

	private void logEarlyExitAfterStep() {
		mLogger.debug("Ignoring successors of the last worklist entry as its output was bottom.");
	}

	private void logConsiderAbstraction() {
		mLogger.debug("Asking fluid if we should abstract");
	}

	private void logFluidAbstractionYes() {
		mLogger.debug("Fluid: Yes, abstract");
	}

	private void logFluidAbstractionNo() {
		mLogger.debug("Fluid: No, don't abstract");
	}

	private void logFluidAbstractionDone(final IPredicate abstractedPred) {
		mLogger.debug("Fluid abstraction is %s", abstractedPred);
	}

	private void logIpretInternal() {
		mLogger.debug("→  Interpreting internal transition");
	}

	private void logIpretInternalDone() {
		mLogger.debug("→  Internal transition interpreted");
	}

	private void logIpretLoop() {
		mLogger.debug("⟲  Using loop summarizer");
	}

	private void logIpretLoopDone() {
		mLogger.debug("⟲  Loop summarizer finished");
	}

	private void logRegisterEnterCall() {
		mLogger.debug("Register enter call for later");
	}

	private static void logRegisterEnterCallDone() {
		// nothing to do
		// log message could be relevant if we interpreted registered entered calls immediately
	}

	private void logIpretCallReturnQuery(final IPredicate inputAfterCall) {
		mLogger.debug("⇵  Requesting call summary for input after call %s", inputAfterCall);
	}

	private void logIpretCallReturnApply(final IPredicate summary) {
		mLogger.debug("⇵  Apply call summary %s", summary);
	}
}
