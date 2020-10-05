/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AbstractResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.IResultWithCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.RtInconcistencyConditionGenerator.InvariantInfeasibleException;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheck;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckFailResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckRtInconsistentResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckSuccessResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.RequirementInconsistentErrorResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.RequirementTransformationErrorResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.RequirementTypeErrorResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Utility class that helps with reporting results.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PeaResultUtil {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private boolean mIsAborted;
	private final Set<String> mExprWithTypeErrors;

	public PeaResultUtil(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mIsAborted = false;
		mExprWithTypeErrors = new HashSet<>();
	}

	public boolean isAlreadyAborted() {
		return mIsAborted;
	}

	public void transformationError(final PatternType req, final String reason) {
		assert req != null;
		final IResult result = new RequirementTransformationErrorResult(req.getId(), reason);
		mLogger.warn(result.getLongDescription());
		report(result);
	}

	public void syntaxError(final ILocation location, final String description) {
		errorAndAbort(location, description, new SyntaxErrorResult(Activator.PLUGIN_ID, location, description));
	}

	public void typeError(final PatternType req, final String description) {
		typeError(req.getId(), description);
	}

	public void typeError(final String reqId, final String description) {
		errorAndAbort(new RequirementTypeErrorResult(reqId, description));
	}

	public void typeError(final String description, final Expression expr) {
		if (mExprWithTypeErrors.add(expr.toString())) {
			errorAndAbort(new RequirementTypeErrorResult(expr.getLoc().getStartLine(),
					BoogiePrettyPrinter.print(expr) + " :" + description));
		}
	}

	public void intrinsicRtConsistencySuccess(final IElement element) {
		final String plugin = Activator.PLUGIN_ID;
		final IBacktranslationService translatorSequence = mServices.getBacktranslationService();
		report(new ReqCheckSuccessResult<>(element, plugin, translatorSequence));
	}

	public void infeasibleInvariant(final InvariantInfeasibleException ex) {
		errorAndAbort(new RequirementInconsistentErrorResult(ex));
	}

	public IResult convertTraceAbstractionResult(final IResult result) {
		final AbstractResultAtElement<?> oldRes;
		final ReqCheck reqCheck;
		boolean isPositive;
		if (result instanceof CounterExampleResult<?, ?, ?>) {
			oldRes = (AbstractResultAtElement<?>) result;
			reqCheck = (ReqCheck) ((IResultWithCheck) result).getCheckedSpecification();
			isPositive = false;
		} else if (result instanceof PositiveResult<?>) {
			oldRes = (AbstractResultAtElement<?>) result;
			reqCheck = (ReqCheck) ((IResultWithCheck) result).getCheckedSpecification();
			isPositive = true;
		} else if (result instanceof AllSpecificationsHoldResult) {
			// makes no sense in our context, suppress it
			return null;
		} else {
			return result;
		}

		final Set<Spec> specs = reqCheck.getSpec();
		if (specs == null || specs.isEmpty()) {
			throw new AssertionError("Result without specification: " + oldRes.getShortDescription());
		} else if (specs.size() == 1) {
			final Spec spec = specs.iterator().next();
			dieIfUnsupported(spec);

			if (spec == Spec.CONSISTENCY || spec == Spec.VACUOUS) {
				// a counterexample for consistency and vacuity means that the requirements are consistent or
				// non-vacuous
				isPositive = !isPositive;
			}
			final IElement element = oldRes.getElement();
			final String plugin = oldRes.getPlugin();
			final IBacktranslationService translatorSequence = oldRes.getCurrentBacktranslation();

			if (isPositive) {
				return new ReqCheckSuccessResult<>(element, plugin, translatorSequence);
			}

			if (spec == Spec.RTINCONSISTENT) {
				@SuppressWarnings("unchecked")
				final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> newPe = generateRtInconsistencyResult(
						((CounterExampleResult<?, IIcfgTransition<IcfgLocation>, Term>) oldRes).getProgramExecution(),
						reqCheck);
				return new ReqCheckRtInconsistentResult<>(element, plugin, translatorSequence, newPe);

			}
			return new ReqCheckFailResult<>(element, plugin, translatorSequence);

		} else {
			throw new UnsupportedOperationException("Multi-checks of " + specs + " are not yet supported");
		}
	}

	private static void dieIfUnsupported(final Spec spec) {
		switch (spec) {
		case CONSISTENCY:
		case VACUOUS:
		case RTINCONSISTENT:
			return;
		default:
			throw new UnsupportedOperationException("Unknown spec type " + spec);
		}
	}

	private IProgramExecution<IIcfgTransition<IcfgLocation>, Term> generateRtInconsistencyResult(
			final IProgramExecution<IIcfgTransition<IcfgLocation>, Term> pe, final ReqCheck reqCheck) {
		final List<CodeBlock> trace = new ArrayList<>(pe.getLength());
		pe.stream().map(a -> (CodeBlock) a.getTraceElement())
				.filter(a -> !"true".equals(a.getTransformula().getClosedFormula().toString())).forEach(trace::add);
		mLogger.info(reqCheck.getIds());

		trace.stream().forEach(a -> mLogger.info("In: %s Out: %s", a.getTransformula().getInVars().keySet(),
				a.getTransformula().getOutVars().keySet()));

		final CodeBlockFactory cbf = CodeBlockFactory.getFactory((IToolchainStorage) mServices);
		final CfgSmtToolkit toolkit = cbf.getToolkit();

		final ManagedScript mgdScript = toolkit.getManagedScript();
		final Script script = mgdScript.getScript();
		final BasicPredicateFactory bpf = new BasicPredicateFactory(mServices, mgdScript, toolkit.getSymbolTable());
		final BasicPredicate truePred = bpf.newPredicate(script.term("true"));
		final BasicPredicate falsePred = bpf.newPredicate(script.term("false"));

		final AssertCodeBlockOrder assertionOrder =
				new AssertCodeBlockOrder(AssertCodeBlockOrderType.NOT_INCREMENTALLY);
		final List<List<IAction>> flattenedTraces = flattenTrace(trace);
		mLogger.info("Checking %s flattened traces", flattenedTraces.size());
		// TODO: Makes no sense to construct that many traces -- either check them incrementally or do something else
		// differently.
		final int limit = 1024;
		if (flattenedTraces.size() > limit) {
			mLogger.warn("Too many flattened traces, just looking at the first %s", limit);
		}
		for (final List<IAction> flatTrace : flattenedTraces) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				mLogger.warn("Took too long looking at flattened traces, bailing...");
				break;
			}
			final TraceCheck<IAction> tc = new TraceCheck<>(truePred, falsePred, new TreeMap<>(),
					NestedWord.nestedWord(new Word<>(flatTrace.toArray(new IAction[flatTrace.size()]))), mServices,
					toolkit, assertionOrder, true, false);
			if (tc.isCorrect() == LBool.SAT) {
				return tc.getRcfgProgramExecution();
			}
		}
		// give up if we took too long
		return pe;
	}

	/**
	 * TODO: Rather inefficient to compute all combinations and then check. Better: compute combinations iteratively and
	 * take the first that is sat.
	 */
	private List<List<IAction>> flattenTrace(final List<CodeBlock> trace) {
		List<List<IAction>> rtr = new ArrayList<>();
		for (final CodeBlock cb : trace) {
			if (cb instanceof SequentialComposition) {
				rtr = DataStructureUtils.crossProduct(rtr, flattenTrace(((SequentialComposition) cb).getCodeBlocks()));
			} else if (cb instanceof ParallelComposition) {
				final List<CodeBlock> blocks = ((ParallelComposition) cb).getCodeBlocks();
				final List<List<IAction>> newRtr = new ArrayList<>();
				for (final CodeBlock block : blocks) {
					newRtr.addAll(DataStructureUtils.crossProduct(rtr, flattenTrace(Collections.singletonList(block))));
				}
				rtr = newRtr;
			} else {
				rtr = DataStructureUtils.crossProduct(rtr, Collections.singletonList(Collections.singletonList(cb)));
			}
		}
		return rtr;
	}

	private void errorAndAbort(final IResult result) {
		mLogger.error(result.getLongDescription());
		report(result);
		mServices.getProgressMonitorService().cancelToolchain();
		mIsAborted = true;
	}

	private void errorAndAbort(final ILocation location, final String description, final IResult result) {
		mLogger.error(location + ": " + description);
		report(result);
		mServices.getProgressMonitorService().cancelToolchain();
		mIsAborted = true;
	}

	private void report(final IResult result) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}

}
