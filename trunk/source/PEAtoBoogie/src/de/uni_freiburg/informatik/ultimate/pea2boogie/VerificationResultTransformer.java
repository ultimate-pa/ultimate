/*
 * Copyright (C) 2018-2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018-2020 University of Freiburg
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
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AbstractResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.IResultWithCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrderType;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheck;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckFailResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckRtInconsistentResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheckSuccessResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * Utility class that helps with reporting results.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class VerificationResultTransformer {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final UnionFind<String> mEquivalences;

	public VerificationResultTransformer(final ILogger logger, final IUltimateServiceProvider services,
			final List<ReqPeas> reqPeas) {
		mLogger = logger;
		mServices = services;
		mEquivalences = findEquivalences(reqPeas);
	}

	private static UnionFind<String> findEquivalences(final List<ReqPeas> reqPeas) {
		final UnionFind<String> uf = new UnionFind<>();
		for (final ReqPeas reqpea : reqPeas) {
			for (final Entry<CounterTrace, PhaseEventAutomata> ct2pea : reqpea.getCounterTrace2Pea()) {
				final PhaseEventAutomata somePea = ct2pea.getValue();

				final Set<String> peaVars = new HashSet<>();
				// add all variable names
				peaVars.addAll(somePea.getVariables().keySet());
				// add all clock names
				peaVars.addAll(somePea.getClocks());
				// add pc name
				peaVars.add(ReqSymboltableBuilder.getPcName(somePea));

				peaVars.forEach(uf::findAndConstructEquivalenceClassIfNeeded);
				uf.union(peaVars);
			}
		}
		return uf;
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
				final IProgramExecution<IAction, Term> newPe = generateRtInconsistencyResult(
						(IcfgProgramExecution<? extends IAction>) ((CounterExampleResult<?, ?, Term>) oldRes)
								.getProgramExecution(),
						reqCheck);
				return new ReqCheckRtInconsistentResult<>(element, plugin, translatorSequence, newPe);

			}
			return new ReqCheckFailResult<>(element, plugin, translatorSequence);

		} else {
			throw new UnsupportedOperationException("Multi-checks of " + specs + " are not yet supported");
		}
	}

	private IProgramExecution<IAction, Term> generateRtInconsistencyResult(final IcfgProgramExecution<?> pe,
			final ReqCheck reqCheck) {
		final List<CodeBlock> trace = new ArrayList<>(pe.getLength());
		pe.stream().map(a -> (CodeBlock) a.getTraceElement()).forEach(trace::add);

		final CodeBlockFactory cbf = CodeBlockFactory.getFactory((IToolchainStorage) mServices);
		final CfgSmtToolkit toolkit = cbf.getToolkit();

		final ManagedScript mgdScript = toolkit.getManagedScript();
		final Script script = mgdScript.getScript();
		final BasicPredicateFactory bpf = new BasicPredicateFactory(mServices, mgdScript, toolkit.getSymbolTable());
		final BasicPredicate truePred = bpf.newPredicate(script.term("true"));
		final BasicPredicate falsePred = bpf.newPredicate(script.term("false"));

		final AssertCodeBlockOrder assertionOrder =
				new AssertCodeBlockOrder(AssertCodeBlockOrderType.NOT_INCREMENTALLY);

		// first, recheck to ensure that we have branch encoders
		final TraceCheck<IAction> tcl = new TraceCheck<>(truePred, falsePred, new TreeMap<Integer, IPredicate>(),
				NestedWord.nestedWord(new Word<>(trace.toArray(new IAction[trace.size()]))), mServices, toolkit,
				assertionOrder, true, false);

		final List<IAction> sequentialTrace = extractSequential(tcl.getRcfgProgramExecution(), mgdScript);
		// sequentialTrace.forEach(
		// a -> mLogger.info("In %s Out %s", a.getTransformula().getInVars(), a.getTransformula().getOutVars()));

		final List<IAction> cleanedTrace = removeUnrelatedVariables(sequentialTrace, reqCheck, mgdScript);

		final TraceCheck<IAction> tc = new TraceCheck<>(truePred, falsePred, new TreeMap<Integer, IPredicate>(),
				NestedWord.nestedWord(new Word<>(cleanedTrace.toArray(new IAction[cleanedTrace.size()]))), mServices,
				toolkit, assertionOrder, true, false);
		if (tc.isCorrect() == LBool.SAT) {
			return tc.getRcfgProgramExecution();
		}
		throw new AssertionError("Expected branch is not SAT");
	}

	private List<IAction> removeUnrelatedVariables(final List<IAction> sequentialTrace, final ReqCheck reqCheck,
			final ManagedScript mgdScript) {
		final String firstPeaName = ReqSymboltableBuilder.getPcName(reqCheck.getPeaNames().iterator().next());
		final Set<String> equivClass = mEquivalences.getContainingSet(firstPeaName);
		assert equivClass.containsAll(
				reqCheck.getPeaNames().stream().map(ReqSymboltableBuilder::getPcName).collect(Collectors.toSet()));

		final List<IAction> rtr = new ArrayList<>();
		for (final IAction action : sequentialTrace) {
			final UnmodifiableTransFormula oldTf = action.getTransformula();

			final Set<IProgramConst> nonTheoryConsts = oldTf.getNonTheoryConsts();
			final boolean emptyNonTheoryConsts = nonTheoryConsts.isEmpty();
			final Collection<TermVariable> branchEncoders = oldTf.getBranchEncoders();
			final boolean emptyBranchEncoders = branchEncoders.isEmpty();
			final boolean emptyAuxVars = oldTf.getAuxVars().isEmpty();
			final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, emptyNonTheoryConsts, nonTheoryConsts,
					emptyBranchEncoders, branchEncoders, emptyAuxVars);
			tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);

			final Term oldFormula = oldTf.getFormula();
			final Set<TermVariable> toRemove = new LinkedHashSet<>();
			for (final Entry<IProgramVar, TermVariable> entry : oldTf.getInVars().entrySet()) {
				if (!equivClass.contains(entry.getKey().toString())) {
					toRemove.add(entry.getValue());
					continue;
				}
				tfb.addInVar(entry.getKey(), entry.getValue());
			}
			for (final Entry<IProgramVar, TermVariable> entry : oldTf.getOutVars().entrySet()) {
				if (!equivClass.contains(entry.getKey().toString())) {
					toRemove.add(entry.getValue());
					continue;
				}
				tfb.addOutVar(entry.getKey(), entry.getValue());
			}

			// TODO: Use values from Programexecution as patterns?
			final Term projected = PartialQuantifierElimination.quantifier(mServices, mLogger, mgdScript,
					SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
					QuantifiedFormula.EXISTS, toRemove, oldFormula);
			tfb.setFormula(projected);

			final UnmodifiableTransFormula newTf = tfb.finishConstruction(mgdScript);
			rtr.add(new BasicInternalAction(action.getPrecedingProcedure(), action.getSucceedingProcedure(), newTf));

		}

		return rtr;
	}

	private List<IAction> extractSequential(final IcfgProgramExecution<?> pe, final ManagedScript mgdScript) {
		final Map<TermVariable, Boolean>[] branchEncoders = pe.getBranchEncoders();
		final List<IAction> rtr = new ArrayList<>();
		for (int i = 0; i < pe.getLength(); i++) {
			final AtomicTraceElement<? extends IAction> ate = pe.getTraceElement(i);

			if ("true".equals(ate.getTraceElement().getTransformula().getClosedFormula().toString())) {
				// ignore all true steps
				continue;
			}

			final Map<TermVariable, Boolean> branchEncoder;
			if (branchEncoders == null || i >= branchEncoders.length) {
				branchEncoder = null;
			} else {
				branchEncoder = branchEncoders[i];
			}

			final List<IAction> sequentialActions =
					extractSequential(Collections.singletonList((CodeBlock) ate.getTraceElement()), branchEncoder);

			final List<UnmodifiableTransFormula> transFormulas =
					sequentialActions.stream().map(a -> a.getTransformula()).collect(Collectors.toList());
			final UnmodifiableTransFormula sc = TransFormulaUtils.sequentialComposition(mLogger, mServices, mgdScript,
					false, true, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
					SimplificationTechnique.NONE, transFormulas);
			rtr.add(new BasicInternalAction(null, null, sc));
		}
		return rtr;
	}

	private List<IAction> extractSequential(final List<CodeBlock> cbs, final Map<TermVariable, Boolean> branchEncoder) {
		final List<IAction> rtr = new ArrayList<>();
		for (final CodeBlock cb : cbs) {
			if (cb instanceof SequentialComposition) {
				rtr.addAll(extractSequential(((SequentialComposition) cb).getCodeBlocks(), branchEncoder));
			} else if (cb instanceof ParallelComposition) {
				if (branchEncoder == null) {
					throw new AssertionError("Not enough branch encoders");
				}
				final ParallelComposition parallelComposition = ((ParallelComposition) cb);
				final Map<TermVariable, CodeBlock> bi2cb = parallelComposition.getBranchIndicator2CodeBlock();

				final CodeBlock branch =
						bi2cb.entrySet().stream().filter(a -> branchEncoder.get(a.getKey())).map(a -> a.getValue())
								.findFirst().orElseThrow(() -> new AssertionError("No branch was taken!"));
				rtr.addAll(extractSequential(Collections.singletonList(branch), branchEncoder));
			} else {
				rtr.add(cb);
			}
		}
		return rtr;
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
}
