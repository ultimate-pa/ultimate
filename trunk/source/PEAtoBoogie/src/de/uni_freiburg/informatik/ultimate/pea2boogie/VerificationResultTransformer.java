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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
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
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
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
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Utility class that helps with reporting results.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class VerificationResultTransformer {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IReqSymbolTable mReqSymbolTable;

	public VerificationResultTransformer(final ILogger logger, final IUltimateServiceProvider services,
			final IReqSymbolTable reqSymbolTable) {
		mLogger = logger;
		mServices = services;
		mReqSymbolTable = reqSymbolTable;
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
				if (newPe == null) {
					return new ReqCheckRtInconsistentResult<>(element, plugin, translatorSequence);
				}

				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Result before Pea2Boogie result transformation");
					mLogger.debug(oldRes);
					mLogger.debug("PE after Pea2Boogie result transformation");
					mLogger.debug(newPe);
				}
				final List<Entry<Rational, Map<Term, Term>>> delta2var2value =
						generateTimeSequenceMap(newPe.getProgramStates());
				final String failurePath = formatTimeSequenceMap(delta2var2value);
				return new ReqCheckRtInconsistentResult<>(element, plugin, translatorSequence, failurePath);
			}
			return new ReqCheckFailResult<>(element, plugin, translatorSequence);

		} else {
			throw new UnsupportedOperationException("Multi-checks of " + specs + " are not yet supported");
		}
	}

	private String formatTimeSequenceMap(final List<Entry<Rational, Map<Term, Term>>> delta2var2value) {

		final int deltaMaxLength =
				delta2var2value.stream().map(a -> a.getKey().toString().length()).max(Integer::compare).get();
		// there might be two numbers of maxlength, we have 3 additional chars "(;]", we want 2 spaces
		// if maxLength is smaller than INITIAL (7) + 5 , use 12 instead
		final int maxLength = deltaMaxLength * 2 + 5 < 12 ? 12 : deltaMaxLength * 2 + 5;

		final StringBuilder sb = new StringBuilder();
		Rational last = Rational.ZERO;
		Rational current = Rational.ZERO;
		String lastValues = "";
		for (final Entry<Rational, Map<Term, Term>> entry : delta2var2value) {
			final String values =
					entry.getValue().entrySet().stream().map(this::formatVarValue).collect(Collectors.joining(" "));
			if (lastValues.equals(values)) {
				// subsume these values in the current step
				continue;
			}
			current = current.add(entry.getKey());

			final String currentStr;
			if (current == Rational.ZERO) {
				currentStr = "INITIAL";
			} else {
				currentStr = String.format("[%s;%s]", SmtUtils.toString(last), SmtUtils.toString(current));
			}
			sb.append(currentStr);
			appendRepeatedly(sb, " ", maxLength - currentStr.length());

			sb.append(values);
			sb.append(CoreUtil.getPlatformLineSeparator());

			lastValues = values;
			last = current;
		}

		return sb.toString();
	}

	private String formatVarValue(final Entry<Term, Term> entry) {
		return String.format("%s=%s", entry.getKey(), entry.getValue() == null ? "*" : entry.getValue());
	}

	/**
	 * @return A map from delta value to variable values that are interesting at this point of time
	 */
	private List<Entry<Rational, Map<Term, Term>>>
			generateTimeSequenceMap(final List<ProgramState<Term>> programStates) {
		final List<ProgramState<Term>> stateSequence =
				programStates.stream().filter(Objects::nonNull).collect(Collectors.toList());

		final Map<String, Term> vars =
				new LinkedHashMap<>(stateSequence.stream().flatMap(a -> a.getVariables().stream()).distinct()
						.collect(Collectors.toMap(a -> a.toString(), a -> a)));

		final Term deltaVar = vars.get(mReqSymbolTable.getDeltaVarName());
		vars.remove(mReqSymbolTable.getDeltaVarName());
		mReqSymbolTable.getClockVars().stream().forEach(vars::remove);
		mReqSymbolTable.getPcVars().stream().forEach(vars::remove);

		final List<Entry<Rational, Map<Term, Term>>> delta2term2values = new ArrayList<>();

		Map<Term, Term> last = Collections.emptyMap();
		int i = 0;
		for (final ProgramState<Term> state : stateSequence) {

			final Rational deltaValue;
			if (state.getVariables().contains(deltaVar)) {
				final Term deltaValueTerm = firstOrWarn(state.getValues(deltaVar), () -> {
					throw new AssertionError("Program state broken: Var in vars but no value");
				});
				deltaValue = (Rational) ((ConstantTerm) deltaValueTerm).getValue();
			} else {
				deltaValue = Rational.ZERO;
			}

			final Map<Term, Term> current = new LinkedHashMap<>();
			delta2term2values.add(new Pair<>(deltaValue, current));

			for (final Entry<String, Term> entry : vars.entrySet()) {
				// keep last signal if we dont have a current value
				final Map<Term, Term> lastF = Collections.unmodifiableMap(last);
				final Term value = firstOrWarn(state.getValues(entry.getValue()), () -> lastF.get(entry.getValue()));
				current.put(entry.getValue(), value);
			}

			last = current;

			i++;
			if (i >= stateSequence.size()) {
				// skip last state
				break;
			}
		}

		return delta2term2values;
	}

	private <T> T firstOrWarn(final Collection<T> t, final Supplier<T> funDefault) {
		if (t == null || t.isEmpty()) {
			return funDefault.get();
		}
		if (t.size() > 1) {
			mLogger.warn("More than one value");
		}
		return t.iterator().next();
	}

	/**
	 * Append str reapeat times to sb.
	 *
	 * If sb is null, creates a new {@link StringBuilder} and uses this.
	 *
	 * @return sb
	 */
	private static StringBuilder appendRepeatedly(final StringBuilder sb, final String str, final int repeat) {
		if (sb == null) {
			return appendRepeatedly(new StringBuilder(repeat * str.length()), str, repeat);
		}
		if (repeat <= 0) {
			return sb;
		}
		for (int i = 0; i < repeat; i++) {
			sb.append(str);
		}
		return sb;
	}

	private IProgramExecution<IAction, Term> generateRtInconsistencyResult(final IcfgProgramExecution<?> pe,
			final ReqCheck reqCheck) {
		mLogger.info("Analyzing reasons for rt-inconsistency");
		final List<CodeBlock> trace = new ArrayList<>(pe.getLength());
		pe.stream().map(a -> (CodeBlock) a.getTraceElement()).forEach(trace::add);

		final CodeBlockFactory cbf = CodeBlockFactory.getFactory((IToolchainStorage) mServices);
		final CfgSmtToolkit toolkit = cbf.getToolkit();

		final String solverName = "RtInconsistencyPostProcessor";
		final SolverSettings solverSettings = SolverBuilder.constructSolverSettings()
				.setUseExternalSolver(true, SolverBuilder.COMMAND_Z3_NO_TIMEOUT, SolverBuilder.LOGIC_Z3)
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode);

		final ManagedScript mgdScriptTc = toolkit.createFreshManagedScript(solverSettings, solverName);
		final Script scriptTc = mgdScriptTc.getScript();
		final BasicPredicateFactory bpf = new BasicPredicateFactory(mServices, mgdScriptTc, toolkit.getSymbolTable());
		final BasicPredicate truePred = bpf.newPredicate(scriptTc.term("true"));
		final BasicPredicate falsePred = bpf.newPredicate(scriptTc.term("false"));
		final ManagedScript mgdScriptAux = toolkit.getManagedScript();

		try {
			// first, recheck to ensure that we have branch encoders
			final TraceCheck<IAction> tcl =
					TraceCheck.createTraceCheck(truePred, falsePred, trace, toolkit, mgdScriptTc);
			if (!tcl.providesRcfgProgramExecution()) {
				mLogger.warn("Could not extract reduced program execution from trace: TraceCheck reported "
						+ tcl.isCorrect());
				return null;
			}

			final List<IAction> sequentialTrace =
					sequentialize(tcl.getRcfgProgramExecution(), mgdScriptTc, mgdScriptAux);
			final List<IAction> cleanedTrace = removeUnrelatedVariables(sequentialTrace, reqCheck, mgdScriptTc);
			final TraceCheck<IAction> tc =
					TraceCheck.createTraceCheck(truePred, falsePred, cleanedTrace, toolkit, mgdScriptTc);
			if (tc.isCorrect() == LBool.SAT) {
				return tc.getRcfgProgramExecution();
			}
			throw new AssertionError("Expected branch is not SAT");
		} catch (final ToolchainCanceledException e) {
			mLogger.warn("Timeout during analysis of rt-inconsistency reasons");
			return null;
		} finally {
			mgdScriptTc.getScript().exit();
		}
	}

	private List<IAction> removeUnrelatedVariables(final List<IAction> sequentialTrace, final ReqCheck reqCheck,
			final ManagedScript mgdScript) {
		final String firstPeaName = ReqSymboltableBuilder.getPcName(reqCheck.getPeaNames().iterator().next());
		final Set<String> equivClass =
				new HashSet<>(mReqSymbolTable.getVariableEquivalenceClasses().getContainingSet(firstPeaName));
		equivClass.add(mReqSymbolTable.getDeltaVarName());

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

	/**
	 * Apply the branch encoders to all parallel compositions of the original program execution and transfer all
	 * resulting transformulas from the initial script (aux) to the script we are using (tc) before projection.
	 *
	 * The sequentialisation is necessary to identify the reason for rt inconsistency. The transfer happens here because
	 * we want to use TransFormulaUtils.sequentialComposition, which might timeout during quantifier elimination, which
	 * in turn might pollute the solver, so we are using a separate solver for this.
	 */
	private List<IAction> sequentialize(final IcfgProgramExecution<?> pe, final ManagedScript mgdScriptTc,
			final ManagedScript mgdScriptAux) {
		final Map<TermVariable, Boolean>[] branchEncoders = pe.getBranchEncoders();
		final List<IAction> rtr = new ArrayList<>();
		final TermTransferrer tt = new TermTransferrer(mgdScriptAux.getScript(), mgdScriptTc.getScript());
		final Map<IProgramVarOrConst, IProgramVarOrConst> programVarCache = new HashMap<>();
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

			// IActions of the old script
			final List<IAction> sequentialActions =
					extractSequential(Collections.singletonList((CodeBlock) ate.getTraceElement()), branchEncoder);

			// Transfer transformulas to new script
			final List<UnmodifiableTransFormula> transFormulas = sequentialActions.stream()
					.map(a -> TransFormulaBuilder
							.transferTransformula(tt, mgdScriptTc, programVarCache, a.getTransformula())
							.getTransformula())
					.collect(Collectors.toList());

			final UnmodifiableTransFormula sc = TransFormulaUtils.sequentialComposition(mLogger, mServices, mgdScriptTc,
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
