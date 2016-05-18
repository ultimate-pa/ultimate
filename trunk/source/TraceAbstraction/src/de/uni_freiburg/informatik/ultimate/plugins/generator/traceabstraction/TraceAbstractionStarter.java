/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ResultUtil;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RcfgElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class TraceAbstractionStarter {

	private final ILogger m_Logger;
	private final IUltimateServiceProvider m_Services;
	private final IToolchainStorage m_ToolchainStorage;

	public TraceAbstractionStarter(IUltimateServiceProvider services, IToolchainStorage storage, RootNode rcfgRootNode,
			NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		m_Services = services;
		m_ToolchainStorage = storage;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		runCegarLoops(rcfgRootNode, witnessAutomaton);
	}

	/**
	 * Root Node of this Ultimate model. I use this to store information that should be passed to the next plugin. The
	 * Successors of this node exactly the initial nodes of procedures.
	 */
	private IElement m_RootOfNewModel = null;
	private Result m_OverallResult;
	private IElement m_Artifact;

	private void runCegarLoops(RootNode rcfgRootNode, NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		RootAnnot rootAnnot = rcfgRootNode.getRootAnnot();
		TAPreferences taPrefs = new TAPreferences();

		String settings = "Automizer settings:";
		settings += " Hoare:" + taPrefs.computeHoareAnnotation();
		settings += " " + (taPrefs.differenceSenwa() ? "SeNWA" : "NWA");
		settings += " Interpolation:" + taPrefs.interpolation();
		settings += " Determinization: " + taPrefs.interpolantAutomatonEnhancement();
		System.out.println(settings);

		SmtManager smtManager = new SmtManager(rootAnnot.getScript(), rootAnnot.getBoogie2SMT(),
				rootAnnot.getModGlobVarManager(), m_Services, interpolationModeSwitchNeeded(),
				rootAnnot.getManagedScript());
		TraceAbstractionBenchmarks traceAbstractionBenchmark = new TraceAbstractionBenchmarks(rootAnnot);

		Map<String, Collection<ProgramPoint>> proc2errNodes = rootAnnot.getErrorNodes();
		Collection<ProgramPoint> errNodesOfAllProc = new ArrayList<ProgramPoint>();
		for (Collection<ProgramPoint> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		m_OverallResult = Result.SAFE;
		m_Artifact = null;

		if (taPrefs.allErrorLocsAtOnce()) {
			String name = "AllErrorsAtOnce";
			iterate(name, rcfgRootNode, taPrefs, smtManager, traceAbstractionBenchmark, errNodesOfAllProc,
					witnessAutomaton);
		} else {
			for (ProgramPoint errorLoc : errNodesOfAllProc) {
				String name = errorLoc.getPosition();
				ArrayList<ProgramPoint> errorLocs = new ArrayList<ProgramPoint>(1);
				errorLocs.add(errorLoc);
				m_Services.getProgressMonitorService().setSubtask(errorLoc.toString());
				iterate(name, rcfgRootNode, taPrefs, smtManager, traceAbstractionBenchmark, errorLocs,
						witnessAutomaton);
			}
		}
		logNumberOfWitnessInvariants(errNodesOfAllProc);
		if (m_OverallResult == Result.SAFE) {
			final String longDescription;
			if (errNodesOfAllProc.isEmpty()) {
				longDescription = "We were not able to verify any"
						+ " specifiation because the program does not contain any specification.";
			} else {
				longDescription = errNodesOfAllProc.size() + " specifications checked. All of them hold";
			}
			AllSpecificationsHoldResult result = new AllSpecificationsHoldResult(Activator.s_PLUGIN_NAME,
					longDescription);
			reportResult(result);
		}

		m_Logger.debug("Compute Hoare Annotation: " + taPrefs.computeHoareAnnotation());
		m_Logger.debug("Overall result: " + m_OverallResult);
		m_Logger.debug("Continue processing: " + m_Services.getProgressMonitorService().continueProcessing());
		if (taPrefs.computeHoareAnnotation() && m_OverallResult != Result.TIMEOUT
				&& m_Services.getProgressMonitorService().continueProcessing()) {
			assert (smtManager.cfgInductive(rcfgRootNode));

			final IBacktranslationService backTranslatorService = m_Services.getBacktranslationService();
			final Term trueterm = smtManager.getScript().term("true");

			final Set<ProgramPoint> locsForLoopLocations = new HashSet<>();
			locsForLoopLocations.addAll(rootAnnot.getPotentialCycleProgramPoints());
			locsForLoopLocations.addAll(rootAnnot.getLoopLocations().keySet());
			// find all locations that have outgoing edges which are annotated with LoopEntry, i.e., all loop candidates

			for (ProgramPoint locNode : locsForLoopLocations) {
				final HoareAnnotation hoare = getHoareAnnotation(locNode);
				if (hoare != null) {
					final Term formula = hoare.getFormula();
					final Expression expr = rootAnnot.getBoogie2SMT().getTerm2Expression().translate(formula);
					final InvariantResult<RcfgElement, Expression> invResult = new InvariantResult<RcfgElement, Expression>(
							Activator.s_PLUGIN_NAME, locNode, backTranslatorService, expr);
					reportResult(invResult);

					if (!formula.equals(trueterm)) {
						final String inv = backTranslatorService.translateExpressionToString(expr, Expression.class);
						new WitnessInvariant(inv).annotate(locNode);
					}
				}
			}

			final Map<String, ProgramPoint> finalNodes = rootAnnot.getExitNodes();
			for (final String proc : finalNodes.keySet()) {
				if (isAuxilliaryProcedure(proc)) {
					continue;
				}
				final ProgramPoint finalNode = finalNodes.get(proc);
				final HoareAnnotation hoare = getHoareAnnotation(finalNode);
				if (hoare != null) {
					final Term formula = hoare.getFormula();
					final Expression expr = rootAnnot.getBoogie2SMT().getTerm2Expression().translate(formula);
					final ProcedureContractResult<RcfgElement, Expression> result = new ProcedureContractResult<RcfgElement, Expression>(
							Activator.s_PLUGIN_NAME, finalNode, backTranslatorService, proc, expr);

					reportResult(result);
					// TODO: Add setting that controls the generation of those witness invariants; for now, just
					// commented out
					// if (!formula.equals(trueterm)) {
					// final String inv = backTranslatorService.translateExpressionToString(expr, Expression.class);
					// new WitnessInvariant(inv).annotate(finalNode);
					// }
				}
			}
		}
		reportBenchmark(traceAbstractionBenchmark);
		switch (m_OverallResult) {
		case SAFE:
			// s_Logger.warn("Program is correct");
			// ResultNotifier.programCorrect();
			break;
		case UNSAFE:
			// s_Logger.warn("Program is incorrect");
			// ResultNotifier.programIncorrect();
			break;
		case TIMEOUT:
			m_Logger.warn("Timeout");
			// ResultNotifier
			// .programUnknown("Timeout");
			break;
		case UNKNOWN:
			m_Logger.warn("Unable to decide correctness. Please check the following counterexample manually.");
			// ResultNotifier.programUnknown("Program might be incorrect, check"
			// + " conterexample.");
			break;
		}

		m_RootOfNewModel = m_Artifact;
	}

	private void logNumberOfWitnessInvariants(Collection<ProgramPoint> errNodesOfAllProc) {
		int numberOfCheckedInvariants = 0;
		for (ProgramPoint err : errNodesOfAllProc) {
			BoogieASTNode boogieASTNode = err.getBoogieASTNode();
			IAnnotations annot = boogieASTNode.getPayload().getAnnotations().get(Check.class.getName());
			if (annot != null) {
				Check check = (Check) annot;
				if (check.getSpec() == Spec.WITNESS_INVARIANT) {
					numberOfCheckedInvariants++;
				}
			}
		}
		if (numberOfCheckedInvariants > 0) {
			m_Logger.info("Automizer considered " + numberOfCheckedInvariants + " witness invariants");
			m_Logger.info("WitnessConsidered=" + numberOfCheckedInvariants);
		}
	}

	private void iterate(String name, RootNode root, TAPreferences taPrefs, SmtManager smtManager,
			TraceAbstractionBenchmarks taBenchmark, Collection<ProgramPoint> errorLocs,
			NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		BasicCegarLoop basicCegarLoop;
		LanguageOperation languageOperation = (new UltimatePreferenceStore(Activator.s_PLUGIN_ID))
				.getEnum(TraceAbstractionPreferenceInitializer.LABEL_LANGUAGE_OPERATION, LanguageOperation.class);
		if (languageOperation == LanguageOperation.DIFFERENCE) {
			if (taPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
				basicCegarLoop = new CegarLoopSWBnonRecursive(name, root, smtManager, taBenchmark, taPrefs, errorLocs,
						taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), m_Services, m_ToolchainStorage);
				// abstractCegarLoop = new CegarLoopSequentialWithBackedges(name,
				// root, smtManager, timingStatistics,taPrefs, errorLocs);
			} else {
				basicCegarLoop = new BasicCegarLoop(name, root, smtManager, taPrefs, errorLocs, taPrefs.interpolation(),
						taPrefs.computeHoareAnnotation(), m_Services, m_ToolchainStorage);
			}
		} else {
			basicCegarLoop = new IncrementalInclusionCegarLoop(name, root, smtManager, taPrefs, errorLocs,
					taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), m_Services, m_ToolchainStorage,
					languageOperation);
		}
		basicCegarLoop.setWitnessAutomaton(witnessAutomaton);

		Result result = basicCegarLoop.iterate();
		basicCegarLoop.finish();
		CegarLoopStatisticsGenerator cegarLoopBenchmarkGenerator = basicCegarLoop.getCegarLoopBenchmark();
		cegarLoopBenchmarkGenerator.stop(CegarLoopStatisticsDefinitions.OverallTime.toString());
		taBenchmark.aggregateBenchmarkData(cegarLoopBenchmarkGenerator);

		switch (result) {
		case SAFE:
			reportPositiveResults(errorLocs);
			break;
		case UNSAFE: {
			RcfgProgramExecution pe = basicCegarLoop.getRcfgProgramExecution();
			reportCounterexampleResult(pe);
			m_OverallResult = result;
			break;
		}
		case TIMEOUT:
			reportTimeoutResult(errorLocs, basicCegarLoop.getToolchainCancelledException());
			if (m_OverallResult != Result.UNSAFE) {
				m_OverallResult = result;
			}
			break;
		case UNKNOWN: {
			RcfgProgramExecution pe = basicCegarLoop.getRcfgProgramExecution();
			reportUnproveableResult(pe, pe.getUnprovabilityReasons());
			if (m_OverallResult != Result.UNSAFE) {
				m_OverallResult = result;
			}
			break;
		}
		}
		if (taPrefs.computeHoareAnnotation() && m_OverallResult == Result.SAFE) {
			m_Logger.debug("Computing Hoare annotation of CFG");
			basicCegarLoop.computeCFGHoareAnnotation();
			writeHoareAnnotationToLogger(root);
		} else {
			m_Logger.debug("Ommiting computation of Hoare annotation");

		}
		m_Artifact = basicCegarLoop.getArtifact();
	}

	private void writeHoareAnnotationToLogger(RootNode root) {
		for (Entry<String, Map<String, ProgramPoint>> proc2label2pp : root.getRootAnnot().getProgramPoints()
				.entrySet()) {
			for (ProgramPoint pp : proc2label2pp.getValue().values()) {
				HoareAnnotation hoare = getHoareAnnotation(pp);
				if (hoare == null) {
					m_Logger.info("For program point  " + prettyPrintProgramPoint(pp)
							+ "  no Hoare annotation was computed.");
				} else {
					m_Logger.info("At program point  " + prettyPrintProgramPoint(pp) + "  the Hoare annotation is:  "
							+ hoare.getFormula());
				}
			}
		}
	}

	private static String prettyPrintProgramPoint(ProgramPoint pp) {
		int startLine = pp.getPayload().getLocation().getStartLine();
		int endLine = pp.getPayload().getLocation().getStartLine();
		StringBuilder sb = new StringBuilder();
		sb.append(pp);
		if (startLine == endLine) {
			sb.append("(line " + startLine + ")");
		} else {
			sb.append("(lines " + startLine + " " + endLine + ")");
		}
		return sb.toString();
	}

	private void reportPositiveResults(Collection<ProgramPoint> errorLocs) {
		for (ProgramPoint errorLoc : errorLocs) {
			PositiveResult<RcfgElement> pResult = new PositiveResult<RcfgElement>(Activator.s_PLUGIN_NAME, errorLoc,
					m_Services.getBacktranslationService());
			reportResult(pResult);
		}
	}

	private void reportCounterexampleResult(RcfgProgramExecution pe) {
		if (!pe.getOverapproximations().isEmpty()) {
			reportUnproveableResult(pe, pe.getUnprovabilityReasons());
			return;
		}
		reportResult(new CounterExampleResult<RcfgElement, RCFGEdge, Expression>(getErrorPP(pe),
				Activator.s_PLUGIN_NAME, m_Services.getBacktranslationService(), pe));
	}

	private void reportTimeoutResult(Collection<ProgramPoint> errorLocs,
			ToolchainCanceledException toolchainCanceledException) {
		for (ProgramPoint errorIpp : errorLocs) {
			ProgramPoint errorLoc = errorIpp;
			final ILocation origin = errorLoc.getBoogieASTNode().getLocation().getOrigin();
			String timeOutMessage = "Unable to prove that ";
			timeOutMessage += ResultUtil.getCheckedSpecification(errorLoc).getPositiveMessage();
			timeOutMessage += " (line " + origin.getStartLine() + ").";
			if (toolchainCanceledException != null) {
				timeOutMessage += " " + toolchainCanceledException.prettyPrint();
			}
			TimeoutResultAtElement<RcfgElement> timeOutRes = new TimeoutResultAtElement<RcfgElement>(errorLoc,
					Activator.s_PLUGIN_NAME, m_Services.getBacktranslationService(), timeOutMessage);
			reportResult(timeOutRes);
			// s_Logger.warn(timeOutMessage);
		}
	}

	private void reportUnproveableResult(RcfgProgramExecution pe, List<UnprovabilityReason> unproabilityReasons) {
		ProgramPoint errorPP = getErrorPP(pe);
		UnprovableResult<RcfgElement, RCFGEdge, Expression> uknRes = new UnprovableResult<RcfgElement, RCFGEdge, Expression>(
				Activator.s_PLUGIN_NAME, errorPP, m_Services.getBacktranslationService(), pe, unproabilityReasons);
		reportResult(uknRes);
	}

	private <T> void reportBenchmark(ICsvProviderProvider<T> benchmark) {
		String shortDescription = "Ultimate Automizer benchmark data";
		BenchmarkResult<T> res = new BenchmarkResult<T>(Activator.s_PLUGIN_NAME, shortDescription, benchmark);
		// s_Logger.warn(res.getLongDescription());

		reportResult(res);
	}

	private static boolean isAuxilliaryProcedure(String proc) {
		return proc.equals("ULTIMATE.init") || proc.equals("ULTIMATE.start");
	}

	private void reportResult(IResult res) {
		m_Services.getResultService().reportResult(Activator.s_PLUGIN_ID, res);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRootOfNewModel() {
		return m_RootOfNewModel;
	}

	public static HoareAnnotation getHoareAnnotation(ProgramPoint programPoint) {
		return HoareAnnotation.getAnnotation(programPoint);
	}

	public ProgramPoint getErrorPP(RcfgProgramExecution rcfgProgramExecution) {
		int lastPosition = rcfgProgramExecution.getLength() - 1;
		RCFGEdge last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		ProgramPoint errorPP = (ProgramPoint) last.getTarget();
		return errorPP;
	}

	private boolean interpolationModeSwitchNeeded() {
		SolverMode solver = (new UltimatePreferenceStore(RCFGBuilder.s_PLUGIN_ID))
				.getEnum(RcfgPreferenceInitializer.LABEL_Solver, SolverMode.class);
		if (solver == SolverMode.External_PrincessInterpolationMode) {
			return true;
		} else {
			return false;
		}
	}

}
