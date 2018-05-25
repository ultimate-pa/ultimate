/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryResultChecking;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.RelevanceInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorTraceContainer.ErrorTrace;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization.ErrorLocalizationStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization.FlowSensitiveFaultLocalizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 * Constructs an error automaton for a given error trace.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type in the trace
 */
public class ErrorGeneralizationEngine<LETTER extends IIcfgTransition<?>> implements IErrorAutomatonBuilder<LETTER> {
	private static final ErrorAutomatonType TYPE = ErrorAutomatonType.DANGER_AUTOMATON;

	protected final IUltimateServiceProvider mServices;
	protected final ILogger mLogger;

	private final ErrorTraceContainer<LETTER> mErrorTraces;
	private final List<Collection<LETTER>> mRelevantStatements;
	private final List<ErrorLocalizationStatisticsGenerator> mFaultLocalizerStatistics;
	private final ErrorAutomatonStatisticsGenerator mErrorAutomatonStatisticsGenerator;
	private IErrorAutomatonBuilder<LETTER> mErrorAutomatonBuilder;
	private int mLastIteration = -1;

	/**
	 * @param services
	 *            Ultimate services.
	 */
	public ErrorGeneralizationEngine(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mErrorAutomatonStatisticsGenerator = new ErrorAutomatonStatisticsGenerator(services);
		mErrorTraces = new ErrorTraceContainer<>();
		mRelevantStatements = new ArrayList<>();
		mFaultLocalizerStatistics = new ArrayList<>();
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResultBeforeEnhancement() {
		return mErrorAutomatonBuilder.getResultBeforeEnhancement();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getResultAfterEnhancement() {
		return mErrorAutomatonBuilder.getResultAfterEnhancement();
	}

	@Override
	public ErrorAutomatonType getType() {
		throw new UnsupportedOperationException();
	}

	@Override
	public IPredicate getErrorPrecondition() {
		return mErrorAutomatonBuilder.getErrorPrecondition();
	}

	@Override
	public InterpolantAutomatonEnhancement getEnhancementMode() {
		return mErrorAutomatonBuilder.getEnhancementMode();
	}

	/**
	 * @param iteration
	 *            Iteration of CEGAR loop.
	 * @return {@code true} iff iteration of last error automaton construction coincides with passed iteration
	 */
	public boolean hasAutomatonInIteration(final int iteration) {
		return mLastIteration == iteration;
	}

	/**
	 * @param counterexample
	 *            Counterexample.
	 * @param predicateFactory
	 *            predicate factory
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param csToolkit
	 *            SMT toolkit
	 * @param simplificationTechnique
	 *            simplification technique
	 * @param xnfConversionTechnique
	 *            XNF conversion technique
	 * @param symbolTable
	 *            symbol table
	 * @param stateFactoryForAutomaton
	 *            state factory for automaton (will be refactored eventually)
	 * @param abstraction
	 *            abstraction
	 * @param iteration
	 *            current CEGAR loop iteration
	 */
	public void constructErrorAutomaton(final IRun<LETTER, IPredicate, ?> counterexample,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier,
			final CfgSmtToolkit csToolkit, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata stateFactoryForAutomaton,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, final int iteration) {
		mErrorTraces.addTrace(counterexample);
		mLastIteration = iteration;

		final NestedWord<LETTER> trace = (NestedWord<LETTER>) counterexample.getWord();
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Constructing " + (TYPE == ErrorAutomatonType.ERROR_AUTOMATON ? "error" : "danger")
					+ " automaton for trace of length " + trace.length());
		}

		mErrorAutomatonStatisticsGenerator.reportTrace(trace);
		mErrorAutomatonStatisticsGenerator.startErrorAutomatonConstructionTime();

		try {
			switch (TYPE) {
				case ERROR_AUTOMATON:
					mErrorAutomatonBuilder = new ErrorAutomatonBuilder<>(mServices, predicateFactory, predicateUnifier,
							csToolkit, simplificationTechnique, xnfConversionTechnique, symbolTable,
							stateFactoryForAutomaton, abstraction, trace);
					break;
				case DANGER_AUTOMATON:
					mErrorAutomatonBuilder = new DangerAutomatonBuilder<>(mServices, predicateFactory, predicateUnifier,
							csToolkit, simplificationTechnique, xnfConversionTechnique, symbolTable,
							stateFactoryForAutomaton, abstraction, trace);
					break;
				default:
					throw new IllegalArgumentException("Unknown automaton type: " + TYPE);
			}
		} catch (final ToolchainCanceledException tce) {
			mErrorAutomatonStatisticsGenerator.stopErrorAutomatonConstructionTime();
			mErrorAutomatonStatisticsGenerator.finishAutomatonInstance(true);
			final RunningTaskInfo rti = new RunningTaskInfo(getClass(),
					"constructing error automaton for trace of length " + trace.length() + " (spent "
							+ mErrorAutomatonStatisticsGenerator.getLastConstructionTime() + " nanoseconds)");
			throw new ToolchainCanceledException(tce, rti);
		}
		mErrorAutomatonStatisticsGenerator.stopErrorAutomatonConstructionTime();
		mErrorTraces.addPrecondition(mErrorAutomatonBuilder.getErrorPrecondition());
	}

	/**
	 * Starts difference time measurement.
	 */
	public void startDifference() {
		mErrorAutomatonStatisticsGenerator.startErrorAutomatonDifferenceTime();
	}

	/**
	 * Stops difference time measurement. Also evaluates the automaton.
	 *
	 * @param abstraction
	 *            abstraction
	 * @param predicateFactoryInterpolantAutomata
	 *            state factory for automaton
	 * @param predicateFactoryResultChecking
	 *            state factory for result checking
	 * @throws AutomataLibraryException
	 *             thrown by automaton evaluation
	 */
	public void stopDifference(final INestedWordAutomaton<LETTER, IPredicate> abstraction,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryResultChecking predicateFactoryResultChecking,
			final IRun<LETTER, IPredicate, ?> errorTrace, final boolean prematureTermination)
			throws AutomataLibraryException {
		mErrorAutomatonStatisticsGenerator.stopErrorAutomatonDifferenceTime();
		if (!prematureTermination) {
			mErrorAutomatonStatisticsGenerator.evaluateFinalErrorAutomaton(mServices, mLogger, mErrorAutomatonBuilder,
					(INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate>) abstraction,
					predicateFactoryInterpolantAutomata, predicateFactoryResultChecking, errorTrace);
			mErrorTraces.addEnhancementType(mErrorAutomatonStatisticsGenerator.getEnhancement());
		}
		mErrorAutomatonStatisticsGenerator.finishAutomatonInstance(prematureTermination);
	}

	/**
	 * Reports final error statistics.
	 */
	public void reportErrorGeneralizationBenchmarks() {
		final StatisticsData stat = new StatisticsData();
		mErrorAutomatonStatisticsGenerator.reportRelevantStatements(mRelevantStatements);
		mErrorAutomatonStatisticsGenerator.reportFaultLocalizationStatistics(mFaultLocalizerStatistics);
		stat.aggregateBenchmarkData(mErrorAutomatonStatisticsGenerator);
		final IResult benchmarkResult = new StatisticsResult<>(Activator.PLUGIN_NAME, "ErrorAutomatonStatistics", stat);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, benchmarkResult);
	}

	/**
	 * In case error traces are not reported immediately, the analysis may terminate with an empty abstraction or may
	 * run into termination issues, but it has already found out that the program contains errors. This method can be
	 * used to ask for such results whenever the analysis terminates.
	 *
	 * @param abstractResult
	 *            result that would be reported by {@link AbstractCegarLoop}
	 * @return {@code true} if at least one feasible counterexample was detected
	 */
	public boolean isResultUnsafe(final Result abstractResult, final INestedWordAutomaton<LETTER, IPredicate> cfg,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable) {
		if (mErrorTraces.isEmpty()) {
			return false;
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Found " + mErrorTraces.size()
					+ (mErrorTraces.size() == 1 ? " error trace:" : " different error traces in total:"));
			int ctr = 0;
			for (final ErrorTrace<LETTER> errorTraceWrapper : mErrorTraces) {
				final StringBuilder builder = new StringBuilder();
				builder.append(++ctr).append(": Error trace of length ")
						.append(errorTraceWrapper.getTrace().getWord().length());
				switch (errorTraceWrapper.getEnhancement()) {
					case NONE:
						builder.append(" (no additional traces)");
						break;
					case FINITE:
						builder.append(" (finite language)");
						break;
					case INFINITE:
						builder.append(" (infinite language)");
						break;
					case UNKNOWN:
						builder.append(" (unknown trace enhancement)");
						break;
					default:
						throw new IllegalArgumentException(
								"Unknown enhancement type: " + errorTraceWrapper.getEnhancement());
				}
				final IPredicate precondition = errorTraceWrapper.getPrecondition();
				// TODO 2017-06-14 Christian: Do not print error precondition on info level after testing phase.
				if (precondition == null) {
					builder.append(" (precondition not computed).");
				} else {
					builder.append(" has precondition ").append(precondition.getFormula()).append('.');
				}
				mLogger.warn(builder.toString());
			}
		}

		// apply fault localization to all error traces
		// TODO currently this is done in BasicCegarLoop after each error automaton construction due to timeout problems
		aggregateFaultLocalization(cfg, csToolkit, predicateFactory, predicateUnifier, simplificationTechnique,
				xnfConversionTechnique, symbolTable);

		// TODO 2017-06-18 Christian: Currently we want to run the CEGAR loop until the abstraction is empty.
//		return abstractResult == Result.SAFE;
		return true;
	}

	@SuppressWarnings("unchecked")
	private void aggregateFaultLocalization(final INestedWordAutomaton<LETTER, IPredicate> cfg,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable) {
		final Map<IcfgLocation, Set<LETTER>> finalLoc2responsibleStmts = new HashMap<>();
		final List<ErrorLocalizationStatisticsGenerator> faultLocalizerStatistics = new ArrayList<>();
		final Iterator<Collection<LETTER>> relevantStatementsIt = mRelevantStatements.iterator();
		for (final ErrorTrace<LETTER> errorTraceWrapper : mErrorTraces) {
			final NestedRun<LETTER, IPredicate> trace = (NestedRun<LETTER, IPredicate>) errorTraceWrapper.getTrace();
			if (! relevantStatementsIt.hasNext()) {
				break;
			}

			final Collection<LETTER> newResponsibleStmts =
					// TODO changed this, computed in BasicCegarLoop
//					faultLocalization(cfg, csToolkit, predicateFactory, predicateUnifier, simplificationTechnique,
//							xnfConversionTechnique, symbolTable, faultLocalizerStatistics, trace);
					relevantStatementsIt.next();

			aggregate(newResponsibleStmts, finalLoc2responsibleStmts, trace.getStateSequence());
		}

		presentResult(finalLoc2responsibleStmts, cfg, faultLocalizerStatistics);
	}

	public void faultLocalizationWithStorage(final INestedWordAutomaton<LETTER, IPredicate> cfg,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable,
			final List<ErrorLocalizationStatisticsGenerator> faultLocalizerStatistics,
			final NestedRun<LETTER, IPredicate> trace, IIcfg<IcfgLocation> Icfg) {
		final List<ErrorLocalizationStatisticsGenerator> realFaultLocalizerStatistics =
				(faultLocalizerStatistics == null) ? mFaultLocalizerStatistics : faultLocalizerStatistics;
		mRelevantStatements.add(faultLocalization(cfg, csToolkit, predicateFactory, predicateUnifier,
				simplificationTechnique, xnfConversionTechnique, symbolTable, realFaultLocalizerStatistics, trace, Icfg));
	}

	/**
	 * Fault localization of single trace.
	 * @param icfg 
	 */
	private Collection<LETTER> faultLocalization(final INestedWordAutomaton<LETTER, IPredicate> cfg,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable,
			final List<ErrorLocalizationStatisticsGenerator> faultLocalizerStatistics,
			final NestedRun<LETTER, IPredicate> trace, IIcfg<IcfgLocation> icfg) {
		final FlowSensitiveFaultLocalizer<LETTER> faultLocalizer = new FlowSensitiveFaultLocalizer<>(trace, cfg,
				mServices, csToolkit, predicateFactory, csToolkit.getModifiableGlobalsTable(), predicateUnifier,
				RelevanceAnalysisMode.SINGLE_TRACE, simplificationTechnique, xnfConversionTechnique, symbolTable, icfg);
		final List<IRelevanceInformation> relevanceInformation = faultLocalizer.getRelevanceInformation();
		if (faultLocalizerStatistics != null) {
			faultLocalizerStatistics.add(faultLocalizer.getStatistics());
		}
		return findResponsibleStatements(relevanceInformation, trace.getWord());
	}

	private Collection<LETTER> findResponsibleStatements(final List<IRelevanceInformation> relevanceInformation,
			final NestedWord<LETTER> word) {
		assert word.length() == relevanceInformation.size();
		final Iterator<LETTER> traceIt = word.iterator();
		final Iterator<IRelevanceInformation> relIt = relevanceInformation.iterator();
		final List<LETTER> result = new ArrayList<>();
		while (traceIt.hasNext()) {
			final LETTER stmt = traceIt.next();
			final RelevanceInformation rel = (RelevanceInformation) relIt.next();
			if (rel != null && (rel.getCriterion1GF() || rel.getCriterion1UC())) {
				result.add(stmt);
			}
		}
		return result;
	}

	private static <LETTER> void aggregate(final Collection<LETTER> newResponsibleStmts,
			final Map<IcfgLocation, Set<LETTER>> finalLoc2responsibleStmts, final ArrayList<IPredicate> stateSequence) {
		final IcfgLocation finalLoc = ((ISLPredicate) stateSequence.get(stateSequence.size() - 1)).getProgramPoint();
		Set<LETTER> responsibleStmts = finalLoc2responsibleStmts.get(finalLoc);
		if (responsibleStmts == null) {
			// we start with all responsible statements in this trace
			responsibleStmts = new HashSet<>(newResponsibleStmts);
			finalLoc2responsibleStmts.put(finalLoc, responsibleStmts);
		} else {
			// we take the intersection with all responsible statements
			responsibleStmts.retainAll(newResponsibleStmts);
		}
	}

	private void presentResult(final Map<IcfgLocation, Set<LETTER>> finalLoc2responsibleStmts,
			final INestedWordAutomaton<LETTER, IPredicate> cfg,
			final List<ErrorLocalizationStatisticsGenerator> faultLocalizerStatistics) {
		if (mLogger.isWarnEnabled()) {
			final StringBuilder builder = new StringBuilder();
			final VpAlphabet<LETTER> vpAlphabet = cfg.getVpAlphabet();
			final int alphabetSize = vpAlphabet.getInternalAlphabet().size() + vpAlphabet.getCallAlphabet().size()
					+ vpAlphabet.getReturnAlphabet().size();
			for (final Entry<IcfgLocation, Set<LETTER>> entry : finalLoc2responsibleStmts.entrySet()) {
				builder.append("Error location '").append(entry.getKey());
				final Set<LETTER> statements = entry.getValue();
				if (statements.isEmpty()) {
					builder.append("' has no responsible statements (out of ").append(alphabetSize).append(").");
				} else {
					builder.append("' has the following ").append(statements.size())
							.append(" responsible statements (out of ").append(alphabetSize).append("):\n");
					for (final LETTER stmt : statements) {
						builder.append(stmt).append(", ");
					}
				}
				builder.append('\n');
			}

			long totalFaultLocalizationTimeNano = 0l;
			for (final ErrorLocalizationStatisticsGenerator stats : faultLocalizerStatistics) {
				totalFaultLocalizationTimeNano += stats.getErrorLocalizationTime();
			}
			builder.append("Fault localization was applied ").append(faultLocalizerStatistics.size())
					.append(" times and altogether took ")
					.append(StatisticsType.prettyprintNanoseconds(totalFaultLocalizationTimeNano)).append(" seconds.");

			mLogger.warn(builder);
		}
	}
}
