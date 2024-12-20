package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.OverapproxVariable;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.ModifiableNestedFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedSsaBuilder;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AberranceInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAberrance;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;

/**
 * TODO
 **/

public class TraceAberrantChecker<L extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private AberranceInformation[] mTraceAberranceList;
	private final IIcfgSymbolTable mSymbolTable;
	private final PredicateFactory mPredicateFactory;
	private final ErrorLocalizationStatisticsGenerator mErrorLocalizationStatisticsGenerator;
	private TracePredicates[] mPrePostSequences;
	private final List<L> mPredicateSkipList;
	private int mFirstOverapproxVariable;
	private int mLastOverapproxVariable;

	// TODO ?
	private final boolean mApplyQuantifierElimination = true;

	public TraceAberrantChecker(final NestedRun<L, IPredicate> counterexample, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final ModifiableGlobalsTable modifiableGlobalsTable, final IPredicateUnifier predicateUnifier,
			final RelevanceAnalysisMode faultLocalizationMode, final SimplificationTechnique simplificationTechnique,
			final IIcfgSymbolTable symbolTable, final IIcfg<IcfgLocation> IIcfg) {
		mServices = services;
		mPredicateSkipList = new ArrayList<>();
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mSymbolTable = symbolTable;
		mPredicateFactory = predicateFactory;
		mTraceAberranceList = new AberranceInformation[counterexample.getWord().length()];
		for (int i = 0; i < mTraceAberranceList.length; i++) {
			mTraceAberranceList[i] = new AberranceInformation(TraceAberrance.MAYBE);
		}
		doTraceAberrantAnalysis(counterexample.getWord(), predicateUnifier.getTruePredicate(),
				predicateUnifier.getFalsePredicate(), modifiableGlobalsTable, csToolkit, predicateUnifier);

		mErrorLocalizationStatisticsGenerator = new ErrorLocalizationStatisticsGenerator();
		mFirstOverapproxVariable = -1;
		mLastOverapproxVariable = Integer.MAX_VALUE;
		mErrorLocalizationStatisticsGenerator.continueErrorLocalizationTime();

	}

	public List<IRelevanceInformation> getAberranceInformation() {
		return Arrays.asList(mTraceAberranceList);
	}

	private void doTraceAberrantAnalysis(final NestedWord<L> counterexampleWord, final IPredicate truePredicate,
			final IPredicate falsePredicate, final ModifiableGlobalsTable modGlobVarManager,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier) {
		mLogger.info("started trace aberrance");
		// abort if no VariableOverapproximation in trace
		boolean abort = true;
		final Map<IProgramVar, List<Integer>> overapproximatedVariables = new HashMap<>();
		for (int i = 0; i < counterexampleWord.length(); i++) {
			final IElement elem = counterexampleWord.getSymbol(i);
			final Overapprox overapprox = Overapprox.getAnnotation(elem);
			if (overapprox != null) {
				if (!(overapprox instanceof OverapproxVariable)) {
					// cannot analyse error trace for other overapproximations
					mLogger.info("aborting trace aberrance, other Overapproximation: " + overapprox.toString());
					return;
				}
				mLogger.info("OverapproxVariable in trace: " + overapprox.toString());
				// found overapproximation of variable, therefore analyse error trace
				abort = false;
				if (mFirstOverapproxVariable == -1) {
					mFirstOverapproxVariable = i;
				}
				if (i > mLastOverapproxVariable) {
					mLastOverapproxVariable = i;
				}
				if (elem instanceof CodeBlock) {
					// for (IProgramVar outvar :
					// ((CodeBlock)elem).getTransformula().getOutVars().keySet()) {
					//// TermVariable termVariable =
					// ((CodeBlock)elem).getTransformula().getOutVars().get(outvar);
					// if (!overapproximatedVariables.containsKey(outvar)) {
					// overapproximatedVariables.put(outvar, new ArrayList<Integer>());
					// }
					// overapproximatedVariables.get(outvar).add(i);
					// }
					for (final IProgramVar outvar : ((CodeBlock) elem).getTransformula().getAssignedVars()) {
						// TermVariable termVariable =
						// ((CodeBlock)elem).getTransformula().getOutVars().get(outvar);
						if (!overapproximatedVariables.containsKey(outvar)) {
							overapproximatedVariables.put(outvar, new ArrayList<>());
						}
						overapproximatedVariables.get(outvar).add(i);
					}
				}

			}
		}
		if (abort) {
			mLogger.info("aborting trace aberrance, no OverapproxVariable");
			return;
		}

		// TODO setting
		if (false) {
			final DefaultTransFormulas<L> dtf = new DefaultTransFormulas<>(counterexampleWord, truePredicate,
					falsePredicate, Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
			final NestedSsaBuilder<L> nBuilder = new NestedSsaBuilder<>(csToolkit.getManagedScript(), csToolkit, dtf,
					mLogger);
			final NestedFormulas<L, Term, Term> nFormulas = nBuilder.getSsa();
			final List<Term> terms = new ArrayList<>();
			final List<TermVariable> quantifiedVars = new ArrayList<>();
			final var a = nBuilder.getIndexedVarRepresentative();
			if (nFormulas instanceof ModifiableNestedFormulas) {
				for (int i = 0; i < nFormulas.getTrace().length(); i++) {
					if (nFormulas.callPositions().contains(i)) {
						terms.add(nFormulas.getGlobalVarAssignment(i));
						terms.add(nFormulas.getLocalVarAssignment(i));
						terms.add(nFormulas.getOldVarAssignment(i));
					} else {
						terms.add(nFormulas.getFormulaFromNonCallPos(i));
					}
					// Overapprox overapprox =
					// Overapprox.getAnnotation(nFormulas.getTrace().getSymbol(i));
					// if (overapprox != null && overapprox instanceof OverapproxVariable) {
					// for (IProgramVar outvar :
					// ((CodeBlock)nFormulas.getTrace().getSymbol(i)).getTransformula().getOutVars().keySet())
					// {
					// Term t = a.get(outvar).get(i);
					// if (t != null) {
					// System.out.print("");
					// }
					//
					// }
					// }
				}

				Term term = SmtUtils.and(csToolkit.getManagedScript().getScript(), terms);
				final Map<Term, Term> newVarMap = new HashMap<>();
				for (final IProgramVar lpv : overapproximatedVariables.keySet()) {
					for (final int i : overapproximatedVariables.get(lpv)) {
						final Term t = a.get(lpv).get(i);
						if (t != null) {
							final TermVariable newTVariable = csToolkit.getManagedScript().constructFreshTermVariable(
									((ApplicationTerm) t).getFunction().getName(), t.getSort());
							newVarMap.put(t, newTVariable);
							quantifiedVars.add(newTVariable);
						}

					}
				}
				final List<ApplicationTerm> allVarApplicationTerms = new ArrayList<>();
				// GetAllApplicationTermVariables(term, allVarApplicationTerms);
				final List<Map<Term, Term>> hashMaps = new ArrayList<>();
				for (int i = 0; i < nBuilder.getVariable2Constant().getTrace().length(); i++) {
					if (nFormulas.callPositions().contains(i)) {
						hashMaps.add(nBuilder.getVariable2Constant().getGlobalVarAssignment(i));
						hashMaps.add(nBuilder.getVariable2Constant().getLocalVarAssignment(i));
						hashMaps.add(nBuilder.getVariable2Constant().getOldVarAssignment(i));
					} else {
						hashMaps.add(nBuilder.getVariable2Constant().getFormulaFromNonCallPos(i));
					}
				}
				for (final Map<Term, Term> map : hashMaps) {
					for (final Term t : map.values()) {
						allVarApplicationTerms.add((ApplicationTerm) t);
					}
				}
				for (final IProgramVar t : a.keySet()) {
					final TreeMap<Integer, Term> map = a.get(t);
					for (final int i : map.keySet()) {
						final Term applicationTerm = map.get(i);
						assert applicationTerm instanceof ApplicationTerm;
						allVarApplicationTerms.add((ApplicationTerm) applicationTerm);
					}
				}
				final List<TermVariable> nonOverapproxVars = new ArrayList<>();
				for (final ApplicationTerm t : allVarApplicationTerms) {
					if (!newVarMap.containsKey(t)) {
						final TermVariable newTVariable = csToolkit.getManagedScript()
								.constructFreshTermVariable(t.getFunction().getName(), t.getSort());
						newVarMap.put(t, newTVariable);
						nonOverapproxVars.add(newTVariable);

					}
				}
				term = PureSubstitution.apply(csToolkit.getManagedScript().getScript(), newVarMap, term);
				// final BigInteger minValue = mTypeSizes.getMinValueOfPrimitiveType(type);
				// final Expression greaterMinValue = ExpressionFactory.newBinaryExpression(loc,
				// Operator.COMPGEQ,
				// auxvar,
				// ExpressionFactory.createIntegerLiteral(loc, minValue.toString()));
				// TODO alles in ein oder
				term = SmtUtils.quantifier(csToolkit.getManagedScript().getScript(), QuantifiedFormula.EXISTS,
						nonOverapproxVars, term);
				for (final TermVariable quantifiedVar : quantifiedVars) {
					term = SmtUtils.or(csToolkit.getManagedScript().getScript(),
							SmtUtils.greater(csToolkit.getManagedScript().getScript(), quantifiedVar,
									csToolkit.getManagedScript().getScript().numeral(BigInteger.valueOf(4294967295L))),
							SmtUtils.greater(csToolkit.getManagedScript().getScript(),
									csToolkit.getManagedScript().getScript().numeral(BigInteger.valueOf(0)),
									quantifiedVar),
							term);
				}
				term = SmtUtils.quantifier(csToolkit.getManagedScript().getScript(), QuantifiedFormula.FORALL,
						quantifiedVars, term);
				final var t = SmtUtils.checkSatTerm(csToolkit.getManagedScript().getScript(), term);
				if (t == LBool.SAT) {
					mLogger.info("Success checkSatTerm");
					// TODO only overapprox
					for (int i = 0; i < mTraceAberranceList.length; i++) {
						mTraceAberranceList[i] = new AberranceInformation(TraceAberrance.NO);
					}
					return;
				}
			}

		}

		mPrePostSequences = calculatePrePost(csToolkit, falsePredicate, truePredicate, counterexampleWord,
				mFirstOverapproxVariable, mLastOverapproxVariable);
		final List<Boolean> toCheck = new ArrayList<>();
		for (final L edge : counterexampleWord) {
			final Overapprox overapprox = Overapprox.getAnnotation(edge);
			toCheck.add(overapprox instanceof OverapproxVariable);
			// toCheck.add(overapprox != null);
		}
		mTraceAberranceList = checkHoareTriples(csToolkit, counterexampleWord, mPrePostSequences, toCheck);
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		if (prefs.getBoolean(
				TraceAbstractionPreferenceInitializer.LABEL_TRACE_ABERRANCE_CHECKER_IF_ELSE_ANALYSIS_ENABLED)
				&& !noOverapproxVariableTraceAberrant(counterexampleWord)) {
			final Integer maxPaths = prefs.getInt(
					TraceAbstractionPreferenceInitializer.LABEL_TRACE_ABERRANCE_CHECKER_IF_ELSE_ANALYSIS_MAX_PATHS);
			final Integer maxPathLength = prefs.getInt(
					TraceAbstractionPreferenceInitializer.LABEL_TRACE_ABERRANCE_CHECKER_IF_ELSE_ANALYSIS_MAX_PATH_LENGTH);
			for (int i = counterexampleWord.length() - 1; i >= 0; i--) {
				boolean currentAssumeIrrelevant = false;
				final IcfgEdge cBlock = (IcfgEdge) counterexampleWord.getSymbol(i);
				final ConditionAnnotation cAnnotation = ConditionAnnotation.getAnnotation(cBlock);
				final Check check = Check.getAnnotation(cBlock);
				if (cAnnotation == null || check != null) {
					continue;
				}

				for (final IElement edge : cBlock.getSource().getOutgoingEdges()) {
					final ConditionAnnotation edgeAnnotation = ConditionAnnotation.getAnnotation(edge);
					if (edgeAnnotation == null || edgeAnnotation.isNegated() == cAnnotation.isNegated()) {
						continue;
					}
					// find end of split
					List<IcfgLocation> currentPath = new ArrayList<>();
					for (int j = i; j < counterexampleWord.length(); j++) {
						currentPath.add(counterexampleWord.getSymbol(j).getTarget());
					}
					final List<List<IcfgLocation>> otherPaths = new ArrayList<>();
					final List<List<IcfgEdge>> otherPathsEdges = new ArrayList<>();
					List<IcfgLocation> otherPath = new ArrayList<>();
					List<IcfgEdge> otherPathEdges = new ArrayList<>();
					otherPaths.add(otherPath);
					otherPathsEdges.add(otherPathEdges);

					otherPath.add(((IcfgEdge) edge).getTarget());
					otherPathEdges.add((IcfgEdge) edge);
					final IcfgLocation currentNode = ((IcfgEdge) edge).getTarget();
					final int currentPathEnd = findOtherPathEndAndOtherPaths(currentPath, otherPath, otherPathEdges,
							otherPaths, otherPathsEdges, maxPaths, maxPathLength);
					if (currentPathEnd == 0) {
						break;
					}
					currentPath = currentPath.subList(0, currentPathEnd);

					boolean currentPathIrrelevant = true;
					// check current path
					final List<Boolean> newToCheck = new ArrayList<>();
					for (int j = 0; j < counterexampleWord.length(); j++) {
						newToCheck.add(j > i && j < i + currentPath.size());
					}
					TracePredicates[] prePostSequence = mPrePostSequences;
					int lastToCheck = -1;
					int firstToCheck = -1;
					for (int j = 0; j < newToCheck.size(); j++) {
						if (newToCheck.get(j)) {
							if (firstToCheck == -1) {
								firstToCheck = j;
							}
							lastToCheck = j;
						}
					}
					if (mFirstOverapproxVariable > firstToCheck || mLastOverapproxVariable < lastToCheck) {
						prePostSequence = calculatePrePost(csToolkit, falsePredicate, truePredicate, counterexampleWord,
								firstToCheck, lastToCheck);
					}
					final AberranceInformation[] traceAberrantList = checkHoareTriples(csToolkit, counterexampleWord,
							prePostSequence, newToCheck);
					for (int j = 1; j < currentPath.size(); j++) {
						if (traceAberrantList[i + j].GetTraceAberrance() != TraceAberrance.NO) {
							currentPathIrrelevant = false;
							break;
						}
					}
					if (!currentPathIrrelevant) {
						break;
					}
					// check other paths
					currentAssumeIrrelevant = true;
					for (int path = 0; path < otherPaths.size(); path++) {
						if (!currentAssumeIrrelevant) {
							break;
						}
						otherPath = otherPaths.get(path);
						otherPathEdges = otherPathsEdges.get(path);
						final IcfgEdge[] newOtherPath = new IcfgEdge[counterexampleWord.length() + otherPath.size()
								- currentPath.size()];
						final List<Boolean> newCheck = new ArrayList<>();
						for (int j = 0; j < i; j++) {
							newOtherPath[j] = (IcfgEdge) counterexampleWord.getSymbol(j);
							newCheck.add(false);
						}
						for (int j = 0; j < otherPathEdges.size(); j++) {
							newOtherPath[i + j] = otherPathEdges.get(j);
							newCheck.add(true);
						}
						for (int j = i + currentPath.size(); j < counterexampleWord.length(); j++) {
							newOtherPath[j - currentPath.size() + otherPath.size()] = (IcfgEdge) counterexampleWord
									.getSymbol(j);
							newCheck.add(false);
						}
						final int[] nestingRelations = new int[newOtherPath.length];
						final Stack<Integer> callStack = new Stack<>();
						for (int j = 0; j < nestingRelations.length; j++) {
							if (newOtherPath[j] instanceof Call) {
								callStack.add(j);
								nestingRelations[j] = NestedWord.PLUS_INFINITY;
							} else if (newOtherPath[j] instanceof Return) {
								nestingRelations[j] = callStack.peek();
								nestingRelations[callStack.pop()] = j;
							} else {
								nestingRelations[j] = NestedWord.INTERNAL_POSITION;
							}

						}
						lastToCheck = -1;
						firstToCheck = -1;
						for (int j = 0; j < newCheck.size(); j++) {
							if (newCheck.get(j)) {
								if (firstToCheck == -1) {
									firstToCheck = j;
								}
								lastToCheck = j;
							}
						}
						assert firstToCheck != -1 && lastToCheck != -1;
						final NestedWord<L> newCounterexample = new NestedWord<>((L[]) newOtherPath, nestingRelations);
						final TracePredicates[] prePost = calculatePrePost(csToolkit, falsePredicate, truePredicate,
								newCounterexample, firstToCheck, lastToCheck);
						final AberranceInformation[] aberranceInformations = checkHoareTriples(csToolkit,
								newCounterexample, prePost, newCheck);
						for (int j = 1; j < otherPathEdges.size(); j++) {
							if (aberranceInformations[i + j].GetTraceAberrance() != TraceAberrance.NO) {
								currentAssumeIrrelevant = false;
								break;
							}
						}
					}
				}
				if (currentAssumeIrrelevant) {
					mLogger.info("irrelevant assume: " + counterexampleWord.getSymbol(i));
					mPredicateSkipList.add(counterexampleWord.getSymbol(i));
					mPrePostSequences = calculatePrePost(csToolkit, falsePredicate, truePredicate, counterexampleWord,
							mFirstOverapproxVariable, mLastOverapproxVariable);
					mTraceAberranceList = checkHoareTriples(csToolkit, counterexampleWord, mPrePostSequences, toCheck);
					if (noOverapproxVariableTraceAberrant(counterexampleWord)) {
						break;
					}
				}

			}
		}

		mLogger.info("finished trace aberrance");
	}

	private boolean noOverapproxVariableTraceAberrant(final NestedWord<L> counterexampleWord) {
		for (int i = 0; i < counterexampleWord.length(); i++) {
			final Overapprox overapprox = Overapprox.getAnnotation(counterexampleWord.getSymbol(i));
			if (overapprox instanceof OverapproxVariable
					&& mTraceAberranceList[i].GetTraceAberrance() != TraceAberrance.NO) {
				// if (mTraceAberrantList[i].GetTraceAberrance() != TraceAberrance.NO) {
				return false;
			}
		}
		return true;

	}

	private TracePredicates[] calculatePrePost(final CfgSmtToolkit csToolkit, final IPredicate falsePredicate,
			final IPredicate truePredicate, final NestedWord<L> counterexampleWord, final int firstOverapproxVariable,
			final int lastOverapproxVariable) {
		// calculate Pre and Post
		final DefaultTransFormulas<L> dtf = new DefaultTransFormulas<>(counterexampleWord, truePredicate,
				falsePredicate, Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
		final IterativePredicateTransformer<L> iptPre = new IterativePredicateTransformer<>(mPredicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices, counterexampleWord,
				null, mPredicateFactory.not(falsePredicate), null, mPredicateFactory.not(falsePredicate),
				SimplificationTechnique.NONE, mSymbolTable);
		final IterativePredicateTransformer<L> iptSp = new IterativePredicateTransformer<>(mPredicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices, counterexampleWord,
				truePredicate, null, null, mPredicateFactory.not(falsePredicate), SimplificationTechnique.NONE,
				mSymbolTable);
		final List<IPredicatePostprocessor> postprocessors;
		// if (false && mApplyQuantifierElimination) {
		// final QuantifierEliminationPostprocessor qePostproc =
		// new QuantifierEliminationPostprocessor(mServices,
		// csToolkit.getManagedScript(), mPredicateFactory,
		// SimplificationTechnique.POLY_PAC);
		// postprocessors = Collections.singletonList(qePostproc);
		// } else {
		postprocessors = Collections.emptyList();
		// }
		TracePredicates preSequence;
		TracePredicates postSequence;

		try {
			mLogger.info("started wp calc");
			preSequence = iptPre.computePreSequence(dtf, postprocessors, false, firstOverapproxVariable,
					mPredicateSkipList);
			// preSequence = iptPre.computePreSequence(dtf, postprocessors, false,
			// firstOverapproxVariable);
			mLogger.info("started sp calc");
			postSequence = iptSp.computeStrongestPostconditionSequence(dtf, postprocessors, lastOverapproxVariable,
					mPredicateSkipList);
			// strongestPostconditionSequence =
			// iptSp.computeStrongestPostconditionSequence(dtf, postprocessors,
			// lastOverapproxVariable);
			mLogger.info("finished sp calc");
			// evtl nur teilweise
		} catch (final TraceInterpolationException e) {
			throw new RuntimeException(e);
		}
		return new TracePredicates[] { preSequence, postSequence };
	}

	private AberranceInformation[] checkHoareTriples(final CfgSmtToolkit csToolkit,
			final NestedWord<L> counterexampleWord, final TracePredicates[] prePostPredicates,
			final List<Boolean> toCheck) {
		assert toCheck.size() == counterexampleWord.length();
		final List<AberranceInformation> traceAberranceList = new ArrayList<>();
		final MonolithicHoareTripleChecker hc = new MonolithicHoareTripleChecker(csToolkit);
		final FaultLocalizationRelevanceChecker faultLocalizationRelevanceChecker = new FaultLocalizationRelevanceChecker(
				mServices, csToolkit);
		for (int i = 0; i < counterexampleWord.length(); i++) {
			if (!toCheck.get(i)) {
				traceAberranceList.add(new AberranceInformation(TraceAberrance.MAYBE));
				continue;
			}
			final IPredicate pre = prePostPredicates[0].getPredicate(i + 1);
			final IPredicate sp = prePostPredicates[1].getPredicate(i - 1);
			IInternalAction internal;
			try {
				internal = faultLocalizationRelevanceChecker.constructHavocedInternalAction(mServices,
						(IInternalAction) counterexampleWord.getSymbol(i), csToolkit.getManagedScript());

			} catch (final Exception e) {
				// TODO: handle exception
				traceAberranceList.add(new AberranceInformation(TraceAberrance.MAYBE));
				continue;
			}
			Validity res = null;
			try {
				res = hc.checkInternal(sp, internal, pre);
			} catch (final Exception e) {
				// TODO: handle exception
				mLogger.info(e.getMessage());
			}

			if (res == Validity.VALID) {
				traceAberranceList.add(new AberranceInformation(TraceAberrance.NO));
			} else if (res == Validity.INVALID) {
				traceAberranceList.add(new AberranceInformation(TraceAberrance.YES));
			} else {
				mLogger.info("Validity neither Valid nor invalid");
				traceAberranceList.add(new AberranceInformation(TraceAberrance.MAYBE));
			}
		}
		return traceAberranceList.toArray(new AberranceInformation[traceAberranceList.size()]);
	}

	private static int findOtherPathEndAndOtherPaths(final List<IcfgLocation> currentPath,
			final List<IcfgLocation> otherPath, final List<IcfgEdge> otherPathEdges,
			final List<List<IcfgLocation>> otherPaths, final List<List<IcfgEdge>> otherPathsEdges, final int maxPaths,
			final int maxPathLength) {
		assert otherPath.size() > 0 && currentPath.size() > 0;
		IcfgLocation currentNode = otherPath.get(otherPath.size() - 1);
		if (currentPath.contains(currentNode)) {
			return 1;
		}
		while (true) {
			if (currentNode.getIncomingEdges().size() > 1) {
				return 0;
			}
			if (currentNode.getOutgoingEdges().size() == 0) {
				return 0;
			}
			if (currentNode.getOutgoingEdges().size() > 1) {
				for (int i = 1; i < currentNode.getOutgoingEdges().size(); i++) {
					if (otherPaths.size() >= maxPaths && maxPaths != 0) {
						return 0;
					}
					final IcfgEdge newEdge = currentNode.getOutgoingEdges().get(i);
					if (!(newEdge instanceof CodeBlock) || !((CodeBlock) newEdge instanceof StatementSequence)) {
						return 0;
					}
					final List<IcfgLocation> newPath = new ArrayList<>(otherPath);
					final List<IcfgEdge> newEdges = new ArrayList<>(otherPathEdges);
					newPath.add(newEdge.getTarget());
					newEdges.add(newEdge);
					otherPaths.add(newPath);
					otherPathsEdges.add(newEdges);
					if (findOtherPathEndAndOtherPaths(currentPath, newPath, newEdges, otherPaths, otherPathsEdges,
							maxPaths, maxPathLength) == 0) {
						return 0;
					}
				}
			}
			if (otherPath.size() > maxPathLength && maxPathLength != 0) {
				return 0;
			}
			final IcfgEdge newEdge = currentNode.getOutgoingEdges().get(0);
			if (!(newEdge instanceof CodeBlock) || !((CodeBlock) newEdge instanceof StatementSequence)) {
				if (newEdge instanceof SequentialComposition) {
					for (final var st : ((SequentialComposition) newEdge).getCodeBlocks()) {
						if (!(st instanceof StatementSequence)) {
							return 0;
						}
					}
				} else {
					return 0;
				}
			}
			final IcfgLocation newNode = newEdge.getTarget();
			otherPathEdges.add(newEdge);
			otherPath.add(newNode);
			final int index = currentPath.indexOf(newNode);
			if (index != -1) {
				return index + 1;
			}

			currentNode = newNode;
		}
	}

}
