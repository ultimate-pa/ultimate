package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorlocalization;

import java.io.Console;
import java.io.ObjectOutputStream.PutField;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import javax.management.NotificationBroadcaster;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ConditionAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.OverapproxVariable;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IRelevanceInformation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.LocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.PureSubstitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtLibUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierOverapproximator.Quantifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.VarAbsConstraints;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.QuantifierEliminationPostprocessor;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.ModifiableNestedFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedSsaBuilder;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AberranceInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TraceAberrance;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RelevanceAnalysisMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.FaultLocalizationRelevanceChecker;

/**
TODO
**/

public class TraceAberrantChecker<L extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private AberranceInformation[] mTraceAberrantList;
	private final IIcfgSymbolTable mSymbolTable;
	private final PredicateFactory mPredicateFactory;
	private final ErrorLocalizationStatisticsGenerator mErrorLocalizationStatisticsGenerator;
	private TracePredicates[] mPrePostSequences;
	private List<L> mPredicateSkipList;
	private int mFirstOverapproxVariable;
	private int mLastOverapproxVariable;
	

	// TODO ?
	private final boolean mApplyQuantifierElimination = true;
	
	
	public TraceAberrantChecker(final NestedRun<L, IPredicate> counterexample,
			final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final ModifiableGlobalsTable modifiableGlobalsTable, final IPredicateUnifier predicateUnifier,
			final RelevanceAnalysisMode faultLocalizationMode, final SimplificationTechnique simplificationTechnique,
			final IIcfgSymbolTable symbolTable,
			final IIcfg<IcfgLocation> IIcfg) {
		mServices = services;
		mPredicateSkipList = new ArrayList<>();
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mSymbolTable = symbolTable;
		mPredicateFactory = predicateFactory;
		mTraceAberrantList = new AberranceInformation[counterexample.getWord().length()];
		for (int i = 0; i < mTraceAberrantList.length; i++) {
			mTraceAberrantList[i] = new AberranceInformation(TraceAberrance.MAYBE);
		}
		doTraceAberrantAnalysis(counterexample.getWord(), predicateUnifier.getTruePredicate(),
				predicateUnifier.getFalsePredicate(), modifiableGlobalsTable, csToolkit, predicateUnifier);
		
		mErrorLocalizationStatisticsGenerator = new ErrorLocalizationStatisticsGenerator();
		this.mFirstOverapproxVariable = -1;
		this.mLastOverapproxVariable = Integer.MAX_VALUE;
		mErrorLocalizationStatisticsGenerator.continueErrorLocalizationTime();
		
	}
	
	public List<IRelevanceInformation> getAberranceInformation() {
		return Arrays.asList(mTraceAberrantList);
	}
	
	private void doTraceAberrantAnalysis(final NestedWord<L> counterexampleWord, final IPredicate truePredicate,
			final IPredicate falsePredicate, final ModifiableGlobalsTable modGlobVarManager,
			final CfgSmtToolkit csToolkit, final IPredicateUnifier predicateUnifier){
		mLogger.info("started trace aberrance");
		// abort if no VariableOverapproximation in trace
		boolean abort = true;
		Map<IProgramVar, List<Integer>> overapproximatedVariables = new HashMap<>();
		for (int i = 0; i < counterexampleWord.length(); i++) {
			final IElement elem = counterexampleWord.getSymbol(i);
			final Overapprox overapprox = Overapprox.getAnnotation(elem);
			if (overapprox != null) {
				if (!(overapprox instanceof OverapproxVariable)) {
					// cannot analyse error trace for other overapproximations
					mLogger.info("aborting trace aberrance, other Overapproximation: " + overapprox.toString());
//					return;
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
					for (IProgramVar outvar : ((CodeBlock)elem).getTransformula().getOutVars().keySet()) {
//						TermVariable termVariable = ((CodeBlock)elem).getTransformula().getOutVars().get(outvar);
						if (!overapproximatedVariables.containsKey(outvar)) {
							overapproximatedVariables.put(outvar, new ArrayList<Integer>());
						}
						overapproximatedVariables.get(outvar).add(i);
					}
					for (IProgramVar outvar : ((CodeBlock)elem).getTransformula().getAssignedVars()) {
//						TermVariable termVariable = ((CodeBlock)elem).getTransformula().getOutVars().get(outvar);
						if (!overapproximatedVariables.containsKey(outvar)) {
							overapproximatedVariables.put(outvar, new ArrayList<Integer>());
						}
						overapproximatedVariables.get(outvar).add(i);
					}
				}

			}
		}
		if (abort) {
			mLogger.info("aborting trace aberrance, no OverapproxVariable");
//			return;
		}
		
		// TODO setting
		if (false) {
			final DefaultTransFormulas<L> dtf = new DefaultTransFormulas<>(counterexampleWord, truePredicate,
					falsePredicate, Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
			NestedSsaBuilder<L> nBuilder = new NestedSsaBuilder<>(counterexampleWord, csToolkit.getManagedScript(), csToolkit, dtf, mLogger, true);
			NestedFormulas<L, Term, Term> nFormulas = nBuilder.getSsa();
			List<Term> terms = new ArrayList<>();
			List<TermVariable> quantifiedVars = new ArrayList<>();
			var a = nBuilder.getIndexedVarRepresentative();
			if (nFormulas instanceof ModifiableNestedFormulas) {
				for (int i = 0; i < nFormulas.getTrace().length(); i++) {
					if (nFormulas.callPositions().contains(i)) {
						terms.add(nFormulas.getGlobalVarAssignment(i));
						terms.add(nFormulas.getLocalVarAssignment(i));
						terms.add(nFormulas.getOldVarAssignment(i));
					} else {
						terms.add(nFormulas.getFormulaFromNonCallPos(i));
					}
//					Overapprox overapprox = Overapprox.getAnnotation(nFormulas.getTrace().getSymbol(i));
//					if (overapprox != null && overapprox instanceof OverapproxVariable) {
//						for (IProgramVar outvar : ((CodeBlock)nFormulas.getTrace().getSymbol(i)).getTransformula().getOutVars().keySet()) {
//							Term t = a.get(outvar).get(i);
//							if (t != null) {
//								System.out.print("");
//							}
//							
//						}
//					}
				}
				Term term = SmtUtils.and(csToolkit.getManagedScript().getScript(), terms);
				Map<Term, Term> newVarMap = new HashMap<>();
				for (IProgramVar lpv : overapproximatedVariables.keySet()) {
					for (int i : overapproximatedVariables.get(lpv)) {
						Term t = a.get(lpv).get(i);
						if (t != null) {
							TermVariable newTVariable = csToolkit.getManagedScript().constructFreshTermVariable(((ApplicationTerm)t).getFunction().getName(), t.getSort());
							newVarMap.put(t, newTVariable);
							quantifiedVars.add(newTVariable);
						}
						
					}
				}
				term = Substitution.apply(csToolkit.getManagedScript().getScript(), newVarMap, term);
//				final BigInteger minValue = mTypeSizes.getMinValueOfPrimitiveType(type);
//				final Expression greaterMinValue = ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar,
//						ExpressionFactory.createIntegerLiteral(loc, minValue.toString()));
				// TODO alles in ein oder
//				for (TermVariable quantifiedVar : quantifiedVars) {
//					term = SmtUtils.or(csToolkit.getManagedScript().getScript(), SmtUtils.greater(csToolkit.getManagedScript().getScript(), quantifiedVar, csToolkit.getManagedScript().getScript().numeral(BigInteger.valueOf(1))),
//							SmtUtils.greater(csToolkit.getManagedScript().getScript(), csToolkit.getManagedScript().getScript().numeral(BigInteger.valueOf(0)), quantifiedVar), term);
//				}
				term = SmtUtils.quantifier(csToolkit.getManagedScript().getScript(), QuantifiedFormula.FORALL, quantifiedVars, term);
				var t = SmtUtils.checkSatTerm((Script) csToolkit.getManagedScript().getScript(), term);
				if (t == LBool.SAT) {
					mLogger.info("Success checkSatTerm");
					// TODO only overapprox
					for (int i = 0; i < mTraceAberrantList.length; i++) {
						mTraceAberrantList[i] = new AberranceInformation(TraceAberrance.NO);
					}
					return;
				}
			}
			

		}
		
		mPrePostSequences = calculatePrePost(csToolkit, falsePredicate, truePredicate, counterexampleWord);
		List<Boolean> toCheck = new ArrayList<>();
		for (L edge : counterexampleWord) {
			Overapprox overapprox = Overapprox.getAnnotation(edge);
			toCheck.add(overapprox != null && overapprox instanceof OverapproxVariable);
		}
		mTraceAberrantList = checkHoareTriples(csToolkit, counterexampleWord, toCheck);
		
		
		if (!noOverapproxVariableTraceAberrant(counterexampleWord)) {
			for (int i = counterexampleWord.length()-1; i>=0; i--) {
				boolean currentAssumeIrrelevant = false;
				CodeBlock cBlock = (CodeBlock)counterexampleWord.getSymbol(i);
				ConditionAnnotation cAnnotation = ConditionAnnotation.getAnnotation(cBlock);
				Check check = Check.getAnnotation(cBlock);
				if (cAnnotation == null || check != null) continue;
				
				for (IElement edge : cBlock.getSource().getOutgoingEdges()) {
					ConditionAnnotation edgeAnnotation = ConditionAnnotation.getAnnotation(edge);
					if (edgeAnnotation == null || edgeAnnotation.isNegated() == cAnnotation.isNegated()) continue;				
					System.out.print("");
					if (cBlock.getTarget() == ((CodeBlock)edge).getTarget()) {
						// empty split
						currentAssumeIrrelevant = true;
						break;
					}
					// find end of split
					List<IcfgLocation> currentPath = new ArrayList<>();
					for (int j = i; j < counterexampleWord.length(); j++) {
						currentPath.add(counterexampleWord.getSymbol(j).getTarget());
					}
					List<IcfgLocation> otherPath = new ArrayList<>();
					otherPath.add(((CodeBlock)edge).getTarget());
					IcfgLocation currentNode = ((CodeBlock)edge).getTarget();
					
					boolean successFindingEnd = false;
					
					while (true) {
						if (currentNode.getOutgoingEdges().size() != 1) {
							break;
						}
						IcfgLocation newNode = currentNode.getOutgoingEdges().get(0).getTarget();
						otherPath.add(newNode);
						int index = currentPath.indexOf(newNode);
						if (index != -1) {
							currentPath = currentPath.subList(0, index+1);
							successFindingEnd = true;
							break;
						}
					}
					if (!successFindingEnd) {
						break;
					}
					boolean currentPathIrrelevant = true;
					List<Boolean> newToCheck = new ArrayList<>();
					for (int j = 0; j < counterexampleWord.length(); j++) {
						newToCheck.add(j > i && j < i + currentPath.size());
					}
					AberranceInformation[] traceAberrantList = checkHoareTriples(csToolkit, counterexampleWord, newToCheck);
					for (int j = 1; j < currentPath.size(); j++) {
						if (traceAberrantList[i+j].GetTraceAberrance() != TraceAberrance.NO) {
							currentPathIrrelevant = false;
							break;
						}
					}
					if (!currentPathIrrelevant) {
						break;
					}
					if (otherPath.size() == 1) {
						currentAssumeIrrelevant = true;
						break;
					}
					//TODO else part
				}
				if (currentAssumeIrrelevant) {
					mPredicateSkipList.add(counterexampleWord.getSymbol(i));
					mPrePostSequences = calculatePrePost(csToolkit, falsePredicate, truePredicate, counterexampleWord);
					mTraceAberrantList = checkHoareTriples(csToolkit, counterexampleWord, toCheck);
				}
				
				
				
			}
		}
		
		
		
		mLogger.info("finished trace aberrance");
	}
	
	private boolean noOverapproxVariableTraceAberrant(final NestedWord<L> counterexampleWord) {
		for (int i = 0; i < counterexampleWord.length(); i++) {
			Overapprox overapprox = Overapprox.getAnnotation(counterexampleWord.getSymbol(i));
			if (overapprox instanceof OverapproxVariable && mTraceAberrantList[i].GetTraceAberrance() != TraceAberrance.NO) {
				return false;
			}
		}
		return true;
		
	}
	
	private TracePredicates[] calculatePrePost(CfgSmtToolkit csToolkit, IPredicate falsePredicate, IPredicate truePredicate, NestedWord<L> counterexampleWord) {
		// calculate Pre and Post
		final DefaultTransFormulas<L> dtf = new DefaultTransFormulas<>(counterexampleWord, truePredicate,
				falsePredicate, Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
		final IterativePredicateTransformer<L> iptPre = new IterativePredicateTransformer<>(mPredicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices, counterexampleWord,
				null, mPredicateFactory.not(falsePredicate), null, mPredicateFactory.not(falsePredicate), SimplificationTechnique.NONE,
				mSymbolTable);
		final IterativePredicateTransformer<L> iptSp = new IterativePredicateTransformer<>(mPredicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices, counterexampleWord,
				truePredicate, null, null, mPredicateFactory.not(falsePredicate), SimplificationTechnique.NONE,
				mSymbolTable);
		final List<IPredicatePostprocessor> postprocessors;
//				if (false && mApplyQuantifierElimination) {
//					final QuantifierEliminationPostprocessor qePostproc =
//							new QuantifierEliminationPostprocessor(mServices, csToolkit.getManagedScript(), mPredicateFactory,
//									SimplificationTechnique.POLY_PAC);
//					postprocessors = Collections.singletonList(qePostproc);
//				} else {
			postprocessors = Collections.emptyList();
//				}
		TracePredicates preSequence;
		TracePredicates postSequence;
		
		try {
			mLogger.info("started wp calc");
			preSequence = iptPre.computePreSequence(dtf, postprocessors, false, mFirstOverapproxVariable, mPredicateSkipList);
//					preSequence = iptPre.computePreSequence(dtf, postprocessors, false, firstOverapproxVariable);
			mLogger.info("started sp calc");
			postSequence = iptSp.computeStrongestPostconditionSequence(dtf, postprocessors, mLastOverapproxVariable, mPredicateSkipList);
//					strongestPostconditionSequence = iptSp.computeStrongestPostconditionSequence(dtf, postprocessors, lastOverapproxVariable);
			mLogger.info("finished sp calc");
			// evtl nur teilweise
		} catch (TraceInterpolationException e) {
			throw new RuntimeException(e);
		}
		return new TracePredicates[] {preSequence, postSequence};
	}
	
	private AberranceInformation[] checkHoareTriples(CfgSmtToolkit csToolkit, NestedWord<L> counterexampleWord, List<Boolean> toCheck) {
		assert toCheck.size() == counterexampleWord.length();
		List<AberranceInformation> traceAberranceList = new ArrayList<>();
		MonolithicHoareTripleChecker hc = new MonolithicHoareTripleChecker(csToolkit);
		FaultLocalizationRelevanceChecker faultLocalizationRelevanceChecker = new FaultLocalizationRelevanceChecker(mServices, csToolkit);
		for (int i = 0; i < counterexampleWord.length(); i++) {
			if (!toCheck.get(i)) {
				traceAberranceList.add(new AberranceInformation(TraceAberrance.MAYBE));
				continue;
			}
			final IPredicate pre = mPrePostSequences[0].getPredicate(i+1);
			final IPredicate sp = mPrePostSequences[1].getPredicate(i);
			IInternalAction internal = faultLocalizationRelevanceChecker.constructHavocedInternalAction(mServices, (IInternalAction)counterexampleWord.getSymbol(i), csToolkit.getManagedScript());
			// TODO check if internal possible
			Validity res = null;
			try {
				 res = (hc.checkInternal(sp, internal, pre));
			} catch (Exception e) {
				// TODO: handle exception
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
}
