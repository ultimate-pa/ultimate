/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubtermPropertyChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheck.TraceCheckLock;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.ConstantTermNormalizer;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Class for the computation of nested interpolants and tree interpolants.
 * <br />
 * TODO 2024-10-06 Matthias: We do not really need a class that can be
 * instantiated for the current computation. If I would have more time, I would
 * consider the following options.
 * <li>Do all computations in static methods.
 * <li>Use a class hierarchy to split the computation of nested interpolants and
 * tree interpolants. (I have doubts that this is possible.)
 */
public class NestedInterpolantsBuilder<L extends IAction> {

	private static final int SKIPPED_POSITION_FOR_RECURSIVE_COMPUATION = -47;
	// TODO 2017-10-13 Matthias: When Jochen implement support for "@diff" this
	// probably has to become a parameter for this class.
	private static final boolean ALLOW_AT_DIFF = SolverBuilder.USE_DIFF_WRAPPER_SCRIPT;
	public static final String DIFF_IS_UNSUPPORTED = "@diff is unsupported";

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final boolean mInstantiateArrayExt;
	private final ManagedScript mMgdScriptCfg;
	private final IPredicateUnifier mPredicateUnifier;
	private final BasicPredicateFactory mPredicateFactory;

	private final Set<Integer> mSkippedInnerProcedurePositions;

	private final Function<Term, Term> mConst2RepTvSubst;
	private final int[] mPositionMapping;
	private final Term[] mCraigInterpolants;

	private final IPredicate[] mInterpolants;

	public NestedInterpolantsBuilder(final ManagedScript mgdScriptTc, final TraceCheckLock scriptLockOwner,
			final NestedFormulas<L, Term, Term> annotatdSsa, final Map<Term, IProgramVar> constants2BoogieVar,
			final IPredicateUnifier predicateBuilder, final BasicPredicateFactory predicateFactory,
			final Set<Integer> skippedInnerProcedurePositions, final boolean treeInterpolation,
			final IUltimateServiceProvider services, final TraceCheck<L> traceCheck, final ManagedScript mgdScriptCfg,
			final boolean instantiateArrayExt, final SimplificationTechnique simplificationTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(TraceCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mMgdScriptCfg = mgdScriptCfg;
		mPredicateUnifier = predicateBuilder;
		mPredicateFactory = predicateFactory;
		mSkippedInnerProcedurePositions = skippedInnerProcedurePositions;

		mInstantiateArrayExt = instantiateArrayExt;
		final HashMap<Term, Term> const2RepTv = new HashMap<>();
		for (final Entry<Term, IProgramVar> entry : constants2BoogieVar.entrySet()) {
			const2RepTv.put(entry.getKey(), entry.getValue().getTermVariable());
		}
		if (mgdScriptTc != mgdScriptCfg) {
			mConst2RepTvSubst = (x -> new TermTransferrer(mgdScriptTc.getScript(), mMgdScriptCfg.getScript(),
					const2RepTv, true).transform(x));
		} else {
			mConst2RepTvSubst = (x -> Substitution.apply(mMgdScriptCfg, const2RepTv, x));
		}

		final Triple<Term[], int[], int[]> triple = generateInterpolationInput(mgdScriptTc, annotatdSsa,
				mSkippedInnerProcedurePositions);
		final Term[] interpolInput = triple.getFirst();
		final int[] startOfSubtree = triple.getSecond();
		final int[] positionMapping = triple.getThird();
		mPositionMapping = positionMapping;

		if (treeInterpolation) {
			mCraigInterpolants = mgdScriptTc.getInterpolants(scriptLockOwner, interpolInput, startOfSubtree);
		} else {
			mCraigInterpolants = mgdScriptTc.getInterpolants(scriptLockOwner, interpolInput);
		}

		traceCheck.cleanupAndUnlockSolver();
		for (int i = 0; i < mCraigInterpolants.length; i++) {
			mLogger.debug(new DebugMessage("NestedInterpolant {0}: {1}", i, mCraigInterpolants[i]));
		}
		mInterpolants = buildPredicates();
		assert mInterpolants != null;
		// if (mPref.dumpFormulas()) {
		// dumpNestedStateFormulas(mInterpolants, mTrace, mIterationPW);
	}

	private static <L extends IAction> Triple<Term[], int[], int[]> generateInterpolationInput(
			final ManagedScript mgdScriptTc, final NestedFormulas<L, Term, Term> annotSsa,
			final Set<Integer> skippedInnerProcedurePositions) {
		final NestedWord<L> trace = annotSsa.getTrace();

		final List<Term> interpolInputList = new ArrayList<>();
		final List<Integer> treeInterpolantStructure = new ArrayList<>();
		final int[] positionMapping = new int[trace.length() - 1];

		int startOfCurrentSubtree = 0;
		final Deque<Integer> mStartOfSubtreeStack = new ArrayDeque<>();

		for (int i = 0; i < annotSsa.getTrace().length(); i++) {
			final List<Term> terms;
			if (trace.isInternalPosition(i)) {
				terms = getAnnotatedFormulasForInternalPosition(annotSsa, i);
			} else if (trace.isCallPosition(i)) {
				if (!trace.isPendingCall(i)) {
					final int nextPosition = interpolInputList.size();
					mStartOfSubtreeStack.push(startOfCurrentSubtree);
					startOfCurrentSubtree = nextPosition;
					terms = getAnnotatedFormulasForNonPendingCallPosition(annotSsa, i);
				} else {
					terms = getAnnotatedFormulasForPendingCallPosition(annotSsa, i);
				}
			} else if (trace.isReturnPosition(i)) {
				if (trace.isPendingReturn(i)) {
					terms = getAnnotatedFormulasForPendingReturnPosition(annotSsa, i);
				} else {
					startOfCurrentSubtree = mStartOfSubtreeStack.pop();
					final int correspondingCallPosition = trace.getCallPosition(i);
					terms = getAnnotatedFormulasForNonPendingReturnPosition(annotSsa, i, correspondingCallPosition);
				}
			} else {
				throw new AssertionError("Each position must be either internal, call, or return");
			}
			final Term term = SmtUtils.and(mgdScriptTc.getScript(), terms);
			// Check whether the last position (position i-1) is a position where we want to
			// compute interpolants. If not we do not want to start a new interpolation
			// input formulas afterwards but append the current annotated ssa term(s) to the
			// last interpolation input.
			final boolean startNewFormula = (i == 0 || !skippedInnerProcedurePositions.contains(i - 1));
			if (startNewFormula) {
				if (i > 0) {
					positionMapping[i - 1] = interpolInputList.size() - 1;
				}
				interpolInputList.add(term);
				treeInterpolantStructure.add(startOfCurrentSubtree);
			} else {
				if (i > 0) {
					positionMapping[i - 1] = SKIPPED_POSITION_FOR_RECURSIVE_COMPUATION;
				}
				final int lastPosition = interpolInputList.size() - 1;
				final Term newFormula = SmtUtils.and(mgdScriptTc.getScript(), interpolInputList.get(lastPosition),
						term);
				assert newFormula != null : "newFormula must be != null";
				interpolInputList.set(lastPosition, newFormula);
			}
		}

		final Term[] interpolInput = interpolInputList.toArray(new Term[interpolInputList.size()]);
		// add precondition to first term
		// special case: if first position is non pending call, then we add the
		// precondition to the corresponding return.
		if (trace.isCallPosition(0) && !trace.isPendingCall(0)) {
			final int correspondingReturn = trace.getReturnPosition(0);
			// if we do not interpolate at each position
			// interpolInput[correspondingReturn] might be the wrong position
			int interpolInputPositionOfReturn = 0;
			for (int i = 0; i < correspondingReturn; i++) {
				if (!skippedInnerProcedurePositions.contains(i)) {
					interpolInputPositionOfReturn++;
				}
			}
			interpolInput[interpolInputPositionOfReturn] = SmtUtils.and(mgdScriptTc.getScript(),
					interpolInput[interpolInputPositionOfReturn], annotSsa.getPrecondition());
		} else {
			interpolInput[0] = SmtUtils.and(mgdScriptTc.getScript(), interpolInput[0], annotSsa.getPrecondition());
		}

		// add negated postcondition to last term
		interpolInput[interpolInput.length - 1] = SmtUtils.and(mgdScriptTc.getScript(),
				interpolInput[interpolInput.length - 1], annotSsa.getPostcondition());

		final int[] startOfSubtree = integerListToIntArray(treeInterpolantStructure);
		return new Triple<Term[], int[], int[]>(interpolInput, startOfSubtree, positionMapping);
	}

	private static <L extends IAction> List<Term> getAnnotatedFormulasForInternalPosition(
			final NestedFormulas<L, Term, Term> annotSSA, final int i) {
		final Term internalTransition = annotSSA.getFormulaFromNonCallPos(i);
		if (internalTransition != null) {
			return Collections.singletonList(internalTransition);
		} else {
			return Collections.emptyList();
		}
	}

	private static <L extends IAction> List<Term> getAnnotatedFormulasForNonPendingCallPosition(
			final NestedFormulas<L, Term, Term> annotSSA, final int i) {
		final Term globalVarAssignment = annotSSA.getGlobalVarAssignment(i);
		if (globalVarAssignment != null) {
			return Collections.singletonList(globalVarAssignment);
		} else {
			return Collections.emptyList();
		}
	}

	private static <L extends IAction> List<Term> getAnnotatedFormulasForPendingCallPosition(
			final NestedFormulas<L, Term, Term> annotSSA, final int i) {
		final List<Term> result = new ArrayList<>();
		final Term localVarsAssignment = annotSSA.getLocalVarAssignment(i);
		if (localVarsAssignment != null) {
			result.add(localVarsAssignment);
		}
		final Term globalVarsAssignment = annotSSA.getGlobalVarAssignment(i);
		if (globalVarsAssignment != null) {
			result.add(globalVarsAssignment);
		}
		final Term oldVarsAssignment = annotSSA.getOldVarAssignment(i);
		if (oldVarsAssignment != null) {
			result.add(oldVarsAssignment);
		}
		return result;
	}

	private static <L extends IAction> List<Term> getAnnotatedFormulasForNonPendingReturnPosition(
			final NestedFormulas<L, Term, Term> annotSSA, final int i, final int correspondingCallPosition) {
		final List<Term> result = new ArrayList<>();
		final Term assignmentOnReturn = annotSSA.getFormulaFromNonCallPos(i);
		if (assignmentOnReturn != null) {
			result.add(assignmentOnReturn);
		}
		final Term localVarsAssignment = annotSSA.getLocalVarAssignment(correspondingCallPosition);
		if (localVarsAssignment != null) {
			result.add(localVarsAssignment);
		}
		final Term oldVarsAssignment = annotSSA.getOldVarAssignment(correspondingCallPosition);
		if (oldVarsAssignment != null) {
			result.add(oldVarsAssignment);
		}
		return result;
	}

	private static <L extends IAction> List<Term> getAnnotatedFormulasForPendingReturnPosition(
			final NestedFormulas<L, Term, Term> annotSSA, final int i) {
		final List<Term> result = new ArrayList<>();
		final Term assignmentOnReturn = annotSSA.getFormulaFromNonCallPos(i);
		if (assignmentOnReturn != null) {
			result.add(assignmentOnReturn);
		}
		final Term localVarsAssignment = annotSSA.getLocalVarAssignment(i);
		if (localVarsAssignment != null) {
			result.add(localVarsAssignment);
		}
		final Term oldVarsAssignment = annotSSA.getOldVarAssignment(i);
		if (oldVarsAssignment != null) {
			result.add(oldVarsAssignment);
		}
		final Term pendingContext = annotSSA.getPendingContext(i);
		if (pendingContext != null) {
			result.add(pendingContext);
		}
		return result;
	}

	private static int[] integerListToIntArray(final List<Integer> integerList) {
		final int[] result = new int[integerList.size()];
		for (int i = 0; i < integerList.size(); i++) {
			result[i] = integerList.get(i);
		}
		return result;
	}

	public IPredicate[] getNestedInterpolants() {
		for (int j = 0; j < mInterpolants.length; j++) {
			mLogger.debug(new DebugMessage("Interpolant {0}: {1}", j, mInterpolants[j]));
		}
		return mInterpolants;
	}

	private IPredicate[] buildPredicates() {
		final IPredicate[] result = new IPredicate[mPositionMapping.length];
		final Map<Term, IPredicate> withIndices2Predicate = new HashMap<>();

		for (int i = 0; i < mPositionMapping.length; i++) {
			final int craigInterpolPos = mPositionMapping[i];

			final IPredicate pred;
			if (craigInterpolPos == SKIPPED_POSITION_FOR_RECURSIVE_COMPUATION) {
				assert mSkippedInnerProcedurePositions.contains(i);
				pred = mPredicateFactory.newDontCarePredicate(null);
			} else {
				final Term withIndices = mCraigInterpolants[craigInterpolPos];
				final IPredicate cachedResult = withIndices2Predicate.get(withIndices);
				if (cachedResult != null) {
					pred = cachedResult;
				} else {
					final Term postprocessed = postprocessInterpolant(withIndices);
					pred = mPredicateUnifier.getOrConstructPredicate(postprocessed);
					withIndices2Predicate.put(withIndices, pred);
				}
			}
			result[i] = pred;
		}
		return result;
	}

	/**
	 * Apply various processing steps and (seemingly) translate terms to the script
	 * of the CFG. <br />
	 * TODO 2024-10-06 Matthias:
	 * <li>Check if all postprocessing steps are needed (remove iZ3 support?)
	 * <li>Check if quantifier elimination should really be done here (is it done
	 * twice in the overall trace check?)
	 */
	private Term postprocessInterpolant(final Term withIndices) {
		/*
		 * remove all let terms added because iZ3's interpolants contain let terms
		 * better solution: implement support for let terms in SafeSubstitution
		 */
		final Term unlet = new FormulaUnLet().transform(withIndices);
		Term withoutIndices = mConst2RepTvSubst.apply(unlet);
		if (mInstantiateArrayExt) {
			withoutIndices = instantiateArrayExt(withoutIndices);
		}
		if (!ALLOW_AT_DIFF
				&& new SubtermPropertyChecker(x -> isAtDiffTerm(x)).isSatisfiedBySomeSubterm(withoutIndices)) {
			throw new UnsupportedOperationException(DIFF_IS_UNSUPPORTED);
		}
		final Term withoutIndicesNormalized = new ConstantTermNormalizer().transform(withoutIndices);
		final Term lessQuantifiers = PartialQuantifierElimination.eliminate(mServices, mMgdScriptCfg,
				withoutIndicesNormalized, mSimplificationTechnique);
		return lessQuantifiers;
	}

	/**
	 * TODO 2024-10-06 Matthias: Timeout checks here are probably useless. However
	 * we should catch timeouts thrown by time-consuming methods and append our
	 * message from below.
	 */
	private void checkTimeout() {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(this.getClass(),
					"constructing predicates for " + (mPositionMapping.length - 1) + " interpolants");
		}
	}

	/**
	 * The interpolating Z3 generates Craig interpolants that contain the array-ext
	 * function whose semantics is defined by the following axiom ∀a∀b∃k.
	 * array-ext(a,b)=k <--> (a=b \/ a[k] != b[k]). The theory of arrays does not
	 * contain this axiom, hence we instantiate it for each occurrence.
	 */
	private Term instantiateArrayExt(final Term interpolantWithoutIndices) {
		final Term nnf = new NnfTransformer(mMgdScriptCfg, mServices, QuantifierHandling.PULL)
				.transform(interpolantWithoutIndices);
		// not needed, at the moment our NNF transformation also produces
		// Term prenex = (new PrenexNormalForm(mCsToolkitPredicates.getScript(),
		// mCsToolkitPredicates.getVariableManager())).transform(nnf);
		final QuantifierSequence qs = new QuantifierSequence(mMgdScriptCfg, nnf);
		// The quantifier-free part of of formula in prenex normal form is called
		// matrix
		final Term matrix = qs.getInnerTerm();

		final Set<ApplicationTerm> arrayExtAppTerms = SmtUtils.extractApplicationTerms("array-ext",
				interpolantWithoutIndices, false);
		if (arrayExtAppTerms.isEmpty()) {
			return interpolantWithoutIndices;
		}
		final Term[] implications = new Term[arrayExtAppTerms.size()];
		final TermVariable[] replacingTermVariable = new TermVariable[arrayExtAppTerms.size()];
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		int offset = 0;
		for (final ApplicationTerm appTerm : arrayExtAppTerms) {
			final ArrayExtTerm aet = new ArrayExtTerm(appTerm);
			replacingTermVariable[offset] = aet.getReplacementTermVariable();
			implications[offset] = aet.getImplication();
			substitutionMapping.put(aet.getArrayExtTerm(), aet.getReplacementTermVariable());
			offset++;
		}
		Term result = Substitution.apply(mMgdScriptCfg, substitutionMapping, matrix);
		result = SmtUtils.and(mMgdScriptCfg.getScript(), result, SmtUtils.and(mMgdScriptCfg.getScript(), implications));
		result = mMgdScriptCfg.getScript().quantifier(QuantifiedFormula.EXISTS, replacingTermVariable, result);
		result = QuantifierSequence.prependQuantifierSequence(mMgdScriptCfg.getScript(), qs.getQuantifierBlocks(),
				result);
		// Term pushed = new QuantifierPusher(mCsToolkitPredicates.getScript(),
		// mServices).transform(result);
		return result;
	}

	private class ArrayExtTerm {
		private final ApplicationTerm mArrayExtTerm;
		private final Term mFirstArray;
		private final Term mSecondArray;
		private final TermVariable mReplacementTermVariable;
		private final Term mImplication;

		public ArrayExtTerm(final ApplicationTerm arrayExtTerm) {
			mArrayExtTerm = arrayExtTerm;
			if (!mArrayExtTerm.getFunction().getName().equals("array-ext")) {
				throw new IllegalArgumentException("no array-ext Term");
			}
			if (mArrayExtTerm.getParameters().length != 2) {
				throw new IllegalArgumentException("expected two params");
			}
			mFirstArray = mArrayExtTerm.getParameters()[0];
			mSecondArray = mArrayExtTerm.getParameters()[1];
			mReplacementTermVariable = arrayExtTerm.getTheory().createFreshTermVariable("arrExt",
					arrayExtTerm.getSort());
			mImplication = constructImplication();
		}

		private Term constructImplication() {
			final Term arraysDistinct = mMgdScriptCfg.getScript().term("distinct", mFirstArray, mSecondArray);
			final Term firstSelect = SmtUtils.select(mMgdScriptCfg.getScript(), mFirstArray, mReplacementTermVariable);
			final Term secondSelect = SmtUtils.select(mMgdScriptCfg.getScript(), mSecondArray,
					mReplacementTermVariable);
			final Term selectDistinct = mMgdScriptCfg.getScript().term("distinct", firstSelect, secondSelect);
			final Term implication = Util.implies(mMgdScriptCfg.getScript(), arraysDistinct, selectDistinct);
			return implication;
		}

		public ApplicationTerm getArrayExtTerm() {
			return mArrayExtTerm;
		}

		public Term getFirstArray() {
			return mFirstArray;
		}

		public Term getSecondArray() {
			return mSecondArray;
		}

		public TermVariable getReplacementTermVariable() {
			return mReplacementTermVariable;
		}

		public Term getImplication() {
			return mImplication;
		}

	}

	private static void dumpInterpolationInput(final int offset, final Term[] interpolInput,
			final List<Integer> indexTranslation, final NestedRun<?, IPredicate> run, final Script theory,
			final PrintWriter pW, final ILogger logger) {
		String line;
		int indentation = 0;
		int translatedPosition;
		final FormulaUnLet unflet = new FormulaUnLet();
		try {
			line = "==Interpolation Input";
			logger.debug(line);
			pW.println(line);
			for (int j = 0; j < interpolInput.length; j++) {
				if (j == 0) {
					translatedPosition = offset;
				} else {
					translatedPosition = indexTranslation.get(j - 1);
				}
				line = CoreUtil.addIndentation(indentation, "Location " + translatedPosition + ": "
						+ ((SPredicate) run.getStateAtPosition(translatedPosition)).getProgramPoint());
				logger.debug(line);
				pW.println(line);
				if (run.isCallPosition(translatedPosition)) {
					indentation++;
				}
				line = CoreUtil.addIndentation(indentation, unflet.unlet(interpolInput[j]).toString());
				logger.debug(line);
				pW.println(line);
				if (run.isReturnPosition(translatedPosition)) {
					indentation--;
				}
			}
			if (offset != 0) {
				final int returnSuccPos = run.getWord().getReturnPosition(offset) + 1;
				line = CoreUtil.addIndentation(indentation, "Location " + returnSuccPos + ": "
						+ ((SPredicate) run.getStateAtPosition(returnSuccPos)).getProgramPoint());
				logger.debug(line);
				pW.println(line);
			}
			pW.println("");
			pW.println("");
		} finally {
			pW.flush();
		}
	}

	private static void dumpInterpolationOutput(final int offset, final Term[] interpolOutput,
			final List<Integer> indexTranslation, final Word<?> run, final PrintWriter pW, final ILogger logger) {
		final NestedWord<?> word = NestedWord.nestedWord(run);
		assert interpolOutput.length == indexTranslation.size();
		String line;
		int indentation = 0;
		int translatedPosition;
		try {
			line = "==Interpolation Output";
			logger.debug(line);
			pW.println(line);
			for (int j = 0; j < interpolOutput.length; j++) {
				translatedPosition = indexTranslation.get(j);
				if (translatedPosition > 1 && word.isCallPosition(translatedPosition - 1)) {
					indentation++;
				}
				line = CoreUtil.addIndentation(indentation,
						"InterpolOutput" + translatedPosition + ": " + interpolOutput[j]);
				logger.debug(line);
				pW.println(line);
				if (word.isReturnPosition(translatedPosition)) {
					indentation--;
				}
			}
			pW.println("");
			pW.println("");
		} finally {
			pW.flush();
		}
	}

	private static void dumpNestedStateFormulas(final IPredicate[] stateFormulas, final Word<?> word,
			final PrintWriter pW, final ILogger logger) {
		final NestedWord<?> nw = NestedWord.nestedWord(word);
		assert stateFormulas.length == word.length() + 1;
		String line;
		int indentation = 0;
		try {
			line = "==NestedInterpolants";
			logger.debug(line);
			pW.println(line);
			for (int j = 0; j < stateFormulas.length; j++) {
				line = CoreUtil.addIndentation(indentation, j + ": " + stateFormulas[j]);
				logger.debug(line);
				pW.println(line);
				if (j != stateFormulas.length - 1) {
					pW.println(word.getSymbol(j));
					if (nw.isCallPosition(j)) {
						indentation++;
					}
					if (nw.isReturnPosition(j)) {
						indentation--;
					}
				}
			}
		} finally {
			pW.flush();
		}
	}

	private static boolean isAtDiffTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("@diff");
		}
		return false;
	}

}
