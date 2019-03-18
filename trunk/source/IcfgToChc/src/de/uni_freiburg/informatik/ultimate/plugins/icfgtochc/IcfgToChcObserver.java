/*
 * Copyright (C) 2019 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.ChcCategoryInfo;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcBodyAuxVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcBodyVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClauseAST;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermClassifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;

/**
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class IcfgToChcObserver implements IUnmanagedObserver {

	private static final String ASSERTIONVIOLATEDVARNAME = "V";
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private IElement mResult;

	private ManagedScript mMgdScript;
	private HcSymbolTable mHcSymbolTable;
	private IIcfg<IcfgLocation> mIcfg;

	private final Map<String, List<IProgramVar>> mProcToVarList;

	private TermVariable mAssertionViolatedVar;
	private final Map<TermVariable, IProgramVar> mTermVarToProgVar;
	private boolean mHasNonLinearClauses;

	// TODO setting
	// private final boolean ANNOTATE_ASSERTED_TERMS = true;

	public IcfgToChcObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;

		mProcToVarList = new LinkedHashMap<>();

		mTermVarToProgVar = new LinkedHashMap<>();
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// no initialization needed
	}

	@Override
	public void finish() throws Throwable {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	public IElement getModel() {
		return mResult;
	}

	@Override
	public boolean process(final IElement root) throws Exception {
		if (root instanceof IIcfg) {
			processIcfg((IIcfg<?>) root);
			return false;
		}
		return true;
	}

	@SuppressWarnings("unchecked")
	private <LOC extends IcfgLocation> void processIcfg(final IIcfg<LOC> icfg) {

		/* set up fields that need something from the icfg */
		mMgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		mHcSymbolTable = new HcSymbolTable(mMgdScript);
		mIcfg = (IIcfg<IcfgLocation>) icfg;

		mMgdScript.lock(this);

		mAssertionViolatedVar =
				mMgdScript.constructFreshTermVariable(ASSERTIONVIOLATEDVARNAME, SmtSortUtils.getBoolSort(mMgdScript));

		/* compute resulting chc set */

		/* add chcs for the icfg's edges */

		final Collection<HornClause> resultChcs = new ArrayList<>();
		final IcfgEdgeIterator edgeIt = new IcfgEdgeIterator(mIcfg);

		while (edgeIt.hasNext()) {
			final IcfgEdge currentEdge = edgeIt.next();

			if (currentEdge instanceof IIcfgInternalTransition<?>) {
				if (currentEdge instanceof IIcfgSummaryTransition<?>) {
					final IIcfgSummaryTransition<IcfgLocation> summary =
							(IIcfgSummaryTransition<IcfgLocation>) currentEdge;
					if (summary.calledProcedureHasImplementation()) {
						// nothing to do
					} else {
						// no implementation; treat summary like internal edge
						final Collection<HornClause> chcs =
								computeChcForInternalEdge((IIcfgInternalTransition<IcfgLocation>) currentEdge);
						chcs.forEach(chc -> chc.setComment("Type: internal"));
						resultChcs.addAll(chcs);
					}
				} else {
					// normal (non-summary) edge
					final Collection<HornClause> chcs;
					if (isErrorLocation(currentEdge.getTarget())) {
						chcs = computeChcForInternalErrorEdge((IIcfgInternalTransition<IcfgLocation>) currentEdge);
						chcs.forEach(chc -> chc.setComment("Type: assert edge"));
					} else {
						chcs = computeChcForInternalEdge((IIcfgInternalTransition<IcfgLocation>) currentEdge);
						chcs.forEach(chc -> chc.setComment("Type: internal"));
					}
					resultChcs.addAll(chcs);
				}
			} else if (currentEdge instanceof IIcfgCallTransition<?>) {
				// nothing to do for a call edge
			} else if (currentEdge instanceof IIcfgReturnTransition<?, ?>) {
				final Collection<HornClause> chcs =
						computeChcForReturnEdge((IIcfgReturnTransition<IcfgLocation, Call>) currentEdge);
				chcs.forEach(chc -> chc.setComment("Type: return edge"));
				resultChcs.addAll(chcs);
			} else {
				throw new AssertionError("unforseen edge type (not internal, call, or return");
			}
		}

		/* add chcs for entry and exit points */
		computeClausesForEntryPoints(icfg, resultChcs);

		computeClausesForExitPoints(icfg, resultChcs);

		/* finish construction */

		mHcSymbolTable.finishConstruction();

		mMgdScript.unlock(this);

		final ChcCategoryInfo chcCategoryInfo = computeChcCategoryInfo(resultChcs);

		assert resultChcs.stream().allMatch(chc -> chc.constructFormula(mMgdScript, false).getFreeVars().length == 0);

		final HornAnnot annot =
				new HornAnnot(mIcfg.getIdentifier(), mMgdScript, mHcSymbolTable, new ArrayList<>(resultChcs), true,
						chcCategoryInfo);


		mResult = HornClauseAST.create(annot);
		ModelUtils.copyAnnotations(mIcfg, mResult);

	}

	private ChcCategoryInfo computeChcCategoryInfo(final Collection<HornClause> resultChcs) {
		final ChcCategoryInfo chcCategoryInfo;
		{
			final TermClassifier termClassifierChcs = new TermClassifier();
			resultChcs.forEach(chc -> termClassifierChcs.checkTerm(chc.constructFormula(mMgdScript, false)));
			final TermClassifier termClassifierConstraints = new TermClassifier();
			resultChcs.forEach(chc -> termClassifierConstraints.checkTerm(chc.getConstraintFormula()));

			boolean hasArrays = false;
			boolean hasReals = false;
			boolean hasInts = false;
			for (final String osn : termClassifierChcs.getOccuringSortNames()) {
				hasArrays |= osn.contains(SmtSortUtils.ARRAY_SORT);
				hasReals |= osn.contains(SmtSortUtils.REAL_SORT);
				hasInts |= osn.contains(SmtSortUtils.INT_SORT);
			}

			boolean hasArraysInConstraints = false;
			boolean hasRealsInConstraints = false;
			boolean hasIntsInConstraints = false;
			for (final String osn : termClassifierConstraints.getOccuringSortNames()) {
				hasArraysInConstraints |= osn.contains(SmtSortUtils.ARRAY_SORT);
				hasRealsInConstraints |= osn.contains(SmtSortUtils.REAL_SORT);
				hasIntsInConstraints |= osn.contains(SmtSortUtils.INT_SORT);
			}
			assert hasArrays == hasArraysInConstraints;
			assert hasReals == hasRealsInConstraints;
			assert hasInts == hasIntsInConstraints;

			boolean hasQuantifiersInConstraints = false;
			if (termClassifierConstraints.getOccuringQuantifiers().size() > 0) {
				hasQuantifiersInConstraints = true;
			}

			Logics logics;

			if (!hasArrays && hasInts && !hasReals && !hasQuantifiersInConstraints) {
				logics = Logics.QF_LIA;
			} else if (!hasArrays && !hasInts && hasReals && !hasQuantifiersInConstraints) {
				logics = Logics.QF_LRA;
			} else if (hasArrays && hasInts && !hasReals && !hasQuantifiersInConstraints) {
				logics = Logics.QF_ALIA;
			} else {
				// not a CHC-comp 2019 logic -- we don't care for more details right now
				logics = Logics.ALL;
			}

			chcCategoryInfo = new ChcCategoryInfo(logics, mHasNonLinearClauses);
		}
		return chcCategoryInfo;
	}

	private <LOC extends IcfgLocation> void computeClausesForEntryPoints(final IIcfg<LOC> icfg,
			final Collection<HornClause> resultChcs) {
		/*
		 * every procedure entry point gets a chc of the form (not V') /\ old(g1) = g1 /\ ... -> entryPoint
		 */
		for (final Entry<String, LOC> en : icfg.getProcedureEntryNodes().entrySet()) {

			final String proc = en.getKey();

			final HcPredicateSymbol headPred = getOrConstructPredicateSymbolForIcfgLocation(en.getValue());

			final Map<Term, Term> substitutionMapping = new LinkedHashMap<>();

			// look for V
			// look for globals
			HcHeadVar assertionViolatedHeadVar = null;
			final List<HcHeadVar> headVars = new ArrayList<>();
			final List<Term> globalsWithTheirOldVarsEqualities = new ArrayList<>();
			{
				final List<TermVariable> varsForProc = getTermVariableListForPredForProcedure(proc);
				for (int i = 0; i < varsForProc.size(); i++) {
					final TermVariable tv = varsForProc.get(i);
					final IProgramVar pv = mTermVarToProgVar.get(tv);
					final HcHeadVar headVar = getPrettyHeadVar(headPred, i, tv.getSort(), pv);
					headVars.add(headVar);
					if (tv.equals(mAssertionViolatedVar)) {
						assertionViolatedHeadVar = headVar;
					} else if (pv.isGlobal()) {

						// add equality var = old(var)
						if (!pv.isOldvar()) {
							if (!mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable()
									.getModifiedBoogieVars(proc).contains(pv)) {
								// not modified --> skip
								continue;
							}
							globalsWithTheirOldVarsEqualities.add(SmtUtils.binaryEquality(mMgdScript.getScript(),
									pv.getTermVariable(), ((IProgramNonOldVar) pv).getOldVar().getTermVariable()));
							substitutionMapping.put(pv.getTermVariable(), headVar.getTermVariable());
						} else if (pv.isOldvar()) {
							if (!mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable()
									.getModifiedBoogieVars(proc).contains(((IProgramOldVar) pv).getNonOldVar())) {
								// not modified --> skip
								continue;
							}

							substitutionMapping.put(pv.getTermVariable(), headVar.getTermVariable());
						}
					}
				}
			}

			final Term equateGlobalsWithTheirOldVars = SmtUtils.and(mMgdScript.getScript(),
					globalsWithTheirOldVarsEqualities.toArray(new Term[globalsWithTheirOldVarsEqualities.size()]));

			final Term constraintRaw = SmtUtils.and(mMgdScript.getScript(),
					SmtUtils.not(mMgdScript.getScript(), assertionViolatedHeadVar.getTermVariable()),
					equateGlobalsWithTheirOldVars);
			final Term constraintFinal = new Substitution(mMgdScript, substitutionMapping).transform(constraintRaw);

			updateLogicWrtConstraint(constraintFinal);

			if (!assertNoFreeVars(headVars, Collections.emptySet(), constraintFinal)) {
				throw new UnsupportedOperationException("implement this");
			}

			final HornClause chc = new HornClause(mMgdScript, mHcSymbolTable, constraintFinal, headPred, headVars,
					Collections.emptyList(), Collections.emptyList(), Collections.emptySet());
			chc.setComment("Type: (not V) -> procEntry");
			resultChcs.add(chc);
		}
	}

	private <LOC extends IcfgLocation> void computeClausesForExitPoints(final IIcfg<LOC> icfg,
			final Collection<HornClause> resultChcs) {
		/*
		 * every exit point of a procedure that is an entry point of the program gets a chc exit /\ V -> false
		 */
		for (final Entry<String, LOC> en : icfg.getProcedureExitNodes().entrySet()) {
			final String correspondingProc = en.getKey();
			final LOC correspondingEntryNode = icfg.getProcedureEntryNodes().get(correspondingProc);
			if (!icfg.getInitialNodes().contains(correspondingEntryNode)) {
				// correspondingProc is not an entry point procedure
				continue;
			}

			final HcPredicateSymbol bodyPred = getOrConstructPredicateSymbolForIcfgLocation(en.getValue());

			final List<TermVariable> varsForProc = getTermVariableListForPredForProcedure(en.getKey());

			final Set<HcVar> bodyVars = new LinkedHashSet<>();
			final List<Term> firstPredArgs = new ArrayList<>();
			HcBodyVar assertionViolatedBodyVar = null;
			for (int i = 0; i < varsForProc.size(); i++) {
				final TermVariable tv = varsForProc.get(i);
				final HcBodyVar bodyVar = getPrettyBodyVar(bodyPred, i, tv.getSort(), mTermVarToProgVar.get(tv));
				bodyVars.add(bodyVar);
				firstPredArgs.add(bodyVar.getTerm());
				if (tv.equals(mAssertionViolatedVar)) {
					assertionViolatedBodyVar = bodyVar;
				}
			}

			final TermVariable constraint = assertionViolatedBodyVar.getTermVariable();

			updateLogicWrtConstraint(constraint);

			if (!assertNoFreeVars(Collections.emptyList(), bodyVars, constraint)) {
				throw new UnsupportedOperationException("implement this");
			}

			final HornClause chc =
					new HornClause(mMgdScript, mHcSymbolTable, constraint,
							Collections.singletonList(bodyPred), Collections.singletonList(firstPredArgs), bodyVars);

			chc.setComment("Type: entryProcExit(..., V) /\\ V -> false");
			resultChcs.add(chc);

		}
	}

	private Collection<HornClause> computeChcForReturnEdge(final IIcfgReturnTransition<IcfgLocation, Call> returnEdge) {

		/* fields necessary for building the horn clause */

		final UnmodifiableTransFormula assignmentOfReturn = returnEdge.getAssignmentOfReturn();
		final UnmodifiableTransFormula localVarsAssignmentOfCall = returnEdge.getLocalVarsAssignmentOfCall();
		final UnmodifiableTransFormula oldVarsAssignment = mIcfg.getCfgSmtToolkit().getOldVarsAssignmentCache()
				.getOldVarsAssignment(returnEdge.getPrecedingProcedure());

		final List<TermVariable> varsForInnerProc =
				getTermVariableListForPredForProcedure(returnEdge.getPrecedingProcedure());
		final List<TermVariable> varsForOuterProc =
				getTermVariableListForPredForProcedure(returnEdge.getSucceedingProcedure());

		if (isErrorLocation(returnEdge.getTarget())) {
			throw new AssertionError("return edge whose target is an error location -- that is unexpected");
		}
		if (mIcfg.getInitialNodes().contains(returnEdge.getSource())) {
			throw new AssertionError("source of a return edge is an initial location -- that is unexpected");
		}
		// if (mIcfg.getInitialNodes().contains(returnEdge.getCallerProgramPoint())) {
		// throw new UnsupportedOperationException("case not yet implemented");
		// }

		final Map<Term, Term> substitutionForAssignmentOfReturn = new LinkedHashMap<>();
		final Map<Term, Term> substitutionForAssignmentOfCall = new LinkedHashMap<>();
		final Map<Term, Term> substitutionForOldVarsAssignment = new LinkedHashMap<>();

		/*
		 * Deal with Atom in the head - assignments come from assignmentOfReturn - take over unassigned locals from
		 * before-call location - take over unassigned globals from before-return location
		 */
		final HcPredicateSymbol headPred = getOrConstructPredicateSymbolForIcfgLocation(returnEdge.getTarget());
		final List<HcHeadVar> headVars;
		HcHeadVar headAssertionViolatedVar = null;
		headVars = new ArrayList<>();
		{
			for (int i = 0; i < varsForOuterProc.size(); i++) {
				final TermVariable tv = varsForOuterProc.get(i);
				final IProgramVarOrConst pv = mTermVarToProgVar.get(tv);
				// TransFormulaUtils.getProgramVarForTerm(tf, tv);
				// final IProgramVar pv = varsForOuterProc.get(i);

				final HcHeadVar headVar = getPrettyHeadVar(headPred, i, tv.getSort(), pv);
				headVars.add(headVar);

				if (tv.equals(mAssertionViolatedVar)) {
					// nothing
					headAssertionViolatedVar = headVar;
				} else if (pv.isGlobal()) {
					// nothing
				} else {
					// pv is local
					/*
					 * if the parameters don't change (only the one assigned by the call may change), they will be
					 * reused in the before-call predicate and thus need to be updated in the parameter assignment
					 */
					final TermVariable outTv = assignmentOfReturn.getOutVars().get(pv);
					if (outTv == null) {
						// nothing
					} else {
						substitutionForAssignmentOfReturn.put(outTv, headVar.getTermVariable());
					}
				}
			}
		}

		final List<HcPredicateSymbol> bodyPreds;
		final List<List<Term>> bodyPredToArguments;
		final Set<HcVar> bodyVars;
		HcBodyVar firstBodyPredAssertionViolatedVar = null;
		HcBodyVar secondBodyPredAssertionViolatedVar = null;

		{
			/*
			 * convention: - 1st predicate represents before call location - 2nd predicate represents before return
			 * location
			 */
			bodyPreds = new ArrayList<>();
			bodyPreds.add(getOrConstructPredicateSymbolForIcfgLocation(returnEdge.getCallerProgramPoint()));
			bodyPreds.add(getOrConstructPredicateSymbolForIcfgLocation(returnEdge.getSource()));

			bodyVars = new LinkedHashSet<>();
			{
				final List<Term> firstPredArgs = new ArrayList<>();

				for (int i = 0; i < varsForOuterProc.size(); i++) {
					final TermVariable tv = varsForOuterProc.get(i);
					final IProgramVarOrConst pv = mTermVarToProgVar.get(tv);

					final HcBodyVar bodyVar = getPrettyBodyVar(bodyPreds.get(0), i, tv.getSort(), pv);
					bodyVars.add(bodyVar);

					if (tv.equals(mAssertionViolatedVar)) {
						// nothing
						firstPredArgs.add(bodyVar.getTermVariable());
						firstBodyPredAssertionViolatedVar = bodyVar;
					} else if (pv.isGlobal()) {
						if (mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable()
								.getModifiedBoogieVars(returnEdge.getPrecedingProcedure()).contains(pv)) {
							// pv is global and modified by the procedure
							firstPredArgs.add(bodyVar.getTermVariable());

							final TermVariable inTv = oldVarsAssignment.getInVars().get(pv);
							assert inTv != null;
							substitutionForOldVarsAssignment.put(inTv, bodyVar.getTermVariable());

							final TermVariable inTvCallAssignment = localVarsAssignmentOfCall.getInVars().get(pv);
							if (inTvCallAssignment == null) {
								// nothing
							} else {
								substitutionForAssignmentOfCall.put(inTvCallAssignment, bodyVar.getTermVariable());
							}

						} else {
							// pv is global and not modified by procedure --> use variable from headvars as arg
							// maybe not obvious: this should work because the predicates after the return and before
							// the call have the same signature (both belong to the outer procedure)
							firstPredArgs.add(headVars.get(i).getTermVariable());

							final TermVariable inTv = localVarsAssignmentOfCall.getInVars().get(pv);
							if (inTv == null) {
								// nothing
							} else {
								substitutionForAssignmentOfCall.put(inTv, headVars.get(i).getTermVariable());
							}
						}
					} else {
						/*
						 * pv is local --> if it is assigned by the return, it is new, otherwise we take the one from
						 * the clause head
						 */
						if (assignmentOfReturn.getAssignedVars().contains(pv)) {
							firstPredArgs.add(bodyVar.getTermVariable());
						} else {
							firstPredArgs.add(headVars.get(i).getTermVariable());
						}

						final TermVariable inTv = localVarsAssignmentOfCall.getInVars().get(pv);
						if (inTv == null) {
							// nothing
						} else {
							substitutionForAssignmentOfCall.put(inTv, headVars.get(i).getTermVariable());
						}

					}
				}

				final List<Term> secondPredArgs = new ArrayList<>();

				for (int i = 0; i < varsForInnerProc.size(); i++) {
					final TermVariable tv = varsForInnerProc.get(i);
					final IProgramVar pv = mTermVarToProgVar.get(tv);

					final HcBodyVar bodyVar = getPrettyBodyVar(bodyPreds.get(1), i, tv.getSort(), pv);
					bodyVars.add(bodyVar);

					if (tv.equals(mAssertionViolatedVar)) {
						// nothing
						secondPredArgs.add(bodyVar.getTermVariable());
						secondBodyPredAssertionViolatedVar = bodyVar;
					} else if (pv.isGlobal()) {
						if (pv.isOldvar()) {
							secondPredArgs.add(bodyVar.getTermVariable());

							final TermVariable outTv = oldVarsAssignment.getOutVars().get(pv);
							assert outTv != null;
							substitutionForOldVarsAssignment.put(outTv, bodyVar.getTermVariable());
						} else {
							// find the right head var and use it..

							final int headVarPosInOuterProcPred = varsForOuterProc.indexOf(pv.getTermVariable());
							final HcHeadVar headVarCorrespondingToPv = headVars.get(headVarPosInOuterProcPred);

							secondPredArgs.add(headVarCorrespondingToPv.getTermVariable());
						}
					} else {
						// pv is local

						final TermVariable inParamTv = localVarsAssignmentOfCall.getOutVars().get(pv);
						final TermVariable outParamTv = assignmentOfReturn.getInVars().get(pv);
						if (inParamTv == null && outParamTv == null) {
							// not an inParam
							secondPredArgs.add(bodyVar.getTermVariable());
						} else if (inParamTv != null && outParamTv == null) {
							// pv is an inParam
							secondPredArgs.add(bodyVar.getTermVariable());
							substitutionForAssignmentOfCall.put(inParamTv, bodyVar.getTermVariable());
						} else if (inParamTv == null && outParamTv != null) {
							// pv is an outParam
							secondPredArgs.add(bodyVar.getTermVariable());
							substitutionForAssignmentOfReturn.put(outParamTv, bodyVar.getTermVariable());
						} else {
							// pv is an inParam and an outParam --> can this happen?
							throw new AssertionError();
						}
					}
				}

				bodyPredToArguments = new ArrayList<>();
				bodyPredToArguments.add(firstPredArgs);
				bodyPredToArguments.add(secondPredArgs);
			}
		}

		for (final TermVariable auxVar : localVarsAssignmentOfCall.getAuxVars()) {
			final HcBodyAuxVar hcbav = mHcSymbolTable.getOrConstructBodyAuxVar(auxVar, this);
			bodyVars.add(hcbav);
		}
		for (final TermVariable auxVar : assignmentOfReturn.getAuxVars()) {
			final HcBodyAuxVar hcbav = mHcSymbolTable.getOrConstructBodyAuxVar(auxVar, this);
			bodyVars.add(hcbav);
		}
		for (final TermVariable auxVar : oldVarsAssignment.getAuxVars()) {
			final HcBodyAuxVar hcbav = mHcSymbolTable.getOrConstructBodyAuxVar(auxVar, this);
			bodyVars.add(hcbav);
		}

		final Term updateAssertionViolatedVar =
				SmtUtils.binaryBooleanEquality(mMgdScript.getScript(), headAssertionViolatedVar.getTermVariable(),
						SmtUtils.or(mMgdScript.getScript(), firstBodyPredAssertionViolatedVar.getTermVariable(),
								secondBodyPredAssertionViolatedVar.getTermVariable()));

		final Term constraint = SmtUtils.and(mMgdScript.getScript(),
				new Substitution(mMgdScript, substitutionForAssignmentOfCall)
						.transform(localVarsAssignmentOfCall.getFormula()),
				new Substitution(mMgdScript, substitutionForAssignmentOfReturn)
						.transform(assignmentOfReturn.getFormula()),
				new Substitution(mMgdScript, substitutionForOldVarsAssignment)
						.transform(oldVarsAssignment.getFormula()),
				updateAssertionViolatedVar);

		if (!assertNoFreeVars(headVars, bodyVars, constraint)) {
			throw new UnsupportedOperationException("implement this");
		}

		final Term constraintFinal = constraint;

		updateLogicWrtConstraint(constraintFinal);

		mHasNonLinearClauses = true;

		/* construct the horn clause and add it to the resulting chc set */
		final Collection<HornClause> chcs = new ArrayList<>();
		chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraintFinal, headPred, headVars, bodyPreds,
				bodyPredToArguments, bodyVars));
		return chcs;
	}

	@Deprecated
	private void updateLogicWrtConstraint(final Term term) {
//		mTermClassifier.checkTerm(term);
	}

	private boolean assertNoFreeVars(final List<HcHeadVar> headVars, final Set<HcVar> bodyVars,
			final Term constraint) {
		// compute all variables that only occur in the
		final Set<TermVariable> auxVars = new LinkedHashSet<>();
		auxVars.addAll(Arrays.asList(constraint.getFreeVars()));

		if (headVars != null) {
			auxVars.removeAll(headVars.stream().map(hv -> hv.getTermVariable()).collect(Collectors.toList()));
		}

		auxVars.removeAll(bodyVars.stream().map(bv -> bv.getTermVariable()).collect(Collectors.toList()));

		auxVars.remove(mAssertionViolatedVar);

		if (!auxVars.isEmpty()) {
			assert false;
			return false;
		}
		return true;
	}

	/**
	 * instead of going to the error location, shortcut to procedure exit, if the assertion is violated set the
	 * assertion-violated variable, too
	 *
	 * @param currentInternalEdge
	 * @return
	 */
	private Collection<HornClause>
			computeChcForInternalErrorEdge(final IIcfgInternalTransition<IcfgLocation> currentInternalEdge) {

		final UnmodifiableTransFormula tf = currentInternalEdge.getTransformula();
		final String proc = currentInternalEdge.getPrecedingProcedure();

		final List<TermVariable> varsForProc = getTermVariableListForPredForProcedure(proc);

		final Map<Term, Term> substitutionMapping = new LinkedHashMap<>();

		final HcPredicateSymbol headPred =
				getOrConstructPredicateSymbolForIcfgLocation(mIcfg.getProcedureExitNodes().get(proc));
		final List<HcHeadVar> headVars = new ArrayList<>();
		HcHeadVar assertionViolatedHeadVar = null;
		for (int i = 0; i < varsForProc.size(); i++) {
			final TermVariable tv = varsForProc.get(i);
			final IProgramVarOrConst pv = mTermVarToProgVar.get(tv);

			final HcHeadVar headVar = getPrettyHeadVar(headPred, i, tv.getSort(), pv);
			headVars.add(headVar);

			if (tv == mAssertionViolatedVar) {
				assertionViolatedHeadVar = headVar;
				continue;
			}

			final TermVariable outTv = tf.getOutVars().get(pv);
			if (outTv == null) {
				// pv is not an out var of tf
			} else {
				/*
				 * pv is an out var of tf --> the headvar must connect to the corresponding variable in the constraint
				 */
				substitutionMapping.put(outTv, headVar.getTermVariable());
			}
		}

		HcBodyVar assertionViolatedBodyVar = null;

		final List<HcPredicateSymbol> bodyPreds;
		final List<List<Term>> bodyPredToArguments;
		final Set<HcVar> bodyVars;

		bodyPreds = Collections
				.singletonList(getOrConstructPredicateSymbolForIcfgLocation(currentInternalEdge.getSource()));
		bodyVars = new LinkedHashSet<>();
		{
			final List<Term> firstPredArgs = new ArrayList<>();

			for (int i = 0; i < varsForProc.size(); i++) {
				final TermVariable tv = varsForProc.get(i);

				final HcBodyVar bodyVar =
						getPrettyBodyVar(bodyPreds.get(0), i, tv.getSort(), mTermVarToProgVar.get(tv));
				bodyVars.add(bodyVar);

				if (tv == mAssertionViolatedVar) {
					firstPredArgs.add(bodyVar.getTermVariable());
					assertionViolatedBodyVar = bodyVar;
					continue;
				}

				final IProgramVarOrConst pv = mTermVarToProgVar.get(tv);
				assert pv != null;

				final TermVariable inTv = tf.getInVars().get(pv);
				final TermVariable outTv = tf.getOutVars().get(pv);
				if (inTv == null && outTv == null) {
					// pv is neither in nor out --> the transformula leaves it unchanged--> in and out must match..
					firstPredArgs.add(headVars.get(i).getTermVariable());
				} else if (inTv == null && outTv != null) {
					// pv is not an in var of tf but is an outvar --> var in body is disconnected
					firstPredArgs.add(bodyVar.getTermVariable());
				} else if (inTv != null && outTv == null) {
					// pv is an in var of tf but is not an outvar --> connect to formula
					firstPredArgs.add(bodyVar.getTermVariable());
					substitutionMapping.put(inTv, bodyVar.getTermVariable());
				} else {
					// inTv != null && outTv != null
					/*
					 * pv is an in var of tf --> the headvar must connect to the corresponding variable in the
					 * constraint
					 */
					if (inTv == outTv) {
						// "assume" case --> substitution already exists, use var from head (if a head exists)
						firstPredArgs.add(headVars.get(i).getTermVariable());
					} else {
						// "assign" case --> other var for body, substitute that "unprimed" version, primed
						// version is already in substitution
						assert substitutionMapping.containsKey(outTv) : "subs should have been added during head "
								+ "processing";
						firstPredArgs.add(bodyVar.getTermVariable());
						substitutionMapping.put(inTv, bodyVar.getTermVariable());
					}
				}
			}
			bodyPredToArguments = Collections.singletonList(firstPredArgs);
		}

		for (final TermVariable auxVar : tf.getAuxVars()) {
			final HcBodyAuxVar hcbav = mHcSymbolTable.getOrConstructBodyAuxVar(auxVar, this);
			bodyVars.add(hcbav);
		}

		final Term constraintAndAssertionViolated = SmtUtils.and(mMgdScript.getScript(),
				new Substitution(mMgdScript, substitutionMapping).transform(tf.getFormula()),
				assertionViolatedHeadVar.getTermVariable());

		final Term constraintFinal = constraintAndAssertionViolated;

		assert assertNoFreeVars(headVars, bodyVars, constraintFinal);

		updateLogicWrtConstraint(constraintFinal);

		final Collection<HornClause> chcs = new ArrayList<>();
		chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraintFinal, headPred, headVars, bodyPreds,
				bodyPredToArguments, bodyVars));

		return chcs;
	}

	/**
	 *
	 * Returns one or two chcs (two iff the source of the edge is initial)
	 *
	 * @param currentInternalEdge
	 * @return
	 */
	private Collection<HornClause>
			computeChcForInternalEdge(final IIcfgInternalTransition<IcfgLocation> currentInternalEdge) {
		assert !isErrorLocation(currentInternalEdge.getTarget()) : "use other method for that";

		// target is not an error location

		/* fields necessary for building the horn clause */

		final UnmodifiableTransFormula tf = currentInternalEdge.getTransformula();
		final String proc = currentInternalEdge.getPrecedingProcedure();

		final List<TermVariable> varsForProc = getTermVariableListForPredForProcedure(proc);

		final Map<Term, Term> substitutionMapping = new LinkedHashMap<>();

		final HcPredicateSymbol headPred =
				getOrConstructPredicateSymbolForIcfgLocation(currentInternalEdge.getTarget());
		final List<HcHeadVar> headVars = new ArrayList<>();
		HcHeadVar assertionViolatedHeadVar = null;
		for (int i = 0; i < varsForProc.size(); i++) {
			final TermVariable tv = varsForProc.get(i);
			final IProgramVarOrConst pv = mTermVarToProgVar.get(tv);

			final HcHeadVar headVar = getPrettyHeadVar(headPred, i, tv.getSort(), pv);
			headVars.add(headVar);

			if (tv.equals(mAssertionViolatedVar)) {
				assertionViolatedHeadVar = headVar;
				continue;
			}

			final TermVariable outTv = tf.getOutVars().get(pv);
			if (outTv == null) {
				// pv is not an out var of tf
			} else {
				/*
				 * pv is an out var of tf --> the headvar must connect to the corresponding variable in the constraint
				 */
				substitutionMapping.put(outTv, headVar.getTermVariable());
			}
		}

		final List<HcPredicateSymbol> bodyPreds;
		final List<List<Term>> bodyPredToArguments;
		final Set<HcVar> bodyVars;

		// HcBodyVar assertionViolatedBodyVar = null;

		bodyPreds = Collections
				.singletonList(getOrConstructPredicateSymbolForIcfgLocation(currentInternalEdge.getSource()));
		bodyVars = new LinkedHashSet<>();
		{
			final List<Term> firstPredArgs = new ArrayList<>();

			for (int i = 0; i < varsForProc.size(); i++) {
				final TermVariable tv = varsForProc.get(i);

				final IProgramVarOrConst pv = mTermVarToProgVar.get(tv);

				final HcBodyVar bodyVar = getPrettyBodyVar(bodyPreds.get(0), i, tv.getSort(), pv);
				bodyVars.add(bodyVar);

				if (tv.equals(mAssertionViolatedVar)) {
					firstPredArgs.add(assertionViolatedHeadVar.getTermVariable());
					// assertionViolatedBodyVar = bodyVar;
					continue;
				}

				final TermVariable inTv = tf.getInVars().get(pv);
				final TermVariable outTv = tf.getOutVars().get(pv);
				if (inTv == null && outTv == null) {
					// pv is neither in nor out --> the transformula leaves it unchanged--> in and out must match..
					firstPredArgs.add(headVars.get(i).getTermVariable());
				} else if (inTv == null && outTv != null) {
					// pv is not an in var of tf but is an outvar --> var in body is disconnected
					firstPredArgs.add(bodyVar.getTermVariable());
				} else if (inTv != null && outTv == null) {
					// pv is an in var of tf but is not an outvar --> connect to formula
					firstPredArgs.add(bodyVar.getTermVariable());
					substitutionMapping.put(inTv, bodyVar.getTermVariable());
				} else {
					// inTv != null && outTv != null
					/*
					 * pv is an in var of tf --> the headvar must connect to the corresponding variable in the
					 * constraint
					 */
					if (inTv == outTv) {
						// "assume" case --> substitution already exists, use var from head (if a head exists)
						firstPredArgs.add(headVars.get(i).getTermVariable());
					} else {
						// "assign" case --> other var for body, substitute that "unprimed" version, primed
						// version is already in substitution
						assert substitutionMapping.containsKey(outTv) : "subs should have been added during head "
								+ "processing";
						firstPredArgs.add(bodyVar.getTermVariable());
						substitutionMapping.put(inTv, bodyVar.getTermVariable());
					}
				}
			}
			bodyPredToArguments = Collections.singletonList(firstPredArgs);
		}

		for (final TermVariable auxVar : tf.getAuxVars()) {
			final HcBodyAuxVar hcbav = mHcSymbolTable.getOrConstructBodyAuxVar(auxVar, this);
			bodyVars.add(hcbav);
		}

		final Term constraintOrAssertionViolated;
		{
			final Term constraint = new Substitution(mMgdScript, substitutionMapping).transform(tf.getFormula());
			constraintOrAssertionViolated =
					SmtUtils.or(mMgdScript.getScript(), assertionViolatedHeadVar.getTermVariable(), constraint);
		}


		assert assertNoFreeVars(headVars, bodyVars, constraintOrAssertionViolated);

		final Term constraintFinal = constraintOrAssertionViolated;

		/*
		 * construct the horn clause and add it to the resulting chc set if the source is an initial location, add two
		 * versions of the clause, in one of them, leave out the body predicates, the other as normal
		 */
		updateLogicWrtConstraint(constraintFinal);
		final Collection<HornClause> chcs = new ArrayList<>(2);
		chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraintFinal, headPred, headVars, bodyPreds,
				bodyPredToArguments, bodyVars));
		return chcs;
	}

	private HcHeadVar getPrettyHeadVar(final HcPredicateSymbol headPred, final int i, final Sort sort,
			final IProgramVarOrConst pv) {
		mMgdScript.unlock(this); // TODO not nice
		final HcHeadVar res = mHcSymbolTable.getOrConstructHeadVar(headPred, i, sort);
		mMgdScript.lock(this);
		final String comment = pv != null ? pv.toString() + "'" : ASSERTIONVIOLATEDVARNAME + "'";
		res.setComment(comment);
		return res;
	}

	private HcBodyVar getPrettyBodyVar(final HcPredicateSymbol bodyPred, final int i, final Sort sort,
			final IProgramVarOrConst pv) {
		mMgdScript.unlock(this); // TODO not nice
		final HcBodyVar res = mHcSymbolTable.getOrConstructBodyVar(bodyPred, i, sort);
		mMgdScript.lock(this);
		final String comment = pv != null ? pv.toString() : ASSERTIONVIOLATEDVARNAME;
		res.setComment(comment);
		return res;
	}

	private boolean isErrorLocation(final IcfgLocation loc) {
		final Set<IcfgLocation> errorNodes = mIcfg.getProcedureErrorNodes().get(loc.getProcedure());
		if (errorNodes == null) {
			return false;
		}
		return errorNodes.contains(loc);
	}

	private HcPredicateSymbol getOrConstructPredicateSymbolForIcfgLocation(final IcfgLocation loc) {
		assert mHcSymbolTable != null : "hcSymboltable not yet set up; this method can only be used inside processIcfg";
		final String name = computePredicateNameForIcfgLocation(loc);
		final List<Sort> sorts = computeSortsForIcfgLocationPredicate(loc);
		return mHcSymbolTable.getOrConstructHornClausePredicateSymbol(name, sorts);
	}

	/**
	 * Returns the sorts of the arguments of a predicate that we create for an {@link IcfgLocation}.
	 *
	 * The arguments of such a predicate are determined by the program variables in the Icfg. They are composed of the
	 * modifiable global variables and the local variables of the procedure the location {@link loc} belongs to.
	 *
	 *
	 * @param loc
	 * @return
	 */
	private List<Sort> computeSortsForIcfgLocationPredicate(final IcfgLocation loc) {
		final List<TermVariable> variables = getTermVariableListForPredForProcedure(loc.getProcedure());
		return variables.stream().map(tv -> tv.getSort()).collect(Collectors.toList());
	}

	private List<TermVariable> getTermVariableListForPredForProcedure(final String procedure) {
		final List<TermVariable> result = new ArrayList<>();
		for (final IProgramVar pv : getProgramVariableListForProcedure(procedure)) {
			mTermVarToProgVar.put(pv.getTermVariable(), pv);
			result.add(pv.getTermVariable());
		}
		result.add(mAssertionViolatedVar);
		return Collections.unmodifiableList(result);
	}

	/**
	 * Return the list of variables that belongs to the given procedure.
	 *
	 * Note that the order the variables have in this list is not canonical; To avoid having different variables lists
	 * for the same procedure, this method computes the list only once and caches it for later uses.
	 *
	 * @param procedure
	 * @return
	 */
	private List<IProgramVar> getProgramVariableListForProcedure(final String procedure) {
		List<IProgramVar> result = mProcToVarList.get(procedure);
		if (result == null) {
			final Set<IProgramNonOldVar> allGlobals = mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
			final Set<IProgramNonOldVar> modGlobalVars =
					mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(procedure);
			final Set<ILocalProgramVar> localVars = mIcfg.getCfgSmtToolkit().getSymbolTable().getLocals(procedure);
			result = new ArrayList<>();
			for (final IProgramNonOldVar gv : allGlobals) {
				result.add(gv);
				if (modGlobalVars.contains(gv)) {
					result.add(gv.getOldVar());
				}
			}
			result.addAll(localVars);
			mProcToVarList.put(procedure, Collections.unmodifiableList(result));
		}

		return result;
	}

	private String computePredicateNameForIcfgLocation(final IcfgLocation loc) {
		return loc.getProcedure() + "_" + loc.toString();
	}

}
