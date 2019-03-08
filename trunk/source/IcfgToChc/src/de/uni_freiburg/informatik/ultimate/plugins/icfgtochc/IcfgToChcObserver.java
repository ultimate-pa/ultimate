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
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcBodyVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClauseAST;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;

/**
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class IcfgToChcObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private IElement mResult;

	private ManagedScript mMgdScript;
	private HcSymbolTable mHcSymbolTable;
	private IIcfg<IcfgLocation> mIcfg;

	private final Map<String, List<IProgramVar>> mProcToVarList;

	public IcfgToChcObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;

		mProcToVarList = new LinkedHashMap<>();
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
	private <INLOC extends IcfgLocation> void processIcfg(final IIcfg<INLOC> icfg) {

		/* set up fields that need something from the icfg */
		mMgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		mHcSymbolTable = new HcSymbolTable(mMgdScript);
		mIcfg = (IIcfg<IcfgLocation>) icfg;

		/* compute resulting chc set, iterating over the icfg's edges */

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
						// no implementation treat summary like internal edge
						final Collection<HornClause> chcs =
							computeChcForInternalEdge((IIcfgInternalTransition<IcfgLocation>) currentEdge);
						resultChcs.addAll(chcs);
					}
				} else {
					// normal (non-summary) edge
					final Collection<HornClause> chcs =
							computeChcForInternalEdge((IIcfgInternalTransition<IcfgLocation>) currentEdge);
					resultChcs.addAll(chcs);
				}
			} else if (currentEdge instanceof IIcfgCallTransition<?>) {
				// nothing to do for a call edge
			} else if (currentEdge instanceof IIcfgReturnTransition<?, ?>) {
				resultChcs.addAll(computeChcForReturnEdge((IIcfgReturnTransition<IcfgLocation, Call>) currentEdge));
			} else {
				throw new AssertionError("unforseen edge type (not internal, call, or return");
			}
		}

		/* finish construction */

		mHcSymbolTable.finishConstruction();

		final Payload payload = new Payload();
		final HornAnnot annot = new HornAnnot(mIcfg.getIdentifier(), mMgdScript, mHcSymbolTable,
				new ArrayList<>(resultChcs), true);
		payload.getAnnotations().put(HornUtilConstants.HORN_ANNOT_NAME, annot);

		mResult = new HornClauseAST(payload);
	}

	private Collection<HornClause> computeChcForReturnEdge(final IIcfgReturnTransition<IcfgLocation, Call> returnEdge) {

		/*  fields necessary for building the horn clause */

		final UnmodifiableTransFormula assignmentOfReturn = returnEdge.getAssignmentOfReturn();
		final UnmodifiableTransFormula localVarsAssignmentOfCall = returnEdge.getLocalVarsAssignmentOfCall();
		final UnmodifiableTransFormula oldVarsAssignment = mIcfg.getCfgSmtToolkit().getOldVarsAssignmentCache()
				.getOldVarsAssignment(returnEdge.getPrecedingProcedure());

		final List<IProgramVar> varsForInnerProc =
					getVariableListForProcedure(returnEdge.getPrecedingProcedure());
		final List<IProgramVar> varsForOuterProc =
					getVariableListForProcedure(returnEdge.getSucceedingProcedure());

		final boolean isTargetErrorLocation = isErrorLocation(returnEdge.getTarget());

		if (mIcfg.getInitialNodes().contains(returnEdge.getSource())) {
			throw new AssertionError("source of a return edge is an initial location -- that is unexpected");
		}
		final boolean isCallerSourceInitialLocation =
				mIcfg.getInitialNodes().contains(returnEdge.getCallerProgramPoint());
		if (mIcfg.getInitialNodes().contains(returnEdge.getSource())) {
			throw new UnsupportedOperationException("case not yet implemented");
		}

		final Map<Term, Term> substitutionForAssignmentOfReturn = new LinkedHashMap<>();
		final Map<Term, Term> substitutionForAssignmentOfCall = new LinkedHashMap<>();
		final Map<Term, Term> substitutionForOldVarsAssignment = new LinkedHashMap<>();

		/*
		 * Deal with Atom in the head
		 *  - assignments come from assignmentOfReturn
		 *  - take over unassigned locals from before-call location
		 *  - take over unassigned globals from before-return location
		 */
		final HcPredicateSymbol headPred = computeHeadPred(returnEdge, isTargetErrorLocation);
		final List<HcHeadVar> headVars;
		if (isTargetErrorLocation) {
			headVars = null;
		} else {
			headVars = new ArrayList<>();
			{
				for (int i = 0; i < varsForOuterProc.size(); i++) {
					final IProgramVar pv = varsForOuterProc.get(i);

					final HcHeadVar headVar =
							mHcSymbolTable.getOrConstructHeadVar(headPred, i, pv.getSort());
					headVars.add(headVar);

					if (pv.isGlobal()) {
						// nothing
					} else {
						// pv is local
						/* if the parameters don't change (only the one assigned by the call may change), they will be
						 * reused in the before-call predicate and thus need to be updated in the parameter assignment
						 */
						final TermVariable outTv = assignmentOfReturn.getOutVars().get(pv);
						if (outTv == null) {
							// nothing
						} else {
							substitutionForAssignmentOfReturn.put(outTv, headVar.getTermVariable());
						}

//						final TermVariable inTv = localVarsAssignmentOfCall.getInVars().get(pv);
//						if (inTv == null) {
//							// nothing
//						} else {
//							substitutionForAssignmentOfCall.put(inTv, headVar.getTermVariable());
//						}
					}
				}
			}
		}


		final List<HcPredicateSymbol> bodyPreds;
		final List<List<Term>> bodyPredToArguments;
		final Set<HcBodyVar> bodyVars;

		{
			/* convention:
			 * - 1st predicate represents before call location
			 * - 2nd predicate represents before return location */
			bodyPreds = new ArrayList<>();
			bodyPreds.add(getOrConstructPredicateSymbolForIcfgLocation(returnEdge.getCallerProgramPoint()));
			bodyPreds.add(getOrConstructPredicateSymbolForIcfgLocation(returnEdge.getSource()));

			bodyVars = new LinkedHashSet<>();
			{
				final List<Term> firstPredArgs = new ArrayList<>();

				for (int i = 0; i < varsForOuterProc.size(); i++) {
					final IProgramVar pv = varsForOuterProc.get(i);

					final HcBodyVar bodyVar =
							mHcSymbolTable.getOrConstructBodyVar(bodyPreds.get(0), i, pv.getSort());
					bodyVars.add(bodyVar);


					if (pv.isGlobal()) {
						if (mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable()
								.getModifiedBoogieVars(returnEdge.getPrecedingProcedure()).contains(pv)) {
							// pv is global and modified by the procedure
							firstPredArgs.add(bodyVar.getTermVariable());

							final TermVariable inTv = oldVarsAssignment.getInVars().get(pv);
							assert inTv != null;
							substitutionForOldVarsAssignment.put(inTv, bodyVar.getTermVariable());
						} else {
							// pv is global and not modified by procedure --> use variable from headvars as arg
							// maybe not obvious: this should work because the predicates after the return and before
							// the call have the same signature (both belong to the outer procedure)
							firstPredArgs.add(headVars.get(i).getTermVariable());
						}
					} else {
						/* pv is local --> if it is assigned by the return, it is new, otherwise we take the one from the
						 * clause head */
						if (assignmentOfReturn.getAssignedVars().contains(pv)) {
							firstPredArgs.add(bodyVar.getTermVariable());
//							final TermVariable outTv = assignmentOfReturn.getOutVars().get(pv);
//							substitutionForAssignmentOfReturn.put(outTv, bodyVar.getTermVariable());
						} else {
							firstPredArgs.add(headVars.get(i).getTermVariable());
						}


//						final TermVariable outTv = assignmentOfReturn.getOutVars().get(pv);
//						if (outTv == null) {
//							firstPredArgs.add(headVars.get(i).getTermVariable());
//						} else {
//							assert assignmentOfReturn.getAssignedVars().contains(pv);
//							firstPredArgs.add(bodyVar.getTermVariable());
//							substitutionForAssignmentOfReturn.put(outTv, bodyVar.getTermVariable());
//						}

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
					final IProgramVar pv = varsForInnerProc.get(i);

					final HcBodyVar bodyVar =
							mHcSymbolTable.getOrConstructBodyVar(bodyPreds.get(1), i, pv.getSort());
					bodyVars.add(bodyVar);


					if (pv.isGlobal()) {
						if (pv.isOldvar()) {
							secondPredArgs.add(bodyVar.getTermVariable());

							final TermVariable outTv = oldVarsAssignment.getOutVars().get(pv);
							assert outTv != null;
							substitutionForOldVarsAssignment.put(outTv, bodyVar.getTermVariable());
						} else {
							// find the right head var and use it..

							final int headVarPosInOuterProcPred = varsForOuterProc.indexOf(pv);
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

		final Term constraint = SmtUtils.and(mMgdScript.getScript(),
				new Substitution(mMgdScript, substitutionForAssignmentOfCall)
					.transform(localVarsAssignmentOfCall.getFormula()),
				new Substitution(mMgdScript, substitutionForAssignmentOfReturn)
					.transform(assignmentOfReturn.getFormula()),
				new Substitution(mMgdScript, substitutionForOldVarsAssignment)
					.transform(oldVarsAssignment.getFormula())
							);

//		assert assertNoFreeVars(headVars, bodyVars, constraint);
		if (!assertNoFreeVars(headVars, bodyVars, constraint)) {
			throw new UnsupportedOperationException("implement this");
		}


		/* construct the horn clause and add it to the resulting chc set */
		final Collection<HornClause> chcs = new ArrayList<>();
		if (isTargetErrorLocation) {
			chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, bodyPreds,
					bodyPredToArguments, bodyVars));
			if (isCallerSourceInitialLocation) {
				final List<HcPredicateSymbol> bodyPredsOnlySecond = Collections.singletonList(bodyPreds.get(1));
				final List<List<Term>> bodyPredToArgumentsOnlySecond =
						Collections.singletonList(bodyPredToArguments.get(1));
				chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, bodyPredsOnlySecond,
					bodyPredToArgumentsOnlySecond, bodyVars));
			}
		} else {
			chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, headPred, headVars, bodyPreds,
					bodyPredToArguments, bodyVars));
			if (isCallerSourceInitialLocation) {
				final List<HcPredicateSymbol> bodyPredsOnlySecond = Collections.singletonList(bodyPreds.get(1));
				final List<List<Term>> bodyPredToArgumentsOnlySecond =
						Collections.singletonList(bodyPredToArguments.get(1));
				chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, headPred, headVars, bodyPredsOnlySecond,
					bodyPredToArgumentsOnlySecond, bodyVars));
			}
		}
		return chcs;
	}

	private boolean assertNoFreeVars(final List<HcHeadVar> headVars, final Set<HcBodyVar> bodyVars,
			final Term constraint) {
		// compute all variables that only occur in the
		final Set<TermVariable> auxVars = new LinkedHashSet<>();
		auxVars.addAll(Arrays.asList(constraint.getFreeVars()));
		if (headVars != null) {
			auxVars.removeAll(headVars.stream().map(hv -> hv.getTermVariable()).collect(Collectors.toList()));
		}
		auxVars.removeAll(bodyVars.stream().map(bv -> bv.getTermVariable()).collect(Collectors.toList()));
		if (!auxVars.isEmpty()) {
			assert false;
			return false;
		}
		return true;
	}

	/**
	 *
	 * Returns one or two chcs (two iff the source of the edge is initial)
	 *
	 * @param currentInternalEdge
	 * @return
	 */
	private Collection<HornClause> computeChcForInternalEdge(
			final IIcfgInternalTransition<IcfgLocation> currentInternalEdge) {
		/*  fields necessary for building the horn clause */

		final UnmodifiableTransFormula tf = currentInternalEdge.getTransformula();
		final List<IProgramVar> varsForProc =
					getVariableListForProcedure(currentInternalEdge.getPrecedingProcedure());


		final boolean isTargetErrorLocation = isErrorLocation(currentInternalEdge.getTarget());
		final boolean isSourceInitialLocation = mIcfg.getInitialNodes().contains(currentInternalEdge.getSource());

		final Map<Term, Term> substitutionMapping = new LinkedHashMap<>();

		final HcPredicateSymbol headPred = computeHeadPred(currentInternalEdge, isTargetErrorLocation);
		final List<HcHeadVar> headVars = computeHeadVarsUpdateSubsitution(tf, varsForProc,
				isTargetErrorLocation, headPred, substitutionMapping);



		final List<HcPredicateSymbol> bodyPreds;
		final List<List<Term>> bodyPredToArguments;
		final Set<HcBodyVar> bodyVars;

		bodyPreds = Collections.singletonList(
				getOrConstructPredicateSymbolForIcfgLocation(currentInternalEdge.getSource()));
		bodyVars = new LinkedHashSet<>();
		{
			final List<Term> firstPredArgs = new ArrayList<>();

			for (int i = 0; i < varsForProc.size(); i++) {
				final IProgramVar pv = varsForProc.get(i);

				final HcBodyVar bodyVar =
						mHcSymbolTable.getOrConstructBodyVar(bodyPreds.get(0), i,
								pv.getSort());
				bodyVars.add(bodyVar);

				final TermVariable inTv = tf.getInVars().get(pv);
				final TermVariable outTv = tf.getOutVars().get(pv);
				if (inTv == null && outTv == null) {
					// pv is neither in nor out --> the transformula leaves it unchanged--> in and out must match..
					if (isTargetErrorLocation) {
						/* .. except if there is no out, because the target is "false", then it does not matter
						 * which term we use here */
						firstPredArgs.add(bodyVar.getTermVariable());
					} else {
						firstPredArgs.add(headVars.get(i).getTermVariable());
					}
				} else if (inTv == null && outTv != null) {
					// pv is not an in var of tf but is an outvar --> var in body is disconnected
					firstPredArgs.add(bodyVar.getTermVariable());
					//						substitutionMapping.put(outTv, bodyVar.getTermVariable());
				} else if (inTv != null && outTv == null) {
					// pv is an in var of tf but is not an outvar --> connect to formula
					firstPredArgs.add(bodyVar.getTermVariable());
					substitutionMapping.put(inTv, bodyVar.getTermVariable());
				} else {
					// inTv != null && outTv != null
					/* pv is an in var of tf --> the headvar must connect to the corresponding variable in
					 * the constraint */
					if (inTv == outTv) {
						// "assume" case --> substitution already exists, use var from head (if a head exists)
						if (isTargetErrorLocation) {
							firstPredArgs.add(bodyVar.getTermVariable());
							substitutionMapping.put(inTv, bodyVar.getTermVariable());
						} else {
							firstPredArgs.add(headVars.get(i).getTermVariable());
						}
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

		final Term constraint = new Substitution(mMgdScript, substitutionMapping).transform(tf.getFormula());

		assert assertNoFreeVars(headVars, bodyVars, constraint);

		/* construct the horn clause and add it to the resulting chc set
		 *  if the source is an initial location, add two versions of the clause, in one of them, leave out the body
		 *  predicates, the other as normal */
		final Collection<HornClause> chcs = new ArrayList<>(2);
		if (isSourceInitialLocation && isTargetErrorLocation) {
			chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, Collections.emptyList(),
					Collections.emptyList(), bodyVars));
			chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, bodyPreds,
					bodyPredToArguments, bodyVars));
		} else if (!isSourceInitialLocation && isTargetErrorLocation) {
			chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, bodyPreds,
					bodyPredToArguments, bodyVars));
		} else if (isSourceInitialLocation && !isTargetErrorLocation) {
			chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, headPred, headVars, Collections.emptyList(),
					Collections.emptyList(), bodyVars));
			chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, headPred, headVars, bodyPreds,
					bodyPredToArguments, bodyVars));
		} else {
			// !isSourceInitialLocation && !isTargetErrorLocation
			chcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, headPred, headVars, bodyPreds,
					bodyPredToArguments, bodyVars));
		}
		return chcs;
	}

	private boolean isErrorLocation(final IcfgLocation loc) {
		final Set<IcfgLocation> errorNodes = mIcfg.getProcedureErrorNodes().get(loc.getProcedure());
		if (errorNodes == null) {
			return false;
		}
		return errorNodes.contains(loc);
	}

	private List<HcHeadVar> computeHeadVarsUpdateSubsitution(final UnmodifiableTransFormula tf,
			final List<IProgramVar> varsForProc, final boolean isTargetErrorLocation, final HcPredicateSymbol headPred,
			final Map<Term, Term> substitutionMapping) {
		final List<HcHeadVar> headVars;
		if (isTargetErrorLocation) {
			headVars = null;
		} else {
			headVars = new ArrayList<>();
			{
				for (int i = 0; i < varsForProc.size(); i++) {

					final HcHeadVar headVar =
							mHcSymbolTable.getOrConstructHeadVar(headPred, i, varsForProc.get(i).getSort());
					headVars.add(headVar);

					final TermVariable outTv = tf.getOutVars().get(varsForProc.get(i));
					if (outTv == null) {
						// pv is not an out var of tf
					} else {
						/* pv is an out var of tf --> the headvar must connect to the corresponding variable in
						 * the constraint */
						substitutionMapping.put(outTv, headVar.getTermVariable());
					}
				}
			}
		}
		return headVars;
	}

	private HcPredicateSymbol computeHeadPred(final IIcfgTransition<?> currentEdge,
			final boolean isTargetErrorLocation) {
		final HcPredicateSymbol headPred;
		if (isTargetErrorLocation) {
			headPred = null;
		} else {
			headPred = getOrConstructPredicateSymbolForIcfgLocation(currentEdge.getTarget());
		}
		return headPred;
	}

	private HcPredicateSymbol getOrConstructPredicateSymbolForIcfgLocation(final IcfgLocation loc) {
		assert mHcSymbolTable != null : "hcSymboltable not yet set up; this method can only be used inside processIcfg";
		return mHcSymbolTable.getOrConstructHornClausePredicateSymbol(computePredicateNameForIcfgLocation(loc),
				computeSortsForIcfgLocationPredicate(loc));
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
		final List<IProgramVar> variables = getVariableListForProcedure(loc.getProcedure());
		return variables.stream().map(pv -> pv.getSort()).collect(Collectors.toList());
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
	private List<IProgramVar> getVariableListForProcedure(final String procedure) {
		List<IProgramVar> result = mProcToVarList.get(procedure);
		if (result == null) {
			final Set<IProgramNonOldVar> modGlobalVars =
					mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(procedure);
			final Set<ILocalProgramVar> localVars =
					mIcfg.getCfgSmtToolkit().getSymbolTable().getLocals(procedure);
			result = new ArrayList<>();
			for (final IProgramNonOldVar mgv : modGlobalVars) {
				result.add(mgv);
				result.add(mgv.getOldVar());
			}
			result.addAll(localVars);
			mProcToVarList.put(procedure, Collections.unmodifiableList(result));
		}
		return result;
	}

	private String computePredicateNameForIcfgLocation(final IcfgLocation loc) {
		return loc.toString();
	}

}
