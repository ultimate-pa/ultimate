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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
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
//	private final XnfConversionTechnique mXnfConversionTechnique;
//	private final SimplificationTechnique mSimplificationTechnique;

//	private IIcfg<?> mResult;
	private IElement mResult;

	private ManagedScript mMgdScript;
	private HcSymbolTable mHcSymbolTable;
	private IIcfg<IcfgLocation> mIcfg;

	private final Map<String, List<IProgramVar>> mProcToVarList;

	public IcfgToChcObserver(final ILogger logger, final IUltimateServiceProvider services) {
//			final ITranslator backtranslator, final SimplificationTechnique simplTech,
//			final XnfConversionTechnique xnfConvTech) {
		mLogger = logger;
		mServices = services;
//		mSimplificationTechnique = simplTech;
//		mXnfConversionTechnique = xnfConvTech;
//		mResult = null;
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

		final Set<HornClause> resultChcs = new LinkedHashSet<>();
		final IcfgEdgeIterator edgeIt = new IcfgEdgeIterator(icfg);

		while (edgeIt.hasNext()) {
			final IcfgEdge currentEdge = edgeIt.next();

			if (currentEdge instanceof IIcfgInternalTransition<?>) {
				final IIcfgInternalTransition<IcfgLocation> currentInternalEdge =
						(IIcfgInternalTransition<IcfgLocation>) currentEdge;

				/*  fields necessary for building the horn clause */

				final UnmodifiableTransFormula tf = currentEdge.getTransformula();
				final Map<Term, Term> substitutionMapping = new LinkedHashMap<>();
				final List<IProgramVar> varsForProc =
							getVariableListForProcedure(currentEdge.getPrecedingProcedure());

				final HcPredicateSymbol headPred;
				final List<HcHeadVar> headVars;
				final boolean isTargetErrorLocation = icfg.getProcedureErrorNodes()
						.get(currentEdge.getPrecedingProcedure())
						.contains(currentEdge.getTarget());
				if (isTargetErrorLocation) {
					headPred = null;
					headVars = null;
				} else {
					headPred = getOrConstructPredicateSymbolForIcfgLocation(currentEdge.getTarget());

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


				final boolean isSourceInitialLocation = icfg.getInitialNodes().contains(currentEdge.getSource());

				final List<HcPredicateSymbol> bodyPreds;
				final List<List<Term>> bodyPredToArguments;
				final Set<HcBodyVar> bodyVars;

				if (isSourceInitialLocation) {
					bodyPreds = Collections.emptyList();
					bodyPredToArguments = Collections.emptyList();
					bodyVars = Collections.emptySet();
				} else {
					bodyPreds = Collections.singletonList(
							getOrConstructPredicateSymbolForIcfgLocation(currentEdge.getSource()));
					bodyVars = new LinkedHashSet<>();
					{
						final List<Term> firstPredArgs = new ArrayList<>();

						for (int i = 0; i < varsForProc.size(); i++) {
							final HcBodyVar bodyVar =
									mHcSymbolTable.getOrConstructBodyVar(bodyPreds.get(0), i,
											varsForProc.get(i).getSort());
							bodyVars.add(bodyVar);

							final TermVariable inTv = tf.getInVars().get(varsForProc.get(i));
							final TermVariable outTv = tf.getInVars().get(varsForProc.get(i));
							if (inTv == null && outTv == null) {
								// pv is neither in nor out --> in and out must match..
								if (isTargetErrorLocation) {
									/* .. except if there is on out, because the target is "false", then it does not matter
									 * which term we use here */
									firstPredArgs.add(bodyVar.getTermVariable());
								} else {
									firstPredArgs.add(headVars.get(i).getTermVariable());
								}
							} else if (inTv == null && outTv != null) {
								// pv is not an in var of tf but is an outvar --> leave the body pred arg disconnected..
								firstPredArgs.add(bodyVar.getTermVariable());
							} else {
								/* pv is an in var of tf --> the headvar must connect to the corresponding variable in
								 * the constraint */
								firstPredArgs.add(bodyVar.getTermVariable());
								substitutionMapping.put(inTv, bodyVar.getTermVariable());
							}
						}
						bodyPredToArguments = Collections.singletonList(firstPredArgs);
					}
				}


				final Term constraint = new Substitution(mMgdScript, substitutionMapping).transform(tf.getFormula());


				/* construct the horn clause and add it to the resulting chc set */

				if (isTargetErrorLocation) {
					resultChcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, bodyPreds,
							bodyPredToArguments, bodyVars));
				} else {
					resultChcs.add(new HornClause(mMgdScript, mHcSymbolTable, constraint, headPred, headVars, bodyPreds,
							bodyPredToArguments, bodyVars));
				}
			} else if (currentEdge instanceof IIcfgCallTransition<?>) {
				final IIcfgCallTransition<IcfgLocation> currentCallEdge =
						(IIcfgCallTransition<IcfgLocation>) currentEdge;

			} else if (currentEdge instanceof IIcfgReturnTransition<?, ?>) {
				final IIcfgReturnTransition<IcfgLocation, Call> currentReturnEdge =
						(IIcfgReturnTransition<IcfgLocation, Call>) currentEdge;

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
			result.addAll(modGlobalVars);
			result.addAll(localVars);
			mProcToVarList.put(procedure, Collections.unmodifiableList(result));
		}
		return result;
	}

	private String computePredicateNameForIcfgLocation(final IcfgLocation loc) {
		return loc.toString();
	}


}
