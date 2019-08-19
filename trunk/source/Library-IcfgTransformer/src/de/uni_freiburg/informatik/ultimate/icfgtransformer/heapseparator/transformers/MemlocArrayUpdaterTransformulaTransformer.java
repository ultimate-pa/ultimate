/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.transformers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.LocArrayInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.MemlocArrayManager;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.ArrayEqualityLocUpdateInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.EdgeInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.StoreInfo;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SubtreePosition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Applies the "memloc-array transformation"
 *
 * Transformation rules (assuming a is a heap array group):
 * <ul>
 *  <li> havoc a (i.e., a is completely unconstrained in the given formula TODO: how to determine that??)
 *     --> conjoin a-loc-n := (const l_0) (for every dimension n)
 *  <li> a' = a[i:=v]
 *     -->  conjoin a-loc-1' = a-loc-1[i:=s] (where s is the literal belonging to that store term)
 *  <li> a' = a[i:=a[i][j:=v]]
 *     --> conjoin a-loc-1' = a-loc-1[i:=s]  /\ a-loc-2' = a-loc-2[i:=a-loc-2[i][j:=s']]
 *     (where s,s' are the literals belonging to those store terms)
 *  <li> a' = b (a an in-var b an out-var)
 *     --> conjoin a-loc-n' = b-loc-n (for every dimension n)
 *  <li> a = b (a, b being invars) --> error! forbidden syntax
 * </ul>
 *
 *
 * old (17/08/2018):
 * Performs the following steps:
 * <ul>
 *  <li> introduce a fresh array-type variable, called the memloc-array
 *  <li> at each write to an array in the program, at location l with index variable i:
 *   <ul>
 *    <li> introduce a fresh memloc-literal "(l, i)" that represents this write location
 *    <li> update the memloc array like this: memloc[i] := (l,i);
 *   </ul>
 *  <li> make sure that all memloc-literals are assumed as distinct by the solver (may be done outside this class)
 * </ul>
 *
 * @param <INLOC>
 * @param <OUTLOC>
 */
public class MemlocArrayUpdaterTransformulaTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements ITransformulaTransformer {

	private final Map<StoreInfo, IProgramConst> mStoreInfoToLocLiteral;

	private final NestedMap2<EdgeInfo, SubtreePosition, ArrayEqualityLocUpdateInfo> mEdgeToPositionToLocUpdateInfo;

//	private final static boolean TRACK_CONSTANTS = false;
//	private final Set<ConstantTerm> mAllConstantTerms;

	private final int mMemLocLitCounter = 0;

	private final List<IProgramVarOrConst> mHeapArrays;

	private final MemlocArrayManager mLocArrayManager;

	ManagedScript mMgdScript;

	private final DefaultIcfgSymbolTable mNewSymbolTable;

	/**
	 * info must be queried after all transform calls have been made
	 */
	private boolean mQueriedStoreAndLitInfo;

	private final HashRelation<String, IProgramNonOldVar> mNewModifiableGlobals;

	private final HashRelation<EdgeInfo, TermVariable> mEdgeToUnconstrainedVars = new HashRelation<>();

	private final IUltimateServiceProvider mServices;

	public MemlocArrayUpdaterTransformulaTransformer(
			final IUltimateServiceProvider services,
			final ILogger logger,
			final CfgSmtToolkit oldCsToolkit,
			final MemlocArrayManager memlocArrayManager,
			final List<IProgramVarOrConst> heapArrays,
			final NestedMap2<EdgeInfo, SubtreePosition, ArrayEqualityLocUpdateInfo> edgeToPositionToLocUpdateInfo) {
		mMgdScript = oldCsToolkit.getManagedScript();
		mEdgeToPositionToLocUpdateInfo = edgeToPositionToLocUpdateInfo;
//		mAllConstantTerms = TRACK_CONSTANTS ? new HashSet<>() : null;
		mLocArrayManager = memlocArrayManager;
		mStoreInfoToLocLiteral = new HashMap<>();
		mHeapArrays = heapArrays;

		mNewSymbolTable = new DefaultIcfgSymbolTable(oldCsToolkit.getSymbolTable(), oldCsToolkit.getProcedures());
		mNewModifiableGlobals = new HashRelation<>(oldCsToolkit.getModifiableGlobalsTable().getProcToGlobals());

		mServices = services;
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		assert !mQueriedStoreAndLitInfo;

		final EdgeInfo edgeInfo = new EdgeInfo((IcfgEdge) oldEdge);

		if (mEdgeToPositionToLocUpdateInfo.get(edgeInfo) == null
				&& mEdgeToUnconstrainedVars.getImage(edgeInfo) == null) {
			// edge does not have any array equalities or unconstrained vars --> nothing to do
			return new TransformulaTransformationResult(tf);
		}

		// replace array equations by themselves conjoined with equations on loc arrays
		final Term transitionFormulaWithLocUpdates;
		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();
		final Set<IProgramConst> extraConstants = new HashSet<>();
		final Set<TermVariable> extraAuxVars = new HashSet<>();
		final Map<SubtreePosition, ArrayEqualityLocUpdateInfo> posToLocUpdateInfo =
					mEdgeToPositionToLocUpdateInfo.get(edgeInfo);
		if (posToLocUpdateInfo != null) {
			final Map<SubtreePosition, Term> arrayEqualityPosToTermWithLocUpdates = new HashMap<>();
			for (final Entry<SubtreePosition, ArrayEqualityLocUpdateInfo> en : posToLocUpdateInfo.entrySet()) {
				arrayEqualityPosToTermWithLocUpdates.put(en.getKey(), en.getValue().getFormulaWithLocUpdates());
				extraInVars.putAll(en.getValue().getExtraInVars());
				extraOutVars.putAll(en.getValue().getExtraOutVars());
				extraAuxVars.addAll(en.getValue().getExtraAuxVars());
				extraConstants.addAll(en.getValue().getExtraConstants());
			}

			transitionFormulaWithLocUpdates =
					new PositionAwareSubstitution(mMgdScript, arrayEqualityPosToTermWithLocUpdates)
						.transform(tf.getFormula());
		} else {
			transitionFormulaWithLocUpdates = tf.getFormula();
		}

		// conjoin initialization code for unconstrained loc array variables

		// assuming the formula is in DNF
		final List<Term> disjunctsWithLocUpdatesAndLocInitialization = new ArrayList<>();
//		for (final Term disjunct : SmtUtils.getDisjuncts(tf.getFormula())) {
		for (final Term disjunct :
			SmtUtils.getDisjuncts(SmtUtils.toDnf(mServices, mMgdScript, tf.getFormula(), XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION))) {

			if (!SmtUtils.isAtomicFormula(disjunct) &&
					(!SmtUtils.isNNF(disjunct) || SmtUtils.containsFunctionApplication(disjunct, "or"))) {
				throw new AssertionError("the code below only works for conjunctive formulas");
			}

			final Term disjunctWithLocUpdatesAndLocInitialization;
			{
				final Set<TermVariable> unconstrainedVars = mEdgeToUnconstrainedVars.getImage(edgeInfo);
				final List<Term> tfWithUpdatesAndInitConjuncts = new ArrayList<>();
				tfWithUpdatesAndInitConjuncts.add(transitionFormulaWithLocUpdates);
				for (final TermVariable ucv : unconstrainedVars) {
					final MultiDimensionalSort mds = new MultiDimensionalSort(ucv.getSort());
					final int dimensionality = mds.getDimension();
					assert dimensionality > 0;
					for (int dim = 1; dim <= dimensionality; dim++) {
						final LocArrayInfo locArray = mLocArrayManager.getOrConstructLocArray(edgeInfo, ucv, dim);
						final Term initConjunct = SmtUtils.binaryEquality(mMgdScript.getScript(),
								locArray.getTerm(),
								locArray.getInitializingConstantArray());
						//							mLocArrayManager.getInitConstantArrayForLocArray(locArray));
						tfWithUpdatesAndInitConjuncts.add(initConjunct);
					}
				}
				disjunctWithLocUpdatesAndLocInitialization =
						SmtUtils.and(mMgdScript.getScript(), tfWithUpdatesAndInitConjuncts);
			}
			disjunctsWithLocUpdatesAndLocInitialization.add(disjunctWithLocUpdatesAndLocInitialization);
		}
		final Term transitionFormulaWithLocUpdatesAndLocInitialization =
				SmtUtils.or(mMgdScript.getScript(), disjunctsWithLocUpdatesAndLocInitialization);

		final Map<IProgramVar, TermVariable> newInVars;
		{
			newInVars = new HashMap<>(tf.getInVars());
			newInVars.putAll(extraInVars);
			for (final IProgramVar iv : extraInVars.keySet()) {
				if (iv instanceof IProgramOldVar) {
					continue;
				}
				mNewSymbolTable.add(iv);
			}
		}

		final Map<IProgramVar, TermVariable> newOutVars;
		{
			newOutVars = new HashMap<>(tf.getOutVars());
			newOutVars.putAll(extraOutVars);
			for (final IProgramVar ov : extraOutVars.keySet()) {
				if (ov instanceof IProgramOldVar) {
					continue;
				}
				mNewSymbolTable.add(ov);
			}
		}

		final Set<IProgramConst> newNonTheoryConsts;
		{
			newNonTheoryConsts = new HashSet<>(tf.getNonTheoryConsts());
			newNonTheoryConsts.addAll(extraConstants);
			for (final IProgramConst pc : extraConstants) {
				mNewSymbolTable.add(pc);
			}
		}

		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(newInVars, newOutVars,
				newNonTheoryConsts.isEmpty(), newNonTheoryConsts, tf.getBranchEncoders().isEmpty(),
				tf.getBranchEncoders(), tf.getAuxVars().isEmpty() && extraAuxVars.isEmpty());

		tfBuilder.setFormula(transitionFormulaWithLocUpdatesAndLocInitialization);
		tfBuilder.setInfeasibility(tf.isInfeasible());
		tfBuilder.addAuxVarsButRenameToFreshCopies(DataStructureUtils.union(tf.getAuxVars(), extraAuxVars), mMgdScript);

		final UnmodifiableTransFormula newTf = tfBuilder.finishConstruction(mMgdScript);

		assert (SmtUtils.checkSatTerm(mMgdScript.getScript(), oldEdge.getTransformula().getClosedFormula())
					== LBool.UNSAT)
				|| (SmtUtils.checkSatTerm(mMgdScript.getScript(), newTf.getClosedFormula()) != LBool.UNSAT);

		return new TransformulaTransformationResult(newTf);
	}

//	/**
//	 * Not this class's core concern but it also picks up all ConstantTerms in the program.
//	 *
//	 * EDIT 18/8/2018: I think this will not be needed anymore.. was needed when loc literals did not have their
//	 *  own {@link Sort} to assert them being different from other literals
//	 *
//	 * @return
//	 */
//	@Deprecated
//	public Set<ConstantTerm> getAllConstantTerms() {
//		if (!TRACK_CONSTANTS) {
//			throw new IllegalStateException();
//		}
//		return mAllConstantTerms;
//	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// do nothing
	}


	@Override
	public String getName() {
		return "withMemlocArrayUpdates";
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewSymbolTable;
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		return mNewModifiableGlobals;
	}

}

//class LocArrayUpdateInserter extends PositionAwareTermTransformer {
//
//	Map<SubtreePosition, StoreInfo> mPosToStoreInfo;
//	private Script mScript;
//
//	public LocArrayUpdateInserter() {
//		// TODO Auto-generated constructor stub
//	}
//
//	public Map<IProgramVar, TermVariable> getExtraInVars() {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//	public Set<TermVariable> getExtraAuxVars() {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//	public Set<IProgramConst> getExtraConstants() {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//	public Map<IProgramVar, TermVariable> getExtraOutVars() {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
//	@Override
//	protected void convert(final Term term, final SubtreePosition pos) {
//		final StoreInfo storeInfo = mPosToStoreInfo.get(pos);
//		if (storeInfo != null) {
//			assert SmtUtils.isFunctionApplication(term, "store");
//
//			enqueueWalker(item);
////			final List<Term> conjuncts = new ArrayList<>(storeInfo.getDimension() + 1);
////			// keep the original term
////			conjuncts.add(term);
////			/*
////			 * For each dimension of t
////			 */
////			for (int i = 0; i < storeInfo.getDimension(); i++) {
////
////			}
////			setResult(SmtUtils.and(mScript, conjuncts));
//		} else {
//			// leave term unchanged
//			super.convert(term, pos);
//		}
//	}
//
//	protected static class BuildConjunction implements Walker {
//
//		// how many terms to pop from the converted stack and put into the result conjunction
//		int mNumberOfConjuncts;
//
//		// a script to construct the fresh term
//		Script mScript;
//
//		public BuildConjunction(final int noConjuncts, final Script script) {
//			mNumberOfConjuncts = noConjuncts;
//			mScript = script;
//		}
//
//		@Override
//		public void walk(final NonRecursive engine) {
//			final LocArrayUpdateInserter transformer = (LocArrayUpdateInserter) engine;
//
//			final Term[] conjuncts = new Term[mNumberOfConjuncts];
//
//			for (int i = 0; i < mNumberOfConjuncts; i++) {
//				conjuncts[i] = transformer.getConverted();
//			}
//
//			transformer.setResult(SmtUtils.and(mScript, conjuncts));
//		}
//
//		@Override
//		public String toString() {
//			return "and\\^" + mNumberOfConjuncts;
//		}
//	}
//
//}
