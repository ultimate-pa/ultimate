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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Applies the "freeze-variables transformation"
 * Performs the following steps:
 *  <li> for each index term that is used in an array update, this introduces a fresh global ProgramVariable, called
 *   the freeze variable, adds a conjunct to the transformula, that nondeterministically assigns the freeze variable the
 *   index term or not.
 *  <li> adds initialization code for all newly introduced freeze variables to the beginning(s) of the program. The
 *   initialization code ensures that initially, a freeze variable is distinct from all other expressions in the program
 *   .. furthermore the valid-array at each freeze variable is set to "1" (this is somewhat hacky, as it is the only
 *   place where the Hoenicke-Lindenmann memory model comes into play..)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <INLOC>
 * @param <OUTLOC>
 */
public class StoreIndexFreezerIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements ITransformulaTransformer {

	private final Map<StoreIndexInfo, IProgramNonOldVar> mStoreIndexInfoToFreezeVar = new HashMap<>();

	private final NestedMap2<EdgeInfo, Term, StoreIndexInfo> mEdgeToIndexToStoreIndexInfo;

	private final Set<ConstantTerm> mAllConstantTerms;

	DefaultIcfgSymbolTable mNewSymbolTable;

	ManagedScript mMgdScript;

	private final HashRelation<String, IProgramNonOldVar> mNewModifiedGlobals;

	public StoreIndexFreezerIcfgTransformer(final ILogger logger,
			final CfgSmtToolkit oldCsToolkit,
			final List<IProgramVarOrConst> heapArrays,
			final NestedMap2<EdgeInfo, Term, StoreIndexInfo> edgeToIndexToStoreIndexInfo) {
		mEdgeToIndexToStoreIndexInfo = edgeToIndexToStoreIndexInfo;
		mAllConstantTerms = new HashSet<>();
		mNewSymbolTable = new DefaultIcfgSymbolTable(oldCsToolkit.getSymbolTable(), oldCsToolkit.getProcedures());
		mNewModifiedGlobals = new HashRelation<>(oldCsToolkit.getModifiableGlobalsTable().getProcToGlobals());
	}

	@Override
	public TransforumlaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		final EdgeInfo edgeInfo = new EdgeInfo((IcfgEdge) oldEdge);

		/*
		 * update the all constants tracking
		 */
		mAllConstantTerms.addAll(new SubTermFinder(t -> t instanceof ConstantTerm)
				.findMatchingSubterms(tf.getFormula()).stream().map(t -> (ConstantTerm) t)
				.collect(Collectors.toList()));

		/*
		 * core business from here on..
		 */
		if (mEdgeToIndexToStoreIndexInfo.get(edgeInfo) == null) {
			// edge does not have any array writes --> return it unchanged
			return new TransforumlaTransformationResult(tf);
		}

		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();

		mMgdScript.lock(this);

		final List<Term> freezeVarUpdates = new ArrayList<>();
		for (final Entry<Term, StoreIndexInfo> en : mEdgeToIndexToStoreIndexInfo.get(edgeInfo).entrySet()) {
			final StoreIndexInfo storeIndexInfo = en.getValue();

			final Term indexTerm = storeIndexInfo.getIndexTerm();

			final IProgramNonOldVar freezeVar = getOrConstructFreezeVariable(storeIndexInfo);

			final TermVariable inputFreezeIndexTv;
			final TermVariable updatedFreezeIndexTv;
			if (!extraInVars.containsKey(freezeVar)) {
				assert !extraOutVars.containsKey(freezeVar);
				inputFreezeIndexTv = mMgdScript.constructFreshCopy(freezeVar.getTermVariable());
				updatedFreezeIndexTv = mMgdScript.constructFreshCopy(freezeVar.getTermVariable());
				extraInVars.put(freezeVar, inputFreezeIndexTv);
				extraOutVars.put(freezeVar, updatedFreezeIndexTv);
			} else {
				assert extraOutVars.containsKey(freezeVar);
				inputFreezeIndexTv = extraInVars.get(freezeVar);
				updatedFreezeIndexTv = extraOutVars.get(freezeVar);
			}
			assert extraInVars.containsKey(freezeVar) && extraOutVars.containsKey(freezeVar);

			assert oldEdge instanceof IcfgInternalTransition;
			mNewModifiedGlobals.addPair(oldEdge.getPrecedingProcedure(), freezeVar);

			/*
			 * construct the nondeterministic update "freezeIndex' = freezeIndex \/ freezeIndex' = storeIndex"
			 */
			freezeVarUpdates.add(SmtUtils.or(mMgdScript.getScript(),
					mMgdScript.term(this, "=", updatedFreezeIndexTv, indexTerm),
					mMgdScript.term(this, "=", updatedFreezeIndexTv, inputFreezeIndexTv)));
		}

		mMgdScript.unlock(this);

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
		newInVars.putAll(extraInVars);

		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());
		newOutVars.putAll(extraOutVars);

		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(newInVars, newOutVars,
				tf.getNonTheoryConsts().isEmpty(), tf.getNonTheoryConsts(), tf.getBranchEncoders().isEmpty(),
				tf.getBranchEncoders(), tf.getAuxVars().isEmpty());


		final List<Term> newFormulaConjuncts = new ArrayList<>();
		newFormulaConjuncts.add(tf.getFormula());
		newFormulaConjuncts.addAll(freezeVarUpdates);

		tfBuilder.setFormula(SmtUtils.and(mMgdScript.getScript(), newFormulaConjuncts));

		tfBuilder.setInfeasibility(tf.isInfeasible());

		tfBuilder.addAuxVarsButRenameToFreshCopies(tf.getAuxVars(), mMgdScript);

		final UnmodifiableTransFormula newTf = tfBuilder.finishConstruction(mMgdScript);
		return new TransforumlaTransformationResult(newTf);
	}

	private IProgramNonOldVar getOrConstructFreezeVariable(final StoreIndexInfo storeIndexInfo) {
		final Term indexTerm = storeIndexInfo.getIndexTerm();

		IProgramNonOldVar result = mStoreIndexInfoToFreezeVar.get(storeIndexInfo);

		if (result == null) {
			result = ProgramVarUtils.constructGlobalProgramVarPair(
						indexTerm.toString().replace("|", "").replace("v_", "") + "_" + storeIndexInfo.getId() + "_frz",
						indexTerm.getSort(), mMgdScript, this);
			/*
			 *  we don't need to do anything for the symbol table here it seems, because the TransformedIcfgBuilder
			 *  recognizes new variables in the TransFormula
			 */
			mNewSymbolTable.add(result);
//			mWriteIndexToTfInfoToFreezeVar.put(indexTerm, tfInfo, result);
			mStoreIndexInfoToFreezeVar.put(storeIndexInfo, result);
		}
		return result;
	}

	public Map<StoreIndexInfo, IProgramNonOldVar> getArrayAccessInfoToFreezeVar() {
		return mStoreIndexInfoToFreezeVar;
	}

	public NestedMap2<EdgeInfo, Term, StoreIndexInfo> getEdgeToIndexToStoreIndexInfo() {
		return mEdgeToIndexToStoreIndexInfo;
	}

	/**
	 * Not this class's core concern but it also picks up all ConstantTerms in the program.
	 * @return
	 */
	public Set<ConstantTerm> getAllConstantTerms() {
		return mAllConstantTerms;
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// TODO Auto-generated method stub
	}

	@Override
	public String getName() {
		return "storeIndexFreezeTfTf";
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewSymbolTable;
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		return mNewModifiedGlobals;
	}
}

