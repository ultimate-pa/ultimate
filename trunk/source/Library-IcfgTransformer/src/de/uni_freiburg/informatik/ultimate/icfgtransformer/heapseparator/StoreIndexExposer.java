package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class StoreIndexExposer implements ITransformulaTransformer {
	
	private final Map<ArrayIndex, List<IProgramNonOldVar>> mStoreIndexToFreezeIndex = new HashMap<>();
	private final ManagedScript mMgdScript;
	private final DefaultIcfgSymbolTable mNewSymbolTable;
	
	public StoreIndexExposer(CfgSmtToolkit csToolkit) {
		mMgdScript = csToolkit.getManagedScript();
		mNewSymbolTable = new DefaultIcfgSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures());
	}

	@Override
	public void preprocessIcfg(IIcfg<?> icfg) {
		// do nothing
	}

	@Override
	public TransforumlaTransformationResult transform(UnmodifiableTransFormula tf) {
		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();
		
		final List<Term> indexUpdateFormula = new ArrayList<>();
		
		mMgdScript.lock(this);
		
		final Set<ArrayIndex> storeIndices = MultiDimensionalStore.extractArrayStoresShallow(tf.getFormula()).stream()
			.map(mds -> mds.getIndex()).collect(Collectors.toSet());
		
		for (ArrayIndex storeIndex : storeIndices) {
			final List<Term> indexUpdates = new ArrayList<>();
			
			final List<IProgramNonOldVar> freezeIndex = getFreezeIndex(storeIndex);
			
			for (int i = 0; i < freezeIndex.size(); i++) {
				final TermVariable inputFreezeIndexTv;
				final TermVariable updatedFreezeIndexTv;
				if (!extraInVars.containsKey(freezeIndex.get(i))) {
					assert !extraOutVars.containsKey(freezeIndex.get(i));
					inputFreezeIndexTv = mMgdScript.constructFreshCopy(freezeIndex.get(i).getTermVariable());
					updatedFreezeIndexTv = mMgdScript.constructFreshCopy(freezeIndex.get(i).getTermVariable());
					extraInVars.put(freezeIndex.get(i), inputFreezeIndexTv);
					extraOutVars.put(freezeIndex.get(i), updatedFreezeIndexTv);
				} else {
					assert extraOutVars.containsKey(freezeIndex.get(i));
					inputFreezeIndexTv = extraInVars.get(freezeIndex.get(i));
					updatedFreezeIndexTv = extraOutVars.get(freezeIndex.get(i));
				}
				assert extraInVars.containsKey(freezeIndex.get(i)) && extraOutVars.containsKey(freezeIndex.get(i));

				/*
				 * construct the nondeterministic update "freezeIndex' = freezeIndex \/ freezeIndex' = storeIndex"
				 */
				indexUpdates.add(
						SmtUtils.or(mMgdScript.getScript(), 
//								mMgdScript.term(this, "=", updatedFreezeIndexTv, inputFreezeIndexTv),
								mMgdScript.term(this, "=", updatedFreezeIndexTv,storeIndex.get(i)))
								);
			}
			indexUpdateFormula.add(SmtUtils.and(mMgdScript.getScript(), indexUpdates));
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
		newFormulaConjuncts.addAll(indexUpdateFormula);
				
		tfBuilder.setFormula(SmtUtils.and(mMgdScript.getScript(), newFormulaConjuncts));
		
		tfBuilder.setInfeasibility(tf.isInfeasible());
		
		return new TransforumlaTransformationResult(tfBuilder.finishConstruction(mMgdScript));
	}
	
	private List<IProgramNonOldVar> getFreezeIndex(ArrayIndex storeIndex) {
		List<IProgramNonOldVar> result = mStoreIndexToFreezeIndex.get(storeIndex);
		if (result == null) {
			result = new ArrayList<>();
			for (Term indEl : storeIndex) {
				final BoogieNonOldVar freshPv = ProgramVarUtils.constructGlobalProgramVarPair(
						indEl.toString().replace("|", "") + "_frz", indEl.getSort(), 
						mMgdScript, this);
				result.add(freshPv);
				mNewSymbolTable.add(freshPv);
			}
			mStoreIndexToFreezeIndex.put(storeIndex, result);
		}
		return result;
	}

	@Override
	public String getName() {
		return this.getClass().getName();
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewSymbolTable;
	}

}
