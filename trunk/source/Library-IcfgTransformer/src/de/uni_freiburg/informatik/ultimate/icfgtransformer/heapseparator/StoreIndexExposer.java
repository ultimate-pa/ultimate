package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class StoreIndexExposer implements ITransformulaTransformer {
	
	private final Map<ArrayIndex, ArrayIndex> mStoreIndexToFreezeIndex = new HashMap<>();
	private final ManagedScript mMgdScript;
	
	public StoreIndexExposer(ManagedScript mgdScript) {
		mMgdScript = mgdScript;
	}

	@Override
	public void preprocessIcfg(IIcfg<?> icfg) {
		// TODO Auto-generated method stub

	}

	@Override
	public TransforumlaTransformationResult transform(UnmodifiableTransFormula tf) {
		final Map<IProgramVar, TermVariable> extraInVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> extraOutVars = new HashMap<>();
		for (MultiDimensionalStore mds : MultiDimensionalStore.extractArrayStoresShallow(tf.getFormula())) {
			final ArrayIndex freezeIndex = getFreezeIndex(mds.getIndex());
			// TODO go on here..
		}

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getOutVars());
		newInVars.putAll(extraOutVars);

		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());
		newOutVars.putAll(extraOutVars);

		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(tf.getInVars(), newOutVars, 
				tf.getNonTheoryConsts().isEmpty(), tf.getNonTheoryConsts(), tf.getBranchEncoders().isEmpty(), 
				tf.getBranchEncoders(), tf.getAuxVars().isEmpty());
				
		final List<Term> newFormulaConjuncts = new ArrayList<>();
		newFormulaConjuncts.add(tf.getFormula());
				
		tfBuilder.setFormula(SmtUtils.and(mMgdScript.getScript(), newFormulaConjuncts));
		
		tfBuilder.setInfeasibility(tf.isInfeasible());

		return new TransforumlaTransformationResult(tfBuilder.finishConstruction(mMgdScript));
	}
	
	ArrayIndex getFreezeIndex(ArrayIndex storeIndex) {
		ArrayIndex result = mStoreIndexToFreezeIndex.get(storeIndex);
		if (result == null) {
			final List<Term> freezeIndex = new ArrayList<>();
			for (Term indEl : storeIndex) {
				freezeIndex.add(mMgdScript.constructFreshTermVariable(indEl.toStringDirect(), indEl.getSort()));
			}
			result = new ArrayIndex(freezeIndex);
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
		// TODO Auto-generated method stub
		return null;
	}

}
