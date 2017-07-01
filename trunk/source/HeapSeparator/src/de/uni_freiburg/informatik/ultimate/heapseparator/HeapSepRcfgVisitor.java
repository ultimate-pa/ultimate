/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE HeapSeparator plug-in.
 *
 * The ULTIMATE HeapSeparator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HeapSeparator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HeapSeparator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HeapSeparator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HeapSeparator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class HeapSepRcfgVisitor extends SimpleRCFGVisitor {

	/**
	 * arrayId before separation --> pointerId --> arrayId after separation
	 */
	NestedMap2<Term, Term, Term> moldArrayToPointerToNewArray;
	/**
	 * arrayId before separation --> arrayId after separation--> Set of pointerIds
	 */
	ManagedScript mScript;
	private VPDomain mVpDomain;
	private NewArrayIdProvider mNewArrayIdProvider;
	
	private final IIcfgSymbolTable mOldSymbolTable;
	private final IIcfgSymbolTable mNewSymbolTable;

	public HeapSepRcfgVisitor(final ILogger logger,
			NewArrayIdProvider naip,
			final ManagedScript script,
			final VPDomain vpDomain, 
			IIcfgSymbolTable oldSymbolTable, 
			IIcfgSymbolTable newSymbolTable) {
		super(logger);
		mNewArrayIdProvider = naip;
		mVpDomain = vpDomain;
		mScript = script;
		mOldSymbolTable = oldSymbolTable;
		mNewSymbolTable = newSymbolTable;
	}

	@Override
	public boolean performedChanges() {
		// TODO make smarter?
		return true;
	}

	@Override
	public boolean abortCurrentBranch() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean abortAll() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void level(final IcfgEdge edge) {
		if (!(edge instanceof CodeBlock)) {
			return;
		}
		final UnmodifiableTransFormula tf = ((CodeBlock) edge).getTransformula();

		final UnmodifiableTransFormula newTf = splitArraysInTransFormula(tf);

		((CodeBlock) edge).setTransitionFormula(newTf);

		super.level(edge);
	}

	public static TermVariable getSplitTermVariable(final String arrayName, final int splitIndex, final Sort sort,
			final Script script) {
		return script.variable(String.format("{}_split_{}", arrayName, splitIndex), sort);
	}

	public static IProgramVar getBoogieVarFromTermVar(final TermVariable tv, final Map<IProgramVar, TermVariable> map1,
			final Map<IProgramVar, TermVariable> map2) {
		for (final Entry<IProgramVar, TermVariable> en : map1.entrySet()) {
			if (en.getValue().equals(tv)) {
				return en.getKey();
			}
		}
		for (final Entry<IProgramVar, TermVariable> en : map2.entrySet()) {
			if (en.getValue().equals(tv)) {
				return en.getKey();
			}
		}
		assert false : "did not find " + tv + " in the given maps";
		return null;
	}

	private UnmodifiableTransFormula splitArraysInTransFormula(final UnmodifiableTransFormula tf) {

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());
		
		Term intermediateFormula = tf.getFormula();

		intermediateFormula = substituteArrayUpdates(tf, newInVars, newOutVars, intermediateFormula);

		intermediateFormula = substituteArrayEqualites(tf, newInVars, newOutVars, intermediateFormula);

		intermediateFormula = substituteRemainingStoresAndSelects(tf, newInVars, newOutVars, intermediateFormula);
		
		boolean newEmptyNonTheoryConsts = false;
		Set<IProgramConst> newNonTheoryConsts = null;
		boolean newEmptyBranchEncoders = false;
		Collection<TermVariable> newBranchEncoders = null; // TODO: deal with these for working LBE, right?..
		boolean newEmptyAuxVars = false;
		TransFormulaBuilder tfBuilder = new TransFormulaBuilder(
				newInVars, 
				newOutVars, 
				newEmptyNonTheoryConsts, 
				newNonTheoryConsts, 
				newEmptyBranchEncoders, 
				newBranchEncoders, 
				newEmptyAuxVars);
		
		tfBuilder.setFormula(intermediateFormula);
		
		tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		
		return tfBuilder.finishConstruction(mScript);
	}



	private Term substituteRemainingStoresAndSelects(final UnmodifiableTransFormula tf,
			final Map<IProgramVar, TermVariable> newInVars, final Map<IProgramVar, TermVariable> newOutVars,
			Term intermediateFormula) {
		final Map<Term, Term> substitutionMapPvoc = new HashMap<>();
		
		List<MultiDimensionalSelect> mdSelects = 
				MultiDimensionalSelect.extractSelectShallow(intermediateFormula, true);//TODO allowArrayValues??
		List<MultiDimensionalSelect> mdSelectsInOriginalTf = 
				MultiDimensionalSelect.extractSelectShallow(tf.getFormula(), true);//TODO allowArrayValues??
		for (MultiDimensionalSelect mds : mdSelects) {
			if (!mdSelectsInOriginalTf.contains(mds)) {
				// the current mds comes from a replacement we made earlier (during ArrayUpdate or ArrayEquality-handling)
				continue;
			}
			if (!mVpDomain.getPreAnalysis().isArrayTracked(
//					VPDomainHelpers.getArrayTerm(getInnerMostArray(mds.getArray())),
					getInnerMostArray(mds.getArray()),
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
//					VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {
				continue;
			}

//			TODO: we can't work on the normalized TermVariables like this, I think..
//			IProgramVarOrConst oldArray = 
//					mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//							VPDomainHelpers.getArrayTerm(mds.getArray()),
//							VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
//							VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
//			assert oldArray != null;
			
			final Term oldArray = VPDomainHelpers.normalizeTerm(getInnerMostArray(mds.getArray()), tf, mScript);

//			List<Term> pointers = convertArrayIndexToEqNodeList(newInVars, newOutVars, mds.getIndex());
			final List<Term> pointers = mds.getIndex().stream()
					.map(t -> VPDomainHelpers.normalizeTerm(t, newInVars, newOutVars, mScript))
					.collect(Collectors.toList());
	

			Term newArray = mNewArrayIdProvider.getNewArrayId(oldArray, pointers);

			updateMappingsForSubstitution(oldArray, newArray, newInVars, newOutVars, substitutionMapPvoc);
		}

		List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresShallow(intermediateFormula);
		List<MultiDimensionalStore> mdStoresInOriginalTf = MultiDimensionalStore.extractArrayStoresShallow(tf.getFormula());
		for (MultiDimensionalStore mds : mdStores) {
			if (!mdStoresInOriginalTf.contains(mds)) {
				// the current mds comes from a replacement we made earlier (during ArrayUpdate or ArrayEquality-handling)
				continue;
			}
			if (!mVpDomain.getPreAnalysis().isArrayTracked(
//					VPDomainHelpers.getArrayTerm(mds.getArray()),
					getInnerMostArray(mds.getArray()),
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
//					VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {
				continue;
			}

//			IProgramVarOrConst oldArray = 
//					mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//							VPDomainHelpers.getArrayTerm(mds.getArray()),
//							VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
			final Term oldArray = VPDomainHelpers.normalizeTerm(getInnerMostArray(mds.getArray()), tf, mScript);

//			List<Term> pointers = convertArrayIndexToEqNodeList(newInVars, newOutVars, mds.getIndex());
			final List<Term> pointers = mds.getIndex().stream()
					.map(t -> VPDomainHelpers.normalizeTerm(t, newInVars, newOutVars, mScript))
					.collect(Collectors.toList());
					
			Term newArray = mNewArrayIdProvider.getNewArrayId(oldArray, pointers);

			updateMappingsForSubstitution(oldArray, newArray, newInVars, newOutVars, substitutionMapPvoc);
		}
		intermediateFormula = new Substitution(mScript, substitutionMapPvoc).transform(intermediateFormula);	
		return intermediateFormula;
	}



	private Term substituteArrayUpdates(final UnmodifiableTransFormula tf,
			final Map<IProgramVar, TermVariable> newInVars, final Map<IProgramVar, TermVariable> newOutVars,
			Term formula) {

		final Map<Term, Term> substitutionMapPvoc = new HashMap<>();

		List<ArrayUpdate> arrayUpdates = ArrayUpdate.extractArrayUpdates(formula);
		for (ArrayUpdate au : arrayUpdates) {
			

//			List<EqNode> pointers = convertArrayIndexToEqNodeList(newInVars, newOutVars, au.getMultiDimensionalStore().getIndex());
			
			final ArrayIndex pointers = au.getMultiDimensionalStore().getIndex();

			if (mVpDomain.getPreAnalysis().isArrayTracked(au.getNewArray(), 
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
//					VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {
//				IProgramVarOrConst lhs = 
//						mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//								au.getNewArray(), 
//								VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
////								VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
//				assert lhs != null;
				final Term lhs = au.getNewArray();
				final Term newArrayLhs = mNewArrayIdProvider.getNewArrayId(lhs, pointers);
				updateMappingsForSubstitution(lhs, newArrayLhs, newInVars, newOutVars, substitutionMapPvoc);
			}
			
			if (mVpDomain.getPreAnalysis().isArrayTracked(au.getOldArray(), 
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
//					VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {
//				IProgramVarOrConst rhsArray = 
//						mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//								au.getOldArray(), 
//								VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
////								VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
//				assert rhsArray != null;
				final Term rhsArray = au.getOldArray();
				Term newArrayRhs = mNewArrayIdProvider.getNewArrayId(rhsArray, pointers);
				updateMappingsForSubstitution(rhsArray, newArrayRhs, newInVars, newOutVars, substitutionMapPvoc);
			}
		}
		
		Term newTerm = new Substitution(mScript, substitutionMapPvoc).transform(formula);
		return newTerm;
	}



//	private List<EqNode> convertArrayIndexToEqNodeList(final Map<IProgramVar, TermVariable> newInVars,
//			final Map<IProgramVar, TermVariable> newOutVars, ArrayIndex index) {
//		List<EqNode> pointers = index.stream()
//				.map(indexTerm -> mVpDomain.getPreAnalysis().getEqNode(
//						indexTerm, 
//						VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars)))
//				.collect(Collectors.toList());
//		return pointers;
//	}



	private Term substituteArrayEqualites(final UnmodifiableTransFormula tf,
			final Map<IProgramVar, TermVariable> newInVars, 
			final Map<IProgramVar, TermVariable> newOutVars, 
			final Term intermediateFormula) {
		final List<ArrayEquality> arrayEqualities = ArrayEquality.extractArrayEqualities(intermediateFormula);
		final Map<Term, Term> equalitySubstitution = new HashMap<>();
		mScript.lock(this);
		for (ArrayEquality ae : arrayEqualities) {
			/*
			 * plan:
			 *  (- check compatibility --> should be guaranteed by NewArrayIdProvider)
			 *  - make an assignment between all the partitions
			 */
			if (!mVpDomain.getPreAnalysis().isArrayTracked(ae.getLhs(), 
//					VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))
					|| !mVpDomain.getPreAnalysis().isArrayTracked(ae.getRhs(), 
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
//							VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {
				continue;
			}
			
			
			List<Term> newEqualities = new ArrayList<>();
			
			final Term oldLhs = ae.getLhs();
//			IProgramVarOrConst oldLhs = mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//							ae.getLhs(), 
//					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
//							VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
			final List<Term> newLhss = mNewArrayIdProvider.getAllNewArrayIds(oldLhs);

			final Term oldRhs = ae.getRhs();
//			IProgramVarOrConst oldRhs = mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//							ae.getRhs(), 
//					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
//							VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
			final List<Term> newRhss = mNewArrayIdProvider.getAllNewArrayIds(oldRhs);
			
			
			assert newLhss.size() == newRhss.size();
			for (int i = 0; i < newLhss.size(); i++) {
				final Term newLhs = newLhss.get(i);
				final Term newRhs = newRhss.get(i);
				final Term newEquality = mScript.term(this, "=", newLhs, newRhs);
				newEqualities.add(newEquality);
				
				if (tf.getInVars().containsKey(oldLhs)) {
					newInVars.remove(oldLhs);
					newInVars.put((IProgramVar) newLhs, (TermVariable) newLhs);
				}
				if (tf.getInVars().containsKey(oldRhs)) {
					newInVars.remove(oldRhs);
					newInVars.put((IProgramVar) newRhs, (TermVariable) newRhs);
				}
				if (tf.getOutVars().containsKey(oldLhs)) {
					newOutVars.remove(oldLhs);
					newOutVars.put((IProgramVar) newLhs, (TermVariable) newLhs);
				}
				if (tf.getOutVars().containsKey(oldRhs)) {
					newOutVars.remove(oldRhs);
					newOutVars.put((IProgramVar) newRhs, (TermVariable) newRhs);
				}

			}
			assert newEqualities.size() > 0;
			final Term newConjunctionOfEquations = SmtUtils.and(mScript.getScript(), newEqualities);
//					newEqualities.size() == 1 ?
//					newEqualities.get(0) :
//					mScript.term(this, "and", newEqualities.toArray(new Term[newEqualities.size()]));
			equalitySubstitution.put(ae.getOriginalTerm(), newConjunctionOfEquations);
		}
		mScript.unlock(this);
		final Term newTerm = new Substitution(mScript, equalitySubstitution).transform(intermediateFormula);
		return newTerm;
	}



	/**
	 * 
	 * - updates the maps newInVars and newOutVars
	 * - updates the map substitutionMap
	 * 
	 * This method is for the simple cases, where we just need to replace the arrayIdentifer "one-by-one".
	 * (not like the ArrayEquality, where we replace one-by-many)
	 * 
	 * @param oldArray
	 * @param newArray
	 * @param tf
	 * @param newInVars
	 * @param newOutVars
	 * @param substitutionMap
	 */
	private void updateMappingsForSubstitution(Term oldArrayTerm, Term newArrayTerm,
			final Map<IProgramVar, TermVariable> newInVars,
			final Map<IProgramVar, TermVariable> newOutVars,
			final Map<Term, Term> substitutionMap) {
		if (oldArrayTerm instanceof TermVariable) {
//		if (oldArray instanceof IProgramVar) {
//			assert newArray instanceof IProgramVar : "right?..";
			assert newArrayTerm instanceof TermVariable;
			final IProgramVar oldArray = mOldSymbolTable.getProgramVar((TermVariable) oldArrayTerm);
			final IProgramVar newArray = mNewSymbolTable.getProgramVar((TermVariable) newArrayTerm);
		
			TermVariable inv = newInVars.get(oldArray);
			TermVariable outv = newOutVars.get(oldArray);

			TermVariable invNewTv = null;
			if (inv != null) {
				invNewTv = mScript.constructFreshCopy((TermVariable) newArrayTerm);
				newInVars.remove(oldArray);
				newInVars.put((IProgramVar) newArray, invNewTv);
				substitutionMap.put(inv, invNewTv);
			}
		
			if (outv != null) {
				TermVariable newTv;
				if (inv == outv) {
					newTv = invNewTv;
				} else {
					newTv = mScript.constructFreshCopy((TermVariable) newArrayTerm);
				}
				newOutVars.remove(oldArray);
				newOutVars.put((IProgramVar) newArray, newTv);
				substitutionMap.put(outv, newTv);
			}
			
		} else if (SmtUtils.isConstant(oldArrayTerm)) {
			/*
			 * the array id is a constant (or literal)
			 *  --> there are no changes to the invar/outvar mappings, only to the substitution
			 */
			substitutionMap.put(oldArrayTerm, newArrayTerm);
		} else {
			throw new AssertionError("did not see this case coming..");
		}
	}
	
	public static Term getInnerMostArray(Term arrayTerm) {
		assert arrayTerm.getSort().isArraySort();
		Term innerArray = arrayTerm;
		while (SmtUtils.containsFunctionApplication(innerArray, "store")) {
			innerArray = ((ApplicationTerm) innerArray).getParameters()[0];
		}
		assert innerArray instanceof TermVariable;
		return innerArray;
	}
}