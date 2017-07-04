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

import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class HeapSepTransFormulaTransformer implements ITransformulaTransformer {

	private final ManagedScript mScript;
	private final VPDomain<IcfgEdge> mVpDomain;
	private final NewArrayIdProvider mNewArrayIdProvider;

	public HeapSepTransFormulaTransformer(final ManagedScript script, final VPDomain<IcfgEdge> vpDomain,
			final NewArrayIdProvider newArrayIdProvider) {
		mScript = script;
		mVpDomain = vpDomain;
		mNewArrayIdProvider = newArrayIdProvider;
	}

	@Override
	public TransforumlaTransformationResult transform(final UnmodifiableTransFormula tf) {
		// TODO: Determine when this is an overapproximation
		return new TransforumlaTransformationResult(splitArraysInTransFormula(tf), true);
	}

	@Override
	public String getName() {
		return HeapSeparator.class.getSimpleName();
	}

	public static TermVariable getSplitTermVariable(final String arrayName, final int splitIndex, final Sort sort,
			final Script script) {
		return script.variable(String.format("%s_split_%s", arrayName, splitIndex), sort);
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

	private UnmodifiableTransFormula splitArraysInTransFormula(final TransFormula tf) {

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(tf.getOutVars());

		Term intermediateFormula = tf.getFormula();

		intermediateFormula = substituteArrayUpdates(tf, newInVars, newOutVars, intermediateFormula);

		intermediateFormula = substituteArrayEqualites(tf, newInVars, newOutVars, intermediateFormula);

		intermediateFormula = substituteRemainingStoresAndSelects(tf, newInVars, newOutVars, intermediateFormula);

		final boolean newEmptyNonTheoryConsts = false;
		final Set<IProgramConst> newNonTheoryConsts = null;
		final boolean newEmptyBranchEncoders = false;
		// TODO: deal with these for working LBE, right?..
		final Collection<TermVariable> newBranchEncoders = null;
		final boolean newEmptyAuxVars = false;
		final TransFormulaBuilder tfBuilder = new TransFormulaBuilder(newInVars, newOutVars, newEmptyNonTheoryConsts,
				newNonTheoryConsts, newEmptyBranchEncoders, newBranchEncoders, newEmptyAuxVars);

		tfBuilder.setFormula(intermediateFormula);

		tfBuilder.setInfeasibility(Infeasibility.NOT_DETERMINED);

		return tfBuilder.finishConstruction(mScript);
	}

	private Term substituteRemainingStoresAndSelects(final TransFormula tf,
			final Map<IProgramVar, TermVariable> newInVars, final Map<IProgramVar, TermVariable> newOutVars,
			final Term intermediateFormula) {
		final Map<Term, Term> substitutionMapPvoc = new HashMap<>();
		// TODO allowArrayValues??
		final List<MultiDimensionalSelect> mdSelects =
				MultiDimensionalSelect.extractSelectShallow(intermediateFormula, true);
		// TODO allowArrayValues??
		final List<MultiDimensionalSelect> mdSelectsInOriginalTf =
				MultiDimensionalSelect.extractSelectShallow(tf.getFormula(), true);
		for (final MultiDimensionalSelect mds : mdSelects) {
			if (!mdSelectsInOriginalTf.contains(mds)) {
				// the current mds comes from a replacement we made earlier (during ArrayUpdate or
				// ArrayEquality-handling)
				continue;
			}
			if (!mVpDomain.getPreAnalysis().isArrayTracked(VPDomainHelpers.getArrayTerm(mds.getArray()),
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
				// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {
				continue;
			}

			// TODO: we can't work on the normalized TermVariables like this, I think..
//			final IProgramVarOrConst oldArray = mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//					VPDomainHelpers.getArrayTerm(mds.getArray()),
//					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
			// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
			final Term oldArray = VPDomainHelpers.normalizeTerm(mds.getArray(), tf, mScript);

//			assert oldArray != null;

//			final List<EqNode> pointers = convertArrayIndexToEqNodeList(newInVars, newOutVars, mds.getIndex());
			final List<Term> pointers = mds.getIndex().stream()
					.map(t -> VPDomainHelpers.normalizeTerm(t, newInVars, newOutVars, mScript))
					.collect(Collectors.toList());
	

			final Term newArray = mNewArrayIdProvider.getNewArrayId(oldArray, pointers);

			updateMappingsForSubstitution(oldArray, newArray, newInVars, newOutVars, substitutionMapPvoc);
		}

		final List<MultiDimensionalStore> mdStores =
				MultiDimensionalStore.extractArrayStoresShallow(intermediateFormula);
		final List<MultiDimensionalStore> mdStoresInOriginalTf =
				MultiDimensionalStore.extractArrayStoresShallow(tf.getFormula());
		for (final MultiDimensionalStore mds : mdStores) {
			if (!mdStoresInOriginalTf.contains(mds)) {
				// the current mds comes from a replacement we made earlier (during ArrayUpdate or
				// ArrayEquality-handling)
				continue;
			}
			if (!mVpDomain.getPreAnalysis().isArrayTracked(VPDomainHelpers.getArrayTerm(mds.getArray()),
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
				// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {
				continue;
			}

//			final IProgramVarOrConst oldArray = mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//					VPDomainHelpers.getArrayTerm(mds.getArray()),
//					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
			final Term oldArray = VPDomainHelpers.normalizeTerm(mds.getArray(), tf, mScript);

//			final List<EqNode> pointers = convertArrayIndexToEqNodeList(newInVars, newOutVars, mds.getIndex());
			final List<Term> pointers = mds.getIndex().stream()
					.map(t -> VPDomainHelpers.normalizeTerm(t, newInVars, newOutVars, mScript))
					.collect(Collectors.toList());

			final Term newArray = mNewArrayIdProvider.getNewArrayId(oldArray, pointers);

			updateMappingsForSubstitution(oldArray, newArray, newInVars, newOutVars, substitutionMapPvoc);
		}
		return new Substitution(mScript, substitutionMapPvoc).transform(intermediateFormula);
	}

	private Term substituteArrayUpdates(final TransFormula tf, final Map<IProgramVar, TermVariable> newInVars,
			final Map<IProgramVar, TermVariable> newOutVars, final Term formula) {

		final Map<Term, Term> substitutionMapPvoc = new HashMap<>();

		final List<ArrayUpdate> arrayUpdates = ArrayUpdate.extractArrayUpdates(formula);
		for (final ArrayUpdate au : arrayUpdates) {

//			final List<EqNode> pointers =
//					convertArrayIndexToEqNodeList(newInVars, newOutVars, au.getMultiDimensionalStore().getIndex());
			final List<Term> pointers = au.getMultiDimensionalStore().getIndex().stream()
					.map(t -> VPDomainHelpers.normalizeTerm(t, newInVars, newOutVars, mScript))
					.collect(Collectors.toList());

			if (mVpDomain.getPreAnalysis().isArrayTracked(au.getNewArray(),
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
				// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {

//				final IProgramVarOrConst lhs = mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//						au.getNewArray(), VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
				// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
				final Term lhs = VPDomainHelpers.normalizeTerm(au.getNewArray(), tf, mScript);

//				assert lhs != null;
				final Term newArrayLhs = mNewArrayIdProvider.getNewArrayId(lhs, pointers);
				updateMappingsForSubstitution(lhs, newArrayLhs, newInVars, newOutVars, substitutionMapPvoc);
			}

			if (mVpDomain.getPreAnalysis().isArrayTracked(au.getOldArray(),
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
				// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {
//				final IProgramVarOrConst rhsArray = mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(
//						au.getOldArray(), VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
				// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
				final Term rhsArray = VPDomainHelpers.normalizeTerm(au.getOldArray(), tf, mScript);

//				assert rhsArray != null;
//				final IProgramVarOrConst newArrayRhs = mNewArrayIdProvider.getNewArrayId(rhsArray, pointers);
				final Term newArrayRhs = mNewArrayIdProvider.getNewArrayId(rhsArray, pointers);
				updateMappingsForSubstitution(rhsArray, newArrayRhs, newInVars, newOutVars, substitutionMapPvoc);
			}
		}

		final Term newTerm = new Substitution(mScript, substitutionMapPvoc).transform(formula);
		return newTerm;
	}

//	private List<EqNode> convertArrayIndexToEqNodeList(final Map<IProgramVar, TermVariable> newInVars,
//			final Map<IProgramVar, TermVariable> newOutVars, final ArrayIndex index) {
//		final List<EqNode> pointers =
//				index.stream()
//						.map(indexTerm -> mVpDomain.getPreAnalysis()
//								.getEqNode(indexTerm, VPDomainHelpers
//										.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars)))
//						.collect(Collectors.toList());
//		return pointers;
//	}

	private Term substituteArrayEqualites(final TransFormula tf, final Map<IProgramVar, TermVariable> newInVars,
			final Map<IProgramVar, TermVariable> newOutVars, final Term intermediateFormula) {
		final List<ArrayEquality> arrayEqualities = ArrayEquality.extractArrayEqualities(intermediateFormula);
		final Map<Term, Term> equalitySubstitution = new HashMap<>();
		mScript.lock(this);
		for (final ArrayEquality ae : arrayEqualities) {
			/*
			 * plan: (- check compatibility --> should be guaranteed by NewArrayIdProvider) - make an assignment between
			 * all the partitions
			 */
			if (!mVpDomain.getPreAnalysis().isArrayTracked(ae.getLhs(),
					// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))
					|| !mVpDomain.getPreAnalysis().isArrayTracked(ae.getRhs(),
							VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf))) {
				// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars))) {
				continue;
			}

			final List<Term> newEqualities = new ArrayList<>();

//			final IProgramVarOrConst oldLhs = mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(ae.getLhs(),
//					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
			// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
			final Term oldLhs = VPDomainHelpers.normalizeTerm(ae.getLhs(), tf, mScript);

			final List<Term> newLhss = mNewArrayIdProvider.getAllNewArrayIds(oldLhs);

//			final IProgramVarOrConst oldRhs = mVpDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(ae.getRhs(),
//					VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
			// VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(newInVars, newOutVars));
			final Term oldRhs = VPDomainHelpers.normalizeTerm(ae.getRhs(), tf, mScript);
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
			assert !newEqualities.isEmpty();
			final Term newConjunctionOfEquations = newEqualities.size() == 1 ? newEqualities.get(0)
					: mScript.term(this, "and", newEqualities.toArray(new Term[newEqualities.size()]));
			equalitySubstitution.put(ae.getOriginalTerm(), newConjunctionOfEquations);
		}
		mScript.unlock(this);
		final Term newTerm = new Substitution(mScript, equalitySubstitution).transform(intermediateFormula);
		return newTerm;
	}

	/**
	 *
	 * - updates the maps newInVars and newOutVars - updates the map substitutionMap
	 *
	 * This method is for the simple cases, where we just need to replace the arrayIdentifer "one-by-one". (not like the
	 * ArrayEquality, where we replace one-by-many)
	 *
	 * @param oldArray
	 * @param newArray
	 * @param tf
	 * @param newInVars
	 * @param newOutVars
	 * @param substitutionMap
	 */
	private void updateMappingsForSubstitution(final Term oldArray, final Term newArray,
			final Map<IProgramVar, TermVariable> newInVars, final Map<IProgramVar, TermVariable> newOutVars,
			final Map<Term, Term> substitutionMap) {
		if (oldArray instanceof IProgramVar) {
			assert newArray instanceof IProgramVar : "right?..";

			final TermVariable inv = newInVars.get(oldArray);
			final TermVariable outv = newOutVars.get(oldArray);

			TermVariable invNewTv = null;
			if (inv != null) {
				invNewTv = mScript.constructFreshCopy((TermVariable) newArray);
				newInVars.remove(oldArray);
				newInVars.put((IProgramVar) newArray, invNewTv);
				substitutionMap.put(inv, invNewTv);
			}

			if (outv != null) {
				TermVariable newTv;
				if (inv == outv) {
					newTv = invNewTv;
				} else {
					newTv = mScript.constructFreshCopy((TermVariable) newArray);
				}
				newOutVars.remove(oldArray);
				newOutVars.put((IProgramVar) newArray, newTv);
				substitutionMap.put(outv, newTv);
			}

		} else {
			/*
			 * the array id is a constant (or literal) --> there are no changes to the invar/outvar mappings, only to
			 * the substitution
			 */
			substitutionMap.put(oldArray, newArray);
		}
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewArrayIdProvider.getNewSymbolTable();
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// TODO Does this transformer need any knowledge about the icfg as a whole?

	}
}
