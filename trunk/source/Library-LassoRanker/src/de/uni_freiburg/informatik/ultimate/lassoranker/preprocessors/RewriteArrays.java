/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.IndexAnalyzer;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.IndexAnalyzer.Equality;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.SingleUpdateNormalFormTransformer;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays.TransFormulaLRWithArrayInformation;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Dnf;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

/**
 * Replace term with arrays by term without arrays by introducing replacement
 * variables for all "important" array values and equalities that state the
 * constraints between array indices and array values (resp. their replacement
 * variables).
 * 
 * 
 * @author Matthias Heizmann
 */
public class RewriteArrays extends LassoPreProcessor {

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;

	private static final String s_RepInPostfix = "_in_array";
	private static final String s_RepOutPostfix = "_out_array";
	static final String s_AuxArray = "auxArray";

	/**
	 * The script used to transform the formula
	 */
	private Script m_Script;

	/**
	 * Collection of all generated replacement variables and the terms that they
	 * replace. These variables are *not* added to in- or outVars.
	 */
	private final Map<TermVariable, Term> m_repVars;

	/**
	 * The replacement terms for the replacement variables for the formula.
	 * These terms will be set in conjunction with the whole formula.
	 */
	private final Collection<Term> m_repTerms;
	
	/**
	 * Use assert statement to check if result is equivalent to the conjunction
	 * of input term and definition of replacement variables.
	 */
	private static final boolean s_CheckResult = true;
	/**
	 * Use assert statement to check if the input is equivalent to the formula
	 * that is obtained by existentially quantifying each replacement variable
	 * in the result term.
	 */
	private static final boolean s_CheckResultWithQuantifiers = false;
	
	private Map<TermVariable, Map<List<Term>, TermVariable>> m_ArrayInstance2Index2CellVariable;
	private SafeSubstitution m_Select2CellVariable[];

	private IndexAnalyzer m_IndexAnalyzer;

//	private final boolean m_SearchAdditionalSupportingInvariants;
	private final TransFormula m_OriginalStem;
	private final TransFormula m_OriginalLoop;

	private final Set<Term> m_ArrayIndexSupportingInvariants;
	private EquivalentCells[] m_EquivalentCells;

	private final boolean m_OverapproximateByOmmitingDisjointIndices;
	private TransFormulaLRWithArrayInformation tflrwai;

	public RewriteArrays(Set<Term> arrayIndexsupportingInvariants,
			boolean overapproximateByOmmitingDisjointIndices,
			TransFormula originalStem, TransFormula originalLoop,
			IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_repVars = new LinkedHashMap<TermVariable, Term>();
		m_repTerms = new ArrayList<Term>();
		m_OriginalStem = originalStem;
		m_OriginalLoop = originalLoop;
		m_ArrayIndexSupportingInvariants = arrayIndexsupportingInvariants;
		m_OverapproximateByOmmitingDisjointIndices = overapproximateByOmmitingDisjointIndices;
	}

	@Override
	public String getDescription() {
		return "Removes arrays by introducing new variables for each "
				+ "relevant array cell";
	}

	@Override
	public void process(LassoBuilder lasso_builder) 
			throws TermException {
		m_lassoBuilder = lasso_builder;
		m_Script = lasso_builder.getScript();
		
		// Process stem
		{
			Collection<TransFormulaLR> old_stem_components =
					lasso_builder.getStemComponents();
			Collection<TransFormulaLR> new_stem_components =
					new ArrayList<TransFormulaLR>(old_stem_components.size());
			for (TransFormulaLR tf : old_stem_components) {
				TransFormulaLR new_tf =
						this.process(m_Script, tf, true);
				assert checkSoundness(m_Script, tf, new_tf)
					: "Soundness check failed for preprocessor "
					+ this.getClass().getSimpleName();
				new_stem_components.add(new_tf);
			}
			lasso_builder.setStemComponents(new_stem_components);
		}
		
		// Process loop
		{
			Collection<TransFormulaLR> old_loop_components =
					lasso_builder.getLoopComponents();
			Collection<TransFormulaLR> new_loop_components =
					new ArrayList<TransFormulaLR>(old_loop_components.size());
			for (TransFormulaLR tf : old_loop_components) {
				TransFormulaLR new_tf =
						this.process(m_Script, tf, false);
				assert checkSoundness(m_Script, tf, new_tf)
					: "Soundness check failed for preprocessor "
					+ this.getClass().getSimpleName();
				new_loop_components.add(new_tf);
			}
			lasso_builder.setLoopComponents(new_loop_components);
		}
	}
	
	private TransFormulaLR process(Script script, TransFormulaLR tf,
			boolean stem) {
		Term term = tf.getFormula();
		if (!SmtUtils.containsArrayVariables(term)) {
			return tf;
		}
		tflrwai = 
				new TransFormulaLRWithArrayInformation(mServices, tf, m_lassoBuilder.getReplacementVarFactory(), m_Script);
		

		// Create a new TransFormula by copying the old one
		TransFormulaLR new_tf = new TransFormulaLR(tf);
		

		m_IndexAnalyzer = new IndexAnalyzer(term, tflrwai.getArrayFirstGeneration2Indices(), true, m_lassoBuilder.getBoogie2SMT(), tf, m_OriginalStem, m_OriginalLoop);
		m_ArrayIndexSupportingInvariants.addAll(m_IndexAnalyzer.getSupportingInvariants());
		CellVariableBuilder cvb = new CellVariableBuilder(new_tf);
		m_ArrayInstance2Index2CellVariable = cvb.getArrayInstance2Index2CellVariable();
		m_EquivalentCells = new EquivalentCells[tflrwai.numberOfDisjuncts()];
		for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
			m_EquivalentCells[i] = computeEquivalentCells(new_tf, tflrwai.getArrayEqualities().get(i), tflrwai.getArrayUpdates().get(i));
		}

		m_Select2CellVariable = new SafeSubstitution[tflrwai.numberOfDisjuncts()];
		for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
			m_Select2CellVariable[i] = constructIndex2CellVariableSubstitution(m_EquivalentCells[i], i);
		}

		Term[] arrayEqualityConstraints = new Term[tflrwai.numberOfDisjuncts()];
		for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
			arrayEqualityConstraints[i] = m_EquivalentCells[i].getInOutEqauality();
		}

		Term[] indexValueConstraints = new Term[tflrwai.numberOfDisjuncts()];
		for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
			indexValueConstraints[i] = buildIndexValueConstraints(m_Select2CellVariable[i], m_EquivalentCells[i]);
		}

		Term[] arrayUpdateConstraints = new Term[tflrwai.numberOfDisjuncts()];
		for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
			arrayUpdateConstraints[i] = buildArrayUpdateConstraints(tflrwai.getArrayUpdates().get(i), m_Select2CellVariable[i],
					m_EquivalentCells[i]);
		}
		Term[] disjunctsWithUpdateConstraints = new Term[tflrwai.numberOfDisjuncts()];
		for (int i = 0; i < disjunctsWithUpdateConstraints.length; i++) {
			Term removedSelect = m_Select2CellVariable[i].transform(tflrwai.getSunnf()[i]);
			Term[] conjuncts;
			if (m_OverapproximateByOmmitingDisjointIndices) {
				conjuncts = new Term[5];
			} else {
				conjuncts = new Term[6];
				conjuncts[5] = m_IndexAnalyzer.getAdditionalConjunctsNotEquals();
			}
			conjuncts[0] = removedSelect;
			conjuncts[1] = indexValueConstraints[i];
			conjuncts[2] = arrayUpdateConstraints[i];
			conjuncts[3] = arrayEqualityConstraints[i];
			conjuncts[4] = m_IndexAnalyzer.getAdditionalConjunctsEqualities();
			disjunctsWithUpdateConstraints[i] = Util.and(m_Script, conjuncts);
		}
		Term resultDisjuntion = Util.or(m_Script, disjunctsWithUpdateConstraints);

		Term result = PartialQuantifierElimination.elim(m_Script, QuantifiedFormula.EXISTS, cvb.getAuxVars(), resultDisjuntion, mServices, mLogger);
		
		assert SmtUtils.isArrayFree(result);
		result = SmtUtils.simplify(m_Script, result, mLogger);
		
		new_tf.setFormula(result);
		new_tf.addAuxVars(cvb.getAuxVars());
		return new_tf;
	}

	private EquivalentCells computeEquivalentCells(TransFormulaLR tf, List<ArrayEquality> arrayEqualities, List<ArrayUpdate> arrayUpdates) {
		UnionFind<TermVariable> uf = new UnionFind<TermVariable>();
		addArrayIndexConstraints(uf);
		addArrayEqualityConstraints(uf, arrayEqualities);
		addArrayUpdateConstraints(uf, arrayUpdates);
		return new EquivalentCells(uf, tf);
	}

	private void addArrayUpdateConstraints(UnionFind<TermVariable> uf, List<ArrayUpdate> arrayUpdates) {
		for (ArrayUpdate au : arrayUpdates) {
			List<Term> updateIndex = Arrays.asList(au.getIndex());
			Map<List<Term>, TermVariable> newInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(au
					.getNewArray());
			Map<List<Term>, TermVariable> oldInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(au
					.getOldArray());
			for (List<Term> index : newInstance2Index2CellVariable.keySet()) {
				TermVariable newCellVariable = newInstance2Index2CellVariable.get(index);
				TermVariable oldCellVariable = oldInstance2Index2CellVariable.get(index);
				Equality indexEquality = m_IndexAnalyzer.isEqual(index, updateIndex);
				switch (indexEquality) {
				case EQUAL:
					// do nothing
					break;
				case NOT_EQUAL:
					uf.union(newCellVariable, oldCellVariable);
					break;
				case UNKNOWN:
					// do nothing
				default:
					break;
				}
			}
		}
	}

	private void addArrayIndexConstraints(UnionFind<TermVariable> uf) {
		for (Entry<TermVariable, Map<List<Term>, TermVariable>> entry : m_ArrayInstance2Index2CellVariable.entrySet()) {
			Map<List<Term>, TermVariable> indices2values = entry.getValue();
			List<Term>[] indices = new List[indices2values.size()];
			TermVariable[] values = new TermVariable[indices2values.size()];
			int offset = 0;
			for (Entry<List<Term>, TermVariable> index2value : indices2values.entrySet()) {
				indices[offset] = index2value.getKey();
				TermVariable value = index2value.getValue();
				values[offset] = value;
				uf.makeEquivalenceClass(value);
				offset++;
			}
			for (int i = 0; i < indices2values.size(); i++) {
				for (int j = 0; j < i; j++) {
					List<Term> index1 = indices[i];
					List<Term> index2 = indices[j];
					if (m_IndexAnalyzer.isEqual(index1, index2) == Equality.EQUAL) {
						TermVariable value1 = values[i];
						TermVariable value2 = values[j];
						uf.union(value1, value2);
					}
				}
			}
		}

	}

	private void addArrayEqualityConstraints(UnionFind<TermVariable> uf, List<ArrayEquality> arrayEqualities) {
		for (ArrayEquality ae : arrayEqualities) {
			Map<List<Term>, TermVariable> lhsInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(ae
					.getLhs());
			Map<List<Term>, TermVariable> rhsInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(ae
					.getRhs());
			if (lhsInstance2Index2CellVariable == null && rhsInstance2Index2CellVariable == null) {
				// has no index at all
			}
			for (List<Term> index : lhsInstance2Index2CellVariable.keySet()) {
				TermVariable lhsCellVariable = lhsInstance2Index2CellVariable.get(index);
				TermVariable rhsCellVariable = rhsInstance2Index2CellVariable.get(index);
				uf.union(lhsCellVariable, rhsCellVariable);
			}
		}
	}

	private List<MultiDimensionalSelect> extractArrayReads(List<ArrayUpdate> arrayUpdates, Term remainderTerm) {
		ArrayList<MultiDimensionalSelect> result = new ArrayList<>();
		for (ArrayUpdate au : arrayUpdates) {
			for (Term indexEntry : au.getIndex()) {
				result.addAll(MultiDimensionalSelect.extractSelectDeep(indexEntry, true));
			}
			result.addAll(MultiDimensionalSelect.extractSelectDeep(au.getValue(), true));
		}
		result.addAll(MultiDimensionalSelect.extractSelectDeep(remainderTerm, true));
		return result;
	}

//	@Override
//	protected boolean checkSoundness(Script script, TransFormulaLR oldTF,
//			TransFormulaLR newTF) {
//		Term old_term = oldTF.getFormula();
//		Term new_term = newTF.getFormula();
//		boolean check1 = !s_CheckResult || !isIncorrect(old_term, new_term);
//		boolean check2 = !s_CheckResultWithQuantifiers
//				|| !isIncorrectWithQuantifiers(script, old_term, new_term);
//		return check1 && check2;
//	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect. For
	 * this check we add to the input term the definition of the replacement
	 * variables.
	 */
	private boolean isIncorrect(Term input, Term result, Term repTerm) {
		Term inputWithDefinitions = m_Script.term("and", input, repTerm);
		return LBool.SAT == Util.checkSat(m_Script, m_Script.term("distinct", inputWithDefinitions, result));
	}

	/**
	 * Return true if we were able to prove that the result is incorrect. For
	 * this check we existentially quantify replacement variables in the result
	 * term.
	 */
	private boolean isIncorrectWithQuantifiers(Term input, Term result, Term repTerm) {
		Term quantified;
		if (m_repVars.size() > 0) {
			quantified = m_Script.quantifier(Script.EXISTS, m_repVars.keySet().toArray(new TermVariable[0]), result);
		} else {
			quantified = m_Script.term("true");
		}
		return Util.checkSat(m_Script, m_Script.term("distinct", input, quantified)) == LBool.SAT;
	}

	// private List<MultiDimensionalStore> extractArrayStores(Term term) {
	// List<MultiDimensionalStore> foundInThisIteration = new
	// ArrayList<MultiDimensionalStore>();
	// Set<ApplicationTerm> storeTerms =
	// (new ApplicationTermFinder("store", false)).findMatchingSubterms(term);
	// for (Term storeTerm : storeTerms) {
	// MultiDimensionalStore asd;
	// try {
	// asd = new MultiDimensionalStore(storeTerm);
	// } catch (ArrayStoreException e) {
	// throw new UnsupportedOperationException("unexpected store term");
	// }
	// foundInThisIteration.add(asd);
	// }
	// List<MultiDimensionalStore> result = new
	// LinkedList<MultiDimensionalStore>();
	// while (!foundInThisIteration.isEmpty()) {
	// result.addAll(0, foundInThisIteration);
	// List<MultiDimensionalStore> foundInLastIteration = foundInThisIteration;
	// foundInThisIteration = new ArrayList<MultiDimensionalStore>();
	// for (MultiDimensionalStore asd : foundInLastIteration) {
	// storeTerms =
	// (new ApplicationTermFinder("store",
	// false)).findMatchingSubterms(asd.getArray());
	// for (Term storeTerm : storeTerms) {
	// MultiDimensionalStore newAsd;
	// try {
	// newAsd = new MultiDimensionalStore(storeTerm);
	// } catch (ArrayStoreException e) {
	// throw new UnsupportedOperationException("unexpected store term");
	// }
	// foundInThisIteration.add(newAsd);
	// }
	// }
	// }
	// return result;
	// }
	private class CellVariableBuilder {
		private Map<TermVariable, Map<List<Term>, TermVariable>> m_ArrayInstance2Index2CellVariable;
		private Map<TermVariable, Map<List<Term>, ReplacementVar>> m_Array2Index2RepVar;
		private Set<TermVariable> m_AuxVars = new HashSet<TermVariable>();
		private final TransFormulaLR m_TransFormula;

		public CellVariableBuilder(TransFormulaLR tf) {
			m_TransFormula = tf;
			m_ArrayInstance2Index2CellVariable = new HashMap<TermVariable, Map<List<Term>, TermVariable>>();
			m_Array2Index2RepVar = new HashMap<TermVariable, Map<List<Term>, ReplacementVar>>();
			dotSomething();
		}

		/**
		 * Returns a getOrConstructReplacementVar that will represent the array
		 * cell array[index].
		 */
		private ReplacementVar getOrConstructReplacementVar(TermVariable array, List<Term> index) {
			List<Term> translatedIndex = Arrays.asList(translateTermVariablesToDefinitions(m_Script, m_TransFormula,
					index.toArray(new Term[0])));
			Map<List<Term>, ReplacementVar> index2repVar = m_Array2Index2RepVar.get(array);
			if (index2repVar == null) {
				index2repVar = new HashMap<List<Term>, ReplacementVar>();
				m_Array2Index2RepVar.put(array, index2repVar);
			}
			ReplacementVar repVar = index2repVar.get(translatedIndex);
			
			// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
			// TODO @Matthias: Please look at the following code
			
			// old code:
//			if (repVar == null) {
//				VarFactory fac = m_VarCollector.getFactory();
//				String name = getArrayCellName(array, translatedIndex);
//				repVar = fac.getRepVar(name);
//				if (repVar == null) {
//					Term definition = SmtUtils.multiDimensionalSelect(m_Script, array,
//							translatedIndex.toArray(new Term[0]));
//					repVar = fac.registerRepVar(name, definition);
//				}
//				index2repVar.put(translatedIndex, repVar);
//			}
			
			// new code:
			if (repVar == null) {
//				String name = getArrayCellName(array, translatedIndex);
				Term definition = SmtUtils.multiDimensionalSelect(m_Script, array, translatedIndex.toArray(new Term[0]));
				repVar = m_lassoBuilder.getReplacementVarFactory().getOrConstuctReplacementVar(definition);
				index2repVar.put(translatedIndex, repVar);
			}
			// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
			
			return repVar;
		}

		/**
		 * Returns a String that we use to refer to the array cell array[index].
		 */
		private String getArrayCellName(TermVariable array, List<Term> index) {
			return "arrayCell_" + SmtUtils.removeSmtQuoteCharacters(array.toString())
					+ SmtUtils.removeSmtQuoteCharacters(index.toString());
		}

		public void dotSomething() {
			for (TermVariable firstGeneration : tflrwai.getArrayFirstGeneration2Instances().getDomain()) {
				for (TermVariable instance : tflrwai.getArrayFirstGeneration2Instances().getImage(firstGeneration)) {
					Map<List<Term>, TermVariable> index2ArrayCellTv = m_ArrayInstance2Index2CellVariable.get(instance);
					if (index2ArrayCellTv == null) {
						index2ArrayCellTv = new HashMap<List<Term>, TermVariable>();
						m_ArrayInstance2Index2CellVariable.put(instance, index2ArrayCellTv);
					}
					Set<List<Term>> indicesOfOriginalGeneration = tflrwai.getArrayFirstGeneration2Indices().getImage(firstGeneration);
					if (indicesOfOriginalGeneration == null) {
						mLogger.info("Array " + firstGeneration + " is never accessed");
						continue;
					}
					for (List<Term> index : indicesOfOriginalGeneration) {
						TermVariable tv = index2ArrayCellTv.get(index);
						if (tv == null) {
							tv = constructTermVariable(instance, index);
							index2ArrayCellTv.put(index, tv);
						}
						boolean isInVarCell = isInVarCell(instance, index);
						boolean isOutVarCell = isOutVarCell(instance, index);
						if (isInVarCell || isOutVarCell) {
							TermVariable arrayRepresentative = (TermVariable) getDefinition(m_TransFormula, instance);
							ReplacementVar rv = getOrConstructReplacementVar(arrayRepresentative, index);
							if (isInVarCell) {
								if (!m_TransFormula.getInVars().containsKey(rv)) {
									m_TransFormula.addInVar(rv, tv);
								} else {
									assert m_TransFormula.getInVars().get(rv) == tv;
								}
							}
							if (isOutVarCell) {
								if (!m_TransFormula.getOutVars().containsKey(rv)) {
									m_TransFormula.addOutVar(rv, tv);
								} else {
									assert m_TransFormula.getOutVars().get(rv) == tv;
								}
							}
						} else {
							addToAuxVars(tv);
						}
					}

				}
			}
		}

		private void addToAuxVars(TermVariable tv) {
			m_AuxVars.add(tv);
			// assert false : "not yet implemented";
		}

		private TermVariable constructTermVariable(TermVariable instance, List<Term> index) {
			Sort arraySort = instance.getSort();
			assert arraySort.isArraySort();
			MultiDimensionalSort mdias = new MultiDimensionalSort(arraySort);
			assert mdias.getDimension() == index.size();
			Sort valueSort = mdias.getArrayValueSort();
			String name = getArrayCellName(instance, index);
			TermVariable tv = m_lassoBuilder.getReplacementVarFactory().
					getOrConstructAuxVar(name, valueSort);
			return tv;
		}

		/**
		 * Is the cellVariable that we construct for arrayInstance[index] is an
		 * inVar. This is the case if arrayInstance and each free variable of
		 * index is an inVar.
		 */
		private boolean isInVarCell(TermVariable arrayInstance, List<Term> index) {
			if (isInvar(arrayInstance, m_TransFormula)) {
				return allVariablesAreInVars(index, m_TransFormula);
			} else {
				return false;
			}
		}

		private boolean isOutVarCell(TermVariable arrayInstance, List<Term> index) {
			if (isOutvar(arrayInstance, m_TransFormula)) {
				return allVariablesAreOutVars(index, m_TransFormula);
			} else {
				return false;
			}
		}

		public Map<TermVariable, Map<List<Term>, TermVariable>> getArrayInstance2Index2CellVariable() {
			return m_ArrayInstance2Index2CellVariable;
		}

		public Set<TermVariable> getAuxVars() {
			return m_AuxVars;
		}

	}

	public class EquivalentCells {
		private final UnionFind<TermVariable> m_UnionFind;
		private final Map<TermVariable, TermVariable> m_Representative;
		private final Term m_InOutEqauality;
		private final TransFormulaLR m_TransFormula;

		public EquivalentCells(UnionFind<TermVariable> unionFind, TransFormulaLR tf) {
			m_TransFormula = tf;
			m_UnionFind = unionFind;
			m_Representative = computeRepresentatives(unionFind);
			m_InOutEqauality = computeInOutEqualities(unionFind);
		}

		private Term computeInOutEqualities(UnionFind<TermVariable> unionFind) {
			List<Term> conjuncts = new ArrayList<Term>();
			for (TermVariable representative : unionFind.getAllRepresentatives()) {
				List<TermVariable> equalInOutVars = new ArrayList<TermVariable>();
				for (TermVariable member : unionFind.getEquivalenceClassMembers(representative)) {
					if (isInvar(member, m_TransFormula) || isOutvar(member, m_TransFormula)) {
						equalInOutVars.add(member);
					}
				}
				if (equalInOutVars.size() > 1) {
					Term equality = m_Script.term("=", equalInOutVars.toArray(new Term[equalInOutVars.size()]));
					Term binarized = SmtUtils.binarize(m_Script, (ApplicationTerm) equality);
					conjuncts.add(binarized);
				}
			}
			return Util.and(m_Script, conjuncts.toArray(new Term[conjuncts.size()]));
		}

		private Map<TermVariable, TermVariable> computeRepresentatives(UnionFind<TermVariable> uf) {
			Map<TermVariable, TermVariable> result = new HashMap<TermVariable, TermVariable>();
			for (TermVariable ufRepresentative : uf.getAllRepresentatives()) {
				TermVariable inoutRepresentative = computeInOutRepresentative(uf, ufRepresentative);
				result.put(ufRepresentative, inoutRepresentative);
			}
			return result;
		}

		private TermVariable computeInOutRepresentative(UnionFind<TermVariable> uf, TermVariable ufRepresentative) {
			Set<TermVariable> eq = uf.getEquivalenceClassMembers(ufRepresentative);
			for (TermVariable member : eq) {
				if (isInvar(member, m_TransFormula) || isOutvar(member, m_TransFormula)) {
					return member;
				}
			}
			return ufRepresentative;
		}

		public Term getInOutEqauality() {
			return m_InOutEqauality;
		}

		public TermVariable getInOutRepresentative(TermVariable arrayCell) {
			TermVariable ufRepresentative = m_UnionFind.find(arrayCell);
			return m_Representative.get(ufRepresentative);
		}

	}

	private static boolean allVariablesAreInVars(List<Term> terms, TransFormulaLR tf) {
		for (Term term : terms) {
			if (!allVariablesAreInVars(term, tf)) {
				return false;
			}
		}
		return true;
	}

	private static boolean allVariablesAreOutVars(List<Term> terms, TransFormulaLR tf) {
		for (Term term : terms) {
			if (!allVariablesAreOutVars(term, tf)) {
				return false;
			}
		}
		return true;
	}

	public static boolean allVariablesAreInVars(Term term, TransFormulaLR tf) {
		for (TermVariable tv : term.getFreeVars()) {
			if (!isInvar(tv, tf)) {
				return false;
			}
		}
		return true;
	}

	private static boolean allVariablesAreOutVars(Term term, TransFormulaLR tf) {
		for (TermVariable tv : term.getFreeVars()) {
			if (!isOutvar(tv, tf)) {
				return false;
			}
		}
		return true;
	}

	public static Term getDefinition(TransFormulaLR tf, TermVariable tv) {
		RankVar rv = tf.getInVarsReverseMapping().get(tv);
		if (rv == null) {
			rv = tf.getOutVarsReverseMapping().get(tv);
		}
		if (rv == null) {
			throw new AssertionError();
		}
		return rv.getDefinition();
	}

	public static Term[] translateTermVariablesToDefinitions(Script script, TransFormulaLR tf, Term... terms) {
		Term[] result = new Term[terms.length];
		for (int i = 0; i < terms.length; i++) {
			Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (TermVariable tv : terms[i].getFreeVars()) {
				Term definition = getDefinition(tf, tv);
				substitutionMapping.put(tv, definition);
			}
			result[i] = (new SafeSubstitution(script, substitutionMapping)).transform(terms[i]);
		}
		return result;
	}

	private static boolean isInvar(TermVariable tv, TransFormulaLR tf) {
		return tf.getInVarsReverseMapping().keySet().contains(tv);
	}

	private static boolean isOutvar(TermVariable tv, TransFormulaLR tf) {
		return tf.getOutVarsReverseMapping().keySet().contains(tv);
	}

	private Term buildArrayEqualityConstraints(List<ArrayEquality> arrayEqualities) {
		Term[] conjuncts = new Term[arrayEqualities.size()];
		int offset = 0;
		for (ArrayEquality ae : arrayEqualities) {
			conjuncts[offset] = buildArrayEqualityConstraints(ae.getLhs(), ae.getRhs());
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}

	private Term buildArrayEqualityConstraints(TermVariable oldArray, TermVariable newArray) {
		Map<List<Term>, TermVariable> newInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(newArray);
		Map<List<Term>, TermVariable> oldInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(oldArray);
		if (newInstance2Index2CellVariable == null && oldInstance2Index2CellVariable == null) {
			return m_Script.term("true");
		}
		Term[] conjuncts = new Term[newInstance2Index2CellVariable.keySet().size()];
		int offset = 0;
		for (List<Term> index : newInstance2Index2CellVariable.keySet()) {
			Term newCellVariable = newInstance2Index2CellVariable.get(index);
			Term oldCellVariable = oldInstance2Index2CellVariable.get(index);
			conjuncts[offset] = SmtUtils.binaryEquality(m_Script, oldCellVariable, newCellVariable);
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}

	private Term buildArrayUpdateConstraints(List<ArrayUpdate> arrayUpdates, SafeSubstitution select2CellVariable,
			EquivalentCells equivalentCells) {
		Term[] conjuncts = new Term[arrayUpdates.size()];
		int offset = 0;
		for (ArrayUpdate au : arrayUpdates) {
			conjuncts[offset] = buildArrayUpdateConstraints(au.getNewArray(), au.getOldArray(), au.getIndex(),
					au.getValue(), select2CellVariable, equivalentCells);
			offset++;
		}
		Term result = Util.and(m_Script, conjuncts);
		assert (new ApplicationTermFinder("select", false)).findMatchingSubterms(result).isEmpty() : "contains select terms";
		return result;
	}

	private Term buildArrayUpdateConstraints(TermVariable newArray, TermVariable oldArray, Term[] updateIndex,
			Term data, SafeSubstitution select2CellVariable, EquivalentCells equivalentCells) {
		data = select2CellVariable.transform(data);
		Map<List<Term>, TermVariable> newInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(newArray);
		Map<List<Term>, TermVariable> oldInstance2Index2CellVariable = m_ArrayInstance2Index2CellVariable.get(oldArray);
		Term[] conjuncts = new Term[newInstance2Index2CellVariable.keySet().size()];
		int offset = 0;
		for (List<Term> index : newInstance2Index2CellVariable.keySet()) {
			TermVariable newCellVariable = newInstance2Index2CellVariable.get(index);
			newCellVariable = equivalentCells.getInOutRepresentative(newCellVariable);
			TermVariable oldCellVariable = oldInstance2Index2CellVariable.get(index);
			oldCellVariable = equivalentCells.getInOutRepresentative(oldCellVariable);
			Term indexIsUpdateIndex = pairwiseEqualityExploitDoubletons(index, Arrays.asList(updateIndex),
					select2CellVariable);
			Term newDataIsUpdateData = SmtUtils.binaryEquality(m_Script, newCellVariable, data);
			Term newDateIsOldData = SmtUtils.binaryEquality(m_Script, newCellVariable, oldCellVariable);
			Term indexIsNotUpdateIndex = Util.not(m_Script, indexIsUpdateIndex);
			Term indexIsUpdateIndexImpliesUpdateData = Util.or(m_Script, indexIsNotUpdateIndex, newDataIsUpdateData);
			Term indexIsNotUpdateIndexImpliesOldData = Util.or(m_Script, indexIsUpdateIndex, newDateIsOldData);
			conjuncts[offset] = Util.and(m_Script, indexIsUpdateIndexImpliesUpdateData,
					indexIsNotUpdateIndexImpliesOldData);
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}

	private Term buildIndexValueConstraints(SafeSubstitution select2CellVariable, EquivalentCells equivalentCells) {
		Term[] conjuncts = new Term[m_ArrayInstance2Index2CellVariable.size()];
		int offset = 0;
		for (Entry<TermVariable, Map<List<Term>, TermVariable>> entry : m_ArrayInstance2Index2CellVariable.entrySet()) {
			Map<List<Term>, TermVariable> indices2values = entry.getValue();
			conjuncts[offset] = buildIndexValueConstraints(indices2values, select2CellVariable, equivalentCells);
			offset++;
		}
		return Util.and(m_Script, conjuncts);
	}

	private Term buildIndexValueConstraints(Map<List<Term>, TermVariable> indices2values,
			SafeSubstitution select2CellVariable, EquivalentCells equivalentCells) {
		List<Term>[] indices = new List[indices2values.size()];
		TermVariable[] values = new TermVariable[indices2values.size()];
		int offset = 0;
		for (Entry<List<Term>, TermVariable> index2value : indices2values.entrySet()) {
			indices[offset] = index2value.getKey();
			values[offset] = index2value.getValue();
			offset++;
		}
		int numberOfPairs = indices2values.size() * (indices2values.size() - 1) / 2;
		Term[] conjuncts = new Term[numberOfPairs];
		int k = 0;
		for (int i = 0; i < indices2values.size(); i++) {
			for (int j = 0; j < i; j++) {
				List<Term> index1 = indices[i];
				List<Term> index2 = indices[j];
				TermVariable value1 = values[i];
				TermVariable value2 = values[j];
				TermVariable value1Representative = equivalentCells.getInOutRepresentative(value1);
				TermVariable value2Representative = equivalentCells.getInOutRepresentative(value2);
				conjuncts[k] = indexEqualityImpliesValueEquality(index1, index2, value1Representative,
						value2Representative, select2CellVariable);
				k++;
			}
		}
		Term result = Util.and(m_Script, conjuncts);
		return result;
	}

	private Term indexEqualityImpliesValueEquality(List<Term> index1, List<Term> index2, Term value1, Term value2,
			SafeSubstitution select2CellVariable) {
		Term indexEquality = pairwiseEqualityExploitDoubletons(index1, index2, select2CellVariable);
		Term valueEquality = SmtUtils.binaryEquality(m_Script, value1, value2);
		return Util.or(m_Script, Util.not(m_Script, indexEquality), valueEquality);
	}

	Term pairwiseEqualityExploitDoubletons(List<Term> index1, List<Term> index2, SafeSubstitution select2CellVariable) {
		assert index1.size() == index2.size();
		Term[] conjuncts = new Term[index1.size()];
		for (int i = 0; i < index1.size(); i++) {
			Term fst = index1.get(i);
			Term snd = index2.get(i);
			if (fst == snd || m_IndexAnalyzer.isEqualDoubleton(fst, snd)) {
				conjuncts[i] = m_Script.term("true");
			} else if (m_IndexAnalyzer.isDistinctDoubleton(fst, snd)) {
				conjuncts[i] = m_Script.term("false");
			} else if (m_IndexAnalyzer.isUnknownDoubleton(fst, snd)) {
				Term fstSubst = select2CellVariable.transform(fst);
				Term sndSubst = select2CellVariable.transform(snd);
				conjuncts[i] = SmtUtils.binaryEquality(m_Script, fstSubst, sndSubst);
			} else {
				throw new AssertionError("unknown doubleton");
			}
		}
		return Util.and(m_Script, conjuncts);
	}

	/**
	 * Replace all select terms by the corresponding cell variables.
	 */
	private SafeSubstitution constructIndex2CellVariableSubstitution(EquivalentCells ec, int i) {
		Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (MultiDimensionalSelect ar : tflrwai.getArrayReads().get(i)) {
			TermVariable cellVariable = m_ArrayInstance2Index2CellVariable.get(ar.getArray()).get(
					Arrays.asList(ar.getIndex()));
			Term inOutRepresentative = ec.getInOutRepresentative(cellVariable);
			substitutionMapping.put(ar.getSelectTerm(), inOutRepresentative);
		}

		for (MultiDimensionalSelect ar : tflrwai.getAdditionalArrayReads()) {
			TermVariable cellVariable = m_ArrayInstance2Index2CellVariable.get(ar.getArray()).get(
					Arrays.asList(ar.getIndex()));
			Term inOutRepresentative = ec.getInOutRepresentative(cellVariable);
			substitutionMapping.put(ar.getSelectTerm(), inOutRepresentative);
		}
		return new SafeSubstitution(m_Script, substitutionMapping);
	}

	/**
	 * Replace all select terms by the corresponding cell variables.
	 */
	private SafeSubstitution constructIndex2CellVariableSubstitution() {
		Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (int i = 0; i < tflrwai.numberOfDisjuncts(); i++) {
			for (MultiDimensionalSelect ar : tflrwai.getArrayReads().get(i)) {
				Term cellVariable = m_ArrayInstance2Index2CellVariable.get(ar.getArray()).get(
						Arrays.asList(ar.getIndex()));
				substitutionMapping.put(ar.getSelectTerm(), cellVariable);
			}
		}
		for (MultiDimensionalSelect ar : tflrwai.getAdditionalArrayReads()) {
			Term cellVariable = m_ArrayInstance2Index2CellVariable.get(ar.getArray()).get(Arrays.asList(ar.getIndex()));
			substitutionMapping.put(ar.getSelectTerm(), cellVariable);
		}
		return new SafeSubstitution(m_Script, substitutionMapping);
	}


}