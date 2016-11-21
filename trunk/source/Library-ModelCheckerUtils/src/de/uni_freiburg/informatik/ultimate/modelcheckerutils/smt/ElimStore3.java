/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.EqualityInformation;

/**
 * 
 * TODO: - elimination and output of remaining vars - nested store - storeTo and
 * storeFrom (LBE) - index equality testing - documentation
 * 
 * @author Matthias Heizmann
 * 
 */
public class ElimStore3 {

	private int mQuantifier;
	private final Script mScript;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final static String s_FreshVariableString = "arrayElim";

	public ElimStore3(final Script script, 
			final ManagedScript mgdScript, 
			final IUltimateServiceProvider services, 
			final SimplificationTechnique simplificationTechnique) {
		super();
		mQuantifier = QuantifiedFormula.EXISTS;
		mScript = script;
		mMgdScript = mgdScript;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
	}

	private MultiDimensionalStore getArrayStore(final Term array, final Term term) {
		final List<MultiDimensionalStore> all = MultiDimensionalStore.extractArrayStoresDeep(term);
		MultiDimensionalStore result = null;
		for (final MultiDimensionalStore asd : all) {
			if (asd.getArray().equals(array)) {
				if (result != null && !result.equals(asd)) {
					throw new UnsupportedOperationException("unsupported: several stores");
				} else {
					result = asd;
				}
			}
		}
		return result;
	}
	
	private ArrayUpdate getArrayUpdate(final Term array, final Term[] terms) {
		final ArrayUpdateExtractor aue = new ArrayUpdateExtractor(mQuantifier == QuantifiedFormula.FORALL, true, terms);
		ArrayUpdate result = null;
		for (final ArrayUpdate au : aue.getArrayUpdates()) {
			if (au.getNewArray().equals(array)) {
				if (result != null && !result.equals(au)) {
					throw new UnsupportedOperationException("unsupported: several updates");
				} else {
					result = au;
				}
			}
		}
		return result;
	}

	// private ArrayStoreDef getArrayStore(Term array, Term term) {
	// Set<ApplicationTerm> storeTerms =
	// (new ApplicationTermFinder("store", true)).findMatchingSubterms(term);
	// ArrayStoreDef result = null;
	// for (Term storeTerm : storeTerms) {
	// ArrayStoreDef asd;
	// try {
	// asd = new ArrayStoreDef(storeTerm);
	// } catch (MultiDimensionalSelect.ArrayReadException e) {
	// throw new UnsupportedOperationException("unexpected store term");
	// }
	// if (asd.getArray().equals(array)) {
	// if (result != null) {
	// throw new UnsupportedOperationException("unsupported: several stores");
	// } else {
	// result = asd;
	// }
	// }
	// }
	// return result;
	// }

	public Term elim(final int quantifier, TermVariable eliminatee, Term term, final Set<TermVariable> newAuxVars) {
		mQuantifier = quantifier;
		ArrayUpdate writeInto = null;
		ArrayUpdate writtenFrom = null;
		Term[] conjuncts;
		Term othersT;
		
		term = eliminateSelfUpdates(mScript, quantifier, term);

		while (true) {
			assert eliminatee.getSort().isArraySort();

			if (quantifier == QuantifiedFormula.EXISTS) {
				conjuncts = SmtUtils.getConjuncts(term);
			} else {
				assert quantifier == QuantifiedFormula.FORALL;
				conjuncts = SmtUtils.getDisjuncts(term);
			}
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(this.getClass(),
						"eliminating quantified array variable from " + conjuncts.length + " xjuncts");
			}

			MultiDimensionalStore store = getArrayStore(eliminatee, term);
			final ArrayUpdate update = getArrayUpdate(eliminatee, conjuncts);

			final HashSet<Term> others = new HashSet<Term>();

			for (final Term conjunct : conjuncts) {
				try {
					final ArrayUpdate au = new ArrayUpdate(conjunct, quantifier == QuantifiedFormula.FORALL, false);
					if (au.getOldArray().equals(eliminatee)) {
						if (writeInto != null) {
							throw new UnsupportedOperationException("unsupported: write into several arrays");
						}
						writeInto = au;
						if (au.getNewArray().equals(eliminatee)) {
							throw new UnsupportedOperationException("unsupported: self update");
						}
					} else if (au.getNewArray().equals(eliminatee)) {
						if (writtenFrom != null) {
							throw new UnsupportedOperationException("unsupported: written from several arrayas");
						}
						writtenFrom = au;
					} else {
						others.add(conjunct);
					}
				} catch (final ArrayUpdateException e) {
					others.add(conjunct);
				}
			}
			// if both are available we take the writtenFrom
			if (writtenFrom != null && writeInto != null) {
				others.add(writeInto.getArrayUpdateTerm());
				writeInto = null;
			}

			if (quantifier == QuantifiedFormula.EXISTS) {
				othersT = Util.and(mScript, others.toArray(new Term[others.size()]));
			} else {
				assert quantifier == QuantifiedFormula.FORALL;
				othersT = Util.or(mScript, others.toArray(new Term[others.size()]));
			}
			


			if ((store != null || update != null) && (writeInto == null && writtenFrom == null)) {
				final TermVariable auxArray = mMgdScript.constructFreshTermVariable(s_FreshVariableString, eliminatee.getSort()); 
				if (store == null) {
					store = update.getMultiDimensionalStore();
				}
				final Map<Term, Term> auxMap = Collections.singletonMap((Term) store.getStoreTerm(), (Term) auxArray);
				final Substitution subst = new SubstitutionWithLocalSimplification(mMgdScript, auxMap);
				Term auxTerm = subst.transform(term);
				final Term auxVarDef = mScript.term("=", auxArray, store.getStoreTerm());
				if (quantifier == QuantifiedFormula.EXISTS) {
					auxTerm = Util.and(mScript, auxTerm, auxVarDef);
				} else {
					assert quantifier == QuantifiedFormula.FORALL;
					auxTerm = Util.or(mScript, auxTerm, SmtUtils.not(mScript, auxVarDef));
				}
				final Set<TermVariable> auxAuxVars = new HashSet<TermVariable>();
				final Term auxRes = elim(quantifier, eliminatee, auxTerm, newAuxVars);

				term = auxRes;
				eliminatee = auxArray;
				newAuxVars.addAll(auxAuxVars);
			} else {
				break;
			}
		}

		final boolean write = (writeInto != null || writtenFrom != null);

		final Script script = mScript;
		
		Term intermediateResult = othersT;
		if (writeInto != null) {
			// if update is of form (store oldArr idx val) = newArr,
			// we replace all occurrences of (store oldArr idx val) by newArr.
			final Map<Term, Term> mapping = Collections.singletonMap(
					(Term) writeInto.getMultiDimensionalStore().getStoreTerm(), (Term) writeInto.getNewArray());
			final Substitution substStoreTerm = new SubstitutionWithLocalSimplification(mMgdScript, mapping);
			intermediateResult = substStoreTerm.transform(intermediateResult);
		}
		
		// Indices and corresponding values of a_elim 
		final IndicesAndValues iav = new IndicesAndValues(eliminatee, conjuncts);
		final Substitution subst = new SubstitutionWithLocalSimplification(mMgdScript, iav.getMapping());

		final ArrayList<Term> additionalConjuncs = new ArrayList<Term>();
		intermediateResult = subst.transform(intermediateResult);
		
		if (writtenFrom == null && Arrays.asList(intermediateResult.getFreeVars()).contains(eliminatee)) {
			throw new AssertionError("var is still there " + eliminatee + "  quantifier " + quantifier + "  term size " + (new DagSizePrinter(term)) + "   " + term);
		}
		if (write) {
			Term a_heir;
			ArrayIndex idx_write;
			Term data;
			if (writeInto != null) {
				a_heir = writeInto.getNewArray();
				idx_write = writeInto.getIndex();
				data = writeInto.getValue();
			} else {
				assert writtenFrom != null;
				a_heir = writtenFrom.getOldArray();
				idx_write = writtenFrom.getIndex();
				data = writtenFrom.getValue();
			}
			additionalConjuncs.addAll(disjointIndexImpliesValueEquality(quantifier, a_heir, idx_write, iav, subst, eliminatee));
			final ArrayIndex idx_writeRenamed = new ArrayIndex(SmtUtils.substitutionElementwise(idx_write, subst));
			final Term dataRenamed = subst.transform(data);
			if (writeInto != null) {
				assert writeInto.getOldArray() == eliminatee : "array not eliminatee";
				// if store is of the form
				// a_heir == store(a_elim, idx_write, data)
				// construct term a_heir[idx_write] == data
				Term writtenCellHasNewValue;
				writtenCellHasNewValue = mScript.term("=",
						SmtUtils.multiDimensionalSelect(mScript, a_heir, idx_writeRenamed), dataRenamed);
				assert !Arrays.asList(writtenCellHasNewValue.getFreeVars()).contains(eliminatee) : "var is still there";
				additionalConjuncs.add(writtenCellHasNewValue);
			}
			
			/**
			 * Special treatment for the case that the eliminatee to which we
			 * write occurs also in a term somewhere else (which is not a
			 * select term). Maybe we can avoid this if we eliminate variables
			 * in a certain order. 
			 */
			final Substitution writtenFromSubst;
			if (writtenFrom != null) {
				final Term storeRenamed = SmtUtils.multiDimensionalStore(script, a_heir, idx_writeRenamed, dataRenamed);
				final Map<Term, Term> mapping = Collections.singletonMap((Term) eliminatee, storeRenamed);
				writtenFromSubst = new SubstitutionWithLocalSimplification(mMgdScript, mapping);
			} else {
				writtenFromSubst = null;
			}
			
			if (quantifier == QuantifiedFormula.EXISTS) {
				final Term additionalConjuncts = Util.and(script, additionalConjuncs.toArray(new Term[additionalConjuncs.size()])); 
				intermediateResult = Util.and(script, intermediateResult, additionalConjuncts); 
			} else {
				assert quantifier == QuantifiedFormula.FORALL;
				final Term additionalConjuncts = Util.or(script, SmtUtils.negateElementwise(mScript, additionalConjuncs).toArray(new Term[additionalConjuncs.size()])); 
				intermediateResult = Util.or(script, intermediateResult, additionalConjuncts); 
			}
			
			if (writtenFromSubst != null) {
				intermediateResult = writtenFromSubst.transform(intermediateResult); 
			}
		}

		final ArrayList<Term> indexValueConstraintsFromEliminatee = new ArrayList<Term>();
		{
			final List<ArrayIndex> indices = new ArrayList<ArrayIndex>();
			final List<Term> values = new ArrayList<Term>();
			for (int i=0; i<iav.getIndices().length; i++) {
				final ArrayIndex translatedIndex = new ArrayIndex(SmtUtils.substitutionElementwise(iav.getIndices()[i], subst));
				final Term translatedValue = subst.transform(iav.getValues()[i]);
				indices.add(translatedIndex);
				values.add(translatedValue);
			}
			
			
			if (writtenFrom != null) {
				assert writtenFrom.getNewArray() == eliminatee : "array not eliminatee";
				// in the writtenFrom case there is an additional index-value
				// connection on eliminatee, namely
				// that the stored data is the value at index idx_write
				final ArrayIndex idx_writeRenamed = new ArrayIndex(SmtUtils.substitutionElementwise(writtenFrom.getIndex(), subst));
				final Term dataRenamed = subst.transform(writtenFrom.getValue());
				indices.add(idx_writeRenamed);
				values.add(dataRenamed);
			}

			for (int i = 0; i < indices.size(); i++) {
				for (int j = i; j < indices.size(); j++) {
					final Term newConjunct = SmtUtils.indexEqualityImpliesValueEquality(
							mScript, indices.get(i), indices.get(j), values.get(i), values.get(j));
					assert !Arrays.asList(newConjunct.getFreeVars()).contains(eliminatee) : "var is still there";
					indexValueConstraintsFromEliminatee.add(newConjunct);
				}
			}
		}
		
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			final Term newConjunctsFromSelect = Util.and(mScript, indexValueConstraintsFromEliminatee.toArray(new Term[indexValueConstraintsFromEliminatee.size()]));
			result = Util.and(script, intermediateResult, newConjunctsFromSelect);
		} else {
			assert quantifier == QuantifiedFormula.FORALL;
			final Term newConjunctsFromSelect = Util.or(mScript, SmtUtils.negateElementwise(mScript, indexValueConstraintsFromEliminatee).toArray(new Term[indexValueConstraintsFromEliminatee.size()]));
			result = Util.or(script, intermediateResult, newConjunctsFromSelect);
		}

		result = SmtUtils.simplify(mMgdScript, result, mServices, mSimplificationTechnique);
		newAuxVars.addAll(iav.getNewAuxVars());

		return result;
	}

	
	/**
	 * let idx_write be the index to which the store writes
	 * let k_1,...,k_n be indices of the eliminated array
	 * let v_1,...,v_n be terms that are equivalent to the corresponding
	 * values of the eliminated array (i.e. v_i is equivalent to a_elim[k_i]
	 * add for each i the conjunct
	 * (idx_write != k_i) ==> (v_i == a_heir[i])
	 * 
	 * Says that for each index that is different from the write index the
	 * arrayCells of a_heir have the same values than the arrayCells of
	 * a_elim
	 * @param subst 
	 * @param eliminatee 
	 */
	private ArrayList<Term> disjointIndexImpliesValueEquality(final int quantifier,
			final Term a_heir, final ArrayIndex idx_write, final IndicesAndValues iav, final Substitution subst, final TermVariable eliminatee) {
		final ArrayList<Term> result = new ArrayList<Term>();
		for (int i = 0; i < iav.getIndices().length; i++) {
			// select term that represents the array cell a[]
			final Term selectOnHeir = SmtUtils.multiDimensionalSelect(mScript, a_heir, iav.getIndices()[i]);
			final IndexValueConnection ivc = new IndexValueConnection(iav.getIndices()[i], idx_write,
					iav.getValues()[i], selectOnHeir, false);
			Term conjunct = ivc.getTerm();
			conjunct = subst.transform(conjunct);
			result.add(conjunct);
			assert !Arrays.asList(conjunct.getFreeVars()).contains(eliminatee) : "var is still there";
			if (ivc.indexInequality() && !ivc.valueEquality()) {
				assert !ivc.valueInequality() : "term would be false!";
				// case where we have valueEquality hat is not true
				// do something useful...
				// e.g., mark newSelect as occurring or mark auxVar as
				// equal to something
			}
		}
		return result;
	}

//	public static Term indexValueConnections(ArrayIndex ourIndex, Term ourValue, ArrayIndex[] othersIndices,
//			Term[] othersValues, int othersPosition, Script script, int quantifier) {
//		assert othersIndices.length == othersValues.length;
//		ArrayList<Term> additionalConjuncs = new ArrayList<Term>();
//		for (int i = othersPosition; i < othersIndices.length; i++) {
//			ArrayIndex othersIndex = othersIndices[i];
//			assert ourIndex.size() == othersIndex.size();
//			Term indexEquality = Util.and(script, buildPairwiseEquality(ourIndex, othersIndices[i], null, script));
//			Term valueEquality = SmtUtils.binaryEquality(script, ourValue, othersValues[i]);
//			Term conjunct = Util.or(script, SmtUtils.not(script, indexEquality), valueEquality);
//			if (quantifier == QuantifiedFormula.EXISTS) {
//				additionalConjuncs.add(conjunct);
//			} else {
//				assert quantifier == QuantifiedFormula.FORALL;
//				additionalConjuncs.add(SmtUtils.not(script, conjunct));
//			}
//		}
//		Term result;
//		if (quantifier == QuantifiedFormula.EXISTS) {
//			result = Util.and(script, additionalConjuncs.toArray(new Term[additionalConjuncs.size()]));
//		} else {
//			assert quantifier == QuantifiedFormula.FORALL;
//			result = Util.or(script, additionalConjuncs.toArray(new Term[additionalConjuncs.size()]));
//		}
//
//		
//
//		return result;
//	}
	
	


	/**
	 * Given an array a, find all multi-dimensional selects on this array.
	 * For each of them, try to obtain an representation of that value in which
	 * a does not occur. If not such representation exists, add a new auxiliary
	 * variable that represents that value.
	 *
	 */
	private class IndicesAndValues {
		private final Term[] mSelectTerm;
		private final ArrayIndex[] mIndices;
		private final Term mValues[];
		private final Set<TermVariable> mNewAuxVars;
		private final Map<Term, Term> mSelectTerm2Value = new HashMap<Term, Term>();

		public IndicesAndValues(final TermVariable array, final Term[] conjuncts) {
			final Set<MultiDimensionalSelect> set = new HashSet<MultiDimensionalSelect>();
			for (final Term conjunct : conjuncts) {
				for (final MultiDimensionalSelect mdSelect : MultiDimensionalSelect.extractSelectDeep(conjunct, false)) {
					if (mdSelect.getArray().equals(array)) {
						set.add(mdSelect);
					}
				}
			}
			final MultiDimensionalSelect[] arrayReads = set.toArray(new MultiDimensionalSelect[set.size()]);
			mSelectTerm = new Term[arrayReads.length];
			mIndices = new ArrayIndex[arrayReads.length];
			mValues = new Term[arrayReads.length];
			mNewAuxVars = new HashSet<TermVariable>();
			for (int i = 0; i < arrayReads.length; i++) {
				mSelectTerm[i] = arrayReads[i].getSelectTerm();
				mIndices[i] = arrayReads[i].getIndex();
				final EqualityInformation eqInfo = EqualityInformation.getEqinfo(mScript,
						arrayReads[i].getSelectTerm(), conjuncts, array, mQuantifier, mLogger);
				if (eqInfo == null) {
					final Term select = arrayReads[i].getSelectTerm();
					final TermVariable auxVar = mMgdScript.
							constructFreshTermVariable(s_FreshVariableString, select.getSort());
					mNewAuxVars.add(auxVar);
					mValues[i] = auxVar;
				} else {
					mValues[i] = eqInfo.getTerm();
				}
				mSelectTerm2Value.put(mSelectTerm[i], mValues[i]);
			}
		}

		public Term[] getSelectTerm() {
			return mSelectTerm;
		}

		public ArrayIndex[] getIndices() {
			return mIndices;
		}

		public Term[] getValues() {
			return mValues;
		}

		public Set<TermVariable> getNewAuxVars() {
			return mNewAuxVars;
		}

		public Map<Term, Term> getMapping() {
			return mSelectTerm2Value;
		}
	}

	/**
	 * Class that constructs the term 
	 *     (fstIndex == sndIndex) ==> (fstValue == sndValue)
	 * if selectConnection is true and the term
	 *     (fstIndex != sndIndex) ==> (fstValue == sndValue)
	 * if selectConnection is false.
	 *
	 */
	private class IndexValueConnection {
		private final ArrayIndex mfstIndex;
		private final ArrayIndex msndIndex;
		private final Term mfstValue;
		private final Term msndValue;
		private final boolean mSelectConnection;
		private final Term mIndexEquality;
		private final Term mValueEquality;

		public IndexValueConnection(final ArrayIndex fstIndex, final ArrayIndex sndIndex, final Term fstValue, final Term sndValue,
				final boolean selectConnection) {
			mfstIndex = fstIndex;
			msndIndex = sndIndex;
			mfstValue = fstValue;
			msndValue = sndValue;
			mSelectConnection = selectConnection;
			mIndexEquality = Util.and(mScript, SmtUtils.pairwiseEquality(mScript, fstIndex, sndIndex));
			mValueEquality = SmtUtils.binaryEquality(mScript, fstValue, sndValue);
		}

		/**
		 * Is equality of both indices already implied by context?
		 */
		public boolean indexEquality() {
			return mIndexEquality.equals(mScript.term("true"));
		}

		/**
		 * Is inequality of both indices already implied by context?
		 */
		public boolean indexInequality() {
			return mIndexEquality.equals(mScript.term("false"));
		}

		/**
		 * Is equality of both values already implied by context?
		 */
		public boolean valueEquality() {
			return mValueEquality.equals(mScript.term("true"));
		}

		/**
		 * Is inequality of both values already implied by context?
		 */
		public boolean valueInequality() {
			return mValueEquality.equals(mScript.term("false"));
		}

		public Term getTerm() {
			Term indexTerm = mIndexEquality;
			if (mSelectConnection) {
				indexTerm = SmtUtils.not(mScript, indexTerm);
			}
			return Util.or(mScript, indexTerm, mValueEquality);

		}
	}

	/**
	 * Return true if this is a nested select on arr. Throws exception if an
	 * index contains a select.
	 */
	private boolean isMultiDimensionalSelect(final Term term, final Term arr, final int dimension) {
		Term subterm = term;
		for (int i = 0; i < dimension; i++) {
			if (!(term instanceof ApplicationTerm)) {
				return false;
			}
			final ApplicationTerm subtermApp = (ApplicationTerm) subterm;
			if (!subtermApp.getFunction().getName().equals("select")) {
				return false;
			}
			subterm = subtermApp.getParameters()[0];
			final Term index = subtermApp.getParameters()[1];
			final Set<ApplicationTerm> selectTermsInIndex = (new ApplicationTermFinder("select", true))
					.findMatchingSubterms(index);
			if (!selectTermsInIndex.isEmpty()) {
				throw new UnsupportedOperationException("select in index not supported");
			}
		}
		return subterm.equals(arr);
	}

	// /**
	// * Return all selectTerms that read from the array given by arrayTv.
	// * @param selectTerms a[i],
	// * @return
	// */
	// private static Map<Term[], MultiDimensionalSelect> getArrayReads(
	// TermVariable arrayTv,
	// Set<ApplicationTerm> selectTerms) {
	// Map<Term[],MultiDimensionalSelect> index2mdSelect =
	// new HashMap<Term[],MultiDimensionalSelect>();
	// for (ApplicationTerm selectTerm : selectTerms) {
	// if (selectTerm.getFunction().getReturnSort().isArraySort()) {
	// // this is only a select nested in some other select or store
	// continue;
	// }
	// MultiDimensionalSelect ar = new MultiDimensionalSelect(selectTerm);
	// if (ar.getArray() == arrayTv) {
	// index2mdSelect.put(ar.getIndex(), ar);
	// } else {
	// // select on different array
	// continue;
	// }
	// }
	// return index2mdSelect;
	// }

	/**
	 * Given two lists of terms and a subsitution subst return the following
	 * conjunctions subst(first_1) == subst(second_1), ... ,subst(first_n) ==
	 * subst(second_n) if subst is null we use the identity function.
	 */
	private static Term[] buildPairwiseEquality(final ArrayIndex first, final ArrayIndex second, final Substitution subst, final Script script) {
		assert first.size() == second.size();
		final Term[] equivalent = new Term[first.size()];
		for (int i = 0; i < first.size(); i++) {
			Term firstTerm, secondTerm;
			if (subst == null) {
				firstTerm = first.get(i);
				secondTerm = second.get(i);
			} else {
				firstTerm = subst.transform(first.get(i));
				secondTerm = subst.transform(second.get(i));
			}
			equivalent[i] = SmtUtils.binaryEquality(script, firstTerm, secondTerm);
		}
		return equivalent;
	}

	/**
	 * assert term, replace TermVariable by constants in advance, replace by
	 * constants defined by mapping, if no constant defined by mapping declare
	 * constant and add to mapping
	 */
	private void assertTermWithTvs(final Map<Term, Term> mapping, final Script script, final Term term) {
		for (final TermVariable tv : term.getFreeVars()) {
			if (!mapping.containsKey(tv)) {
				final String name = "arrayElim_" + tv.getName();
				script.declareFun(name, new Sort[0], tv.getSort());
				final Term constant = script.term(name);
				mapping.put(tv, constant);
			}
		}
		final Term renamed = (new Substitution(script, mapping)).transform(term);
		mScript.assertTerm(renamed);
	}

	// public static int getDimension(Sort sort) {
	// if (sort.isArraySort()) {
	// Sort[] arg = sort.getArguments();
	// assert arg.length == 2;
	// return 1 + getDimension(arg[1]);
	// } else {
	// return 0;
	// }
	// }
	
	private Term eliminateSelfUpdates(final Script script, final int quantifier, final Term term) {
		final Term[] conjuncts;
		if (quantifier == QuantifiedFormula.EXISTS) {
			conjuncts = SmtUtils.getConjuncts(term);
		} else {
			assert quantifier == QuantifiedFormula.FORALL;
			conjuncts = SmtUtils.getDisjuncts(term);
		}
//		ArrayUpdateExtractor aue = new ArrayUpdateExtractor(quantifier == QuantifiedFormula.FORALL, false, conjuncts);
		final ArrayList<Term> resultConjuncts = new ArrayList<>();
		boolean someSelfUpdate = false;
		for (final Term conjunct : conjuncts) {
			ArrayUpdate au;
			try {
				au = new ArrayUpdate(conjunct, false, false);
			} catch (final ArrayUpdateException aue1) {
				try {
					au = new ArrayUpdate(conjunct, true, false);
				} catch (final ArrayUpdateException aue2) {
					resultConjuncts.add(conjunct);
					continue;
				}
			}
			if (isSelfUpdate(au)) {
				someSelfUpdate = true;
				final Term select = buildEquivalentSelect(script, au);
				resultConjuncts.add(select);
			} else {
				resultConjuncts.add(au.getArrayUpdateTerm());
			}
		}
		if (someSelfUpdate) {
			if (quantifier == QuantifiedFormula.EXISTS) {
				return SmtUtils.and(script, resultConjuncts);
			} else {
				assert quantifier == QuantifiedFormula.FORALL;
				return SmtUtils.or(script, resultConjuncts);
			}
		} else {
			return term;
		}
	}

	private Term buildEquivalentSelect(final Script script, final ArrayUpdate au) {
		assert isSelfUpdate(au) : "no self-update";
		final Term selectTerm = SmtUtils.multiDimensionalSelect(mScript, au.getNewArray(), au.getIndex());
		final String fun;
		if (au.isNegatedEquality()) {
			fun = "distinct";
		} else {
			fun = "=";
		}
		return script.term(fun, selectTerm, au.getValue());
	}

	private boolean isSelfUpdate(final ArrayUpdate au) {
		if (au.getOldArray().equals(au.getNewArray())) {
			return true;
		} else {
			if (Arrays.asList(au.getOldArray().getFreeVars()).contains(au.getNewArray())) {
				throw new UnsupportedOperationException("nested self-update " + au.getArrayUpdateTerm());
			} else {
				return false;
			}
		}
	}

}
