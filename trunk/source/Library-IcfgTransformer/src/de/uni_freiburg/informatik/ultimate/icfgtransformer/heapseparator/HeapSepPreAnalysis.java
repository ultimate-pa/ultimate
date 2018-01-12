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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

/**
 * Does a preanalysis on the program before the actual heap separation is done
 * (using the abstract interpretation result from the equality domain).
 * Computes: - which arrays are equated, anywhere in the program (occur left and
 * right each of an equality in a TransFormula) - for each array in the program
 * the locations where it is accessed (question: does this mean that large block
 * encoding is detrimental to heapseparation?)
 *
 * @author Alexander Nutz
 *
 */
public class HeapSepPreAnalysis {

	private final HashRelation<Term, IcfgLocation> mArrayToAccessLocations;

	private final HashRelation<Term, ArrayIndex> mArrayToAccessingIndices;

	private final SymmetricHashRelation<Term> mArrayEqualities;

	private final ManagedScript mScript;

	/**
	 * The HeapSepPreAnalysisVisitor computes and provides the following
	 * information:
	 *  <li> which arrays (base arrays, not store terms) are equated in the
	 * program
	 *  <li> for each array at which locations in the CFG it is accessed
	 *
	 * @param logger
	 * @param equalityProvider
	 */
	public HeapSepPreAnalysis(final ILogger logger, final ManagedScript script) {
		mArrayToAccessLocations = new HashRelation<>();
		mArrayToAccessingIndices = new HashRelation<>();
		mScript = script;
		mArrayEqualities = new SymmetricHashRelation<>();
	}

	public void processEdge(final IcfgEdge edge) {
		final UnmodifiableTransFormula tf = edge.getTransformula();

		final List<ArrayEquality> aeqs = ArrayEquality.extractArrayEqualities(tf.getFormula());
		for (final ArrayEquality aeq : aeqs) {
			final Term first = VPDomainHelpers.normalizeTerm(aeq.getLhs(), tf, mScript);
			final Term second = VPDomainHelpers.normalizeTerm(aeq.getRhs(), tf, mScript);

			mArrayEqualities.addPair(first, second);
		}

		mArrayToAccessLocations.addAll(findArrayAccesses(edge));

		mArrayToAccessingIndices.addAll(findAccessingIndices(edge));
	}

	private HashRelation<Term, ArrayIndex> findAccessingIndices(final IcfgEdge edge) {

		final UnmodifiableTransFormula tf = edge.getTransformula();
		final HashRelation<Term, ArrayIndex> result = new HashRelation<>();

		/*
		 * handle selects in the formula
		 */
		final List<MultiDimensionalSelect> mdSelectsAll = MultiDimensionalSelect.extractSelectShallow(tf.getFormula(),
				false);
		// MultiDimensionalSelect.extractSelectDeep(tf.getFormula(), false);
		final List<MultiDimensionalSelect> mdSelectsFiltered = mdSelectsAll.stream()
				.filter(mds -> isArrayTracked(mds.getArray(), tf)).collect(Collectors.toList());
		for (final MultiDimensionalSelect mds : mdSelectsFiltered) {
			final Term array = VPDomainHelpers.normalizeTerm(getInnerMostArray(mds.getArray()), tf, mScript);
			final ArrayIndex index = VPDomainHelpers.normalizeArrayIndex(mds.getIndex(), tf, mScript);
			assert index.size() == new MultiDimensionalSort(mds.getArray().getSort()).getDimension();
			result.addPair(array, index);
		}

		/*
		 * handle stores in the formula
		 */
		final List<MultiDimensionalStore> mdStoresAll = MultiDimensionalStore
				.extractArrayStoresShallow(tf.getFormula());
//				.extractArrayStoresDeep(tf.getFormula());
		final List<MultiDimensionalStore> mdStoresFiltered = mdStoresAll.stream()
				.filter(mds -> isArrayTracked(mds.getArray(), tf)).collect(Collectors.toList());
		// mdStoresFiltered.forEach(mds -> result.addPair(
		// VPDomainHelpers.normalizeTerm(getInnerMostArray(mds.getArray()), tf,
		// mScript),
		// VPDomainHelpers.normalizeArrayIndex(mds.getIndex(), tf, mScript)));
		for (final MultiDimensionalStore mds : mdStoresFiltered) {
			final Term array = VPDomainHelpers.normalizeTerm(getInnerMostArray(mds.getArray()), tf, mScript);
			final ArrayIndex index = VPDomainHelpers.normalizeArrayIndex(mds.getIndex(), tf, mScript);
			// assert index.size() == mds.getArray().getSort().getArguments().length - 1;
			assert index.size() == new MultiDimensionalSort(mds.getArray().getSort()).getDimension();
			result.addPair(array, index);
		}

		return result;
	}

	private HashRelation<Term, IcfgLocation> findArrayAccesses(final IcfgEdge edge) {
		final HashRelation<Term, IcfgLocation> result = new HashRelation<>();
		if (edge instanceof Summary && ((Summary) edge).calledProcedureHasImplementation()) {
			return result;
		}

		for (final Entry<IProgramVar, TermVariable> en : edge.getTransformula().getInVars().entrySet()) {
			final IProgramVar pv = en.getKey();
			if (!pv.getTermVariable().getSort().isArraySort()) {
				continue;
			}
			if (!isArrayTracked(pv)) {
				continue;
			}
			// we have an array variable --> store that it occurs after the source location
			// of the edge
			result.addPair(pv.getTerm(), edge.getSource());
		}
		for (final Entry<IProgramVar, TermVariable> en : edge.getTransformula().getOutVars().entrySet()) {
			final IProgramVar pv = en.getKey();
			if (!pv.getTermVariable().getSort().isArraySort()) {
				continue;
			}
			if (!isArrayTracked(pv)) {
				continue;
			}
			// we have an array variable --> store that it occurs after the source location
			// of the edge
			result.addPair(pv.getTerm(), edge.getSource());
		}
		return result;
	}

	SymmetricHashRelation<Term> getArrayEqualities() {
		return mArrayEqualities;
	}

	HashRelation<Term, IcfgLocation> getArrayToAccessLocations() {
		return mArrayToAccessLocations;
	}

	public HashRelation<Term, ArrayIndex> getArrayToAccessingIndices() {
		return mArrayToAccessingIndices;
	}

	public Term getInnerMostArray(final Term arrayTerm) {
		assert arrayTerm.getSort().isArraySort();
		Term innerArray = arrayTerm;
		// while (SmtUtils.containsFunctionApplication(innerArray, "store")) {
		while (true) {
			boolean madeChange = false;
			if (SmtUtils.isFunctionApplication(innerArray, "store")) {
				innerArray = ((ApplicationTerm) innerArray).getParameters()[0];
				madeChange = true;
			} else if (SmtUtils.isFunctionApplication(innerArray, "select")) {
				innerArray = ((ApplicationTerm) innerArray).getParameters()[0];
				madeChange = true;
			}
			if (!madeChange) {
				break;
			}
		}
		assert innerArray instanceof TermVariable;
		return innerArray;
	}

	public Set<ArrayIndex> getAccessingIndicesForArrays(final Set<Term> arrayGroup) {
		final Set<ArrayIndex> result = new HashSet<>();
		arrayGroup.forEach(array -> result.addAll(getArrayToAccessingIndices().getImage(array)));
		return result;
	}

	private boolean isArrayTracked(final IProgramVarOrConst array) {
		return true;
	}

	private boolean isArrayTracked(final Term array, final UnmodifiableTransFormula tf) {
		return true;
	}
}
