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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Does a preanalysis on the program before the actual heap separation is done (using the
 * abstract interpretation result from the equality domain).
 * Computes:
 *  - which arrays are equated, anywhere in the program (occur left and right each of an equality in a TransFormula)
 *  - for each array in the program the locations where it is accessed
 *     (question: does this mean that large block encoding is detrimental to heapseparation?)
 * 
 * @author Alexander Nutz
 *
 */
public class HeapSepPreAnalysis {

	private final HashRelation<Term, IcfgLocation> mArrayToAccessLocations;
	
	private final HashRelation<Term, List<Term>> mArrayToAccessingIndices;

	private final Set<VPDomainSymmetricPair<Term>> mArrayEqualities;

	private final ManagedScript mScript;

	private VPDomainPreanalysis mVpDomainPreAnalysis;

	/**
	 * The HeapSepPreAnalysisVisitor computes and provides the following information:
	 *  - which arrays (base arrays, not store terms) are equated in the program
	 *  - for each array at which locations in the CFG it is accessed
	 * @param logger
	 */
	public HeapSepPreAnalysis(ILogger logger, ManagedScript script, VPDomain domain) {
//		super(logger);
		mArrayToAccessLocations = new HashRelation<>();
		mArrayToAccessingIndices = new HashRelation<>();
		mScript = script;
		mArrayEqualities = new HashSet<>();
		mVpDomainPreAnalysis = domain.getPreAnalysis();
	}

	public void processEdge(IcfgEdge edge) {
		
		if (edge instanceof CodeBlock) {

			final UnmodifiableTransFormula tf = ((CodeBlock) edge).getTransformula();

			final List<ArrayEquality> aeqs = ArrayEquality.extractArrayEqualities(tf.getFormula());
			for (ArrayEquality aeq : aeqs) {
				final Term first = VPDomainHelpers.normalizeTerm(aeq.getLhs(), tf, mScript);
				final Term second = VPDomainHelpers.normalizeTerm(aeq.getRhs(), tf, mScript);
				
				mArrayEqualities.add(new VPDomainSymmetricPair<Term>(first, second));
			}

			mArrayToAccessLocations.addAll(findArrayAccesses((CodeBlock) edge));
			
			mArrayToAccessingIndices.addAll(findAccessingIndices((CodeBlock) edge));
		}
	}
	
	private HashRelation<Term, List<Term>> findAccessingIndices(CodeBlock edge) {
		
		final UnmodifiableTransFormula tf = edge.getTransformula();
		final HashRelation<Term, List<Term>> result = new HashRelation<>();
		
		/*
		 * handle selects in the formula
		 */
		final List<MultiDimensionalSelect> mdSelectsAll =
				MultiDimensionalSelect.extractSelectDeep(tf.getFormula(), false);
		final List<MultiDimensionalSelect> mdSelectsFiltered = 
							mdSelectsAll.stream()
							.filter(mds -> mVpDomainPreAnalysis.isArrayTracked(mds.getArray(), tf))
							.collect(Collectors.toList());
		mdSelectsFiltered.forEach(mds -> result.addPair(
				VPDomainHelpers.normalizeTerm(getInnerMostArray(mds.getArray()), tf, mScript), 
					VPDomainHelpers.normalizeArrayIndex(mds.getIndex(), tf, mScript)));

		/*
		 * handle stores in the formula
		 */
		final List<MultiDimensionalStore> mdStoresAll =
				MultiDimensionalStore.extractArrayStoresDeep(tf.getFormula());
		final List<MultiDimensionalStore> mdStoresFiltered = mdStoresAll.stream()
				.filter(mds -> mVpDomainPreAnalysis.isArrayTracked(mds.getArray(), tf))
				.collect(Collectors.toList());
		mdStoresFiltered.forEach(mds -> result.addPair(
				VPDomainHelpers.normalizeTerm(getInnerMostArray(mds.getArray()), tf, mScript), 
					VPDomainHelpers.normalizeArrayIndex(mds.getIndex(), tf, mScript)));

		return result;
	}

	private HashRelation<Term, IcfgLocation> findArrayAccesses(CodeBlock edge) {
		final HashRelation<Term, IcfgLocation> result = new HashRelation<>();
		
		for (Entry<IProgramVar, TermVariable> en : edge.getTransformula().getInVars().entrySet()) {
			IProgramVar pv = en.getKey();
			if (!pv.getTermVariable().getSort().isArraySort()) {
				continue;
			}
			if (!mVpDomainPreAnalysis.isArrayTracked(pv)) {
				continue;
			}
			// we have an array variable --> store that it occurs after the source location of the edge
			result.addPair(pv.getTerm(), edge.getSource());
		}
		for (Entry<IProgramVar, TermVariable> en : edge.getTransformula().getOutVars().entrySet()) {
			IProgramVar pv = en.getKey();
			if (!pv.getTermVariable().getSort().isArraySort()) {
				continue;
			}
			if (!mVpDomainPreAnalysis.isArrayTracked(pv)) {
				continue;
			}
			// we have an array variable --> store that it occurs after the source location of the edge
			result.addPair(pv.getTerm(), edge.getSource());
		}	
		return result;
	}
	
	Set<VPDomainSymmetricPair<Term>> getArrayEqualities() {
		return mArrayEqualities;
	}

	HashRelation<Term, IcfgLocation> getArrayToAccessLocations() {
		return mArrayToAccessLocations;
	}

	public HashRelation<Term, List<Term>> getArrayToAccessingIndices() {
		return mArrayToAccessingIndices;
	}
	
	public Term getInnerMostArray(Term arrayTerm) {
		assert arrayTerm.getSort().isArraySort();
		Term innerArray = arrayTerm;
		while (SmtUtils.containsFunctionApplication(innerArray, "store")) {
			innerArray = ((ApplicationTerm) innerArray).getParameters()[0];
		}
		assert innerArray instanceof TermVariable;
		return innerArray;
	}

	public Set<List<Term>> getAccessingIndicesForArrays(Set<Term> arrayGroup) {
		 Set<List<Term>> result = new HashSet<>();
		 arrayGroup.forEach(array -> 
		 	result.addAll(getArrayToAccessingIndices().getImage(array)));
		return result;
	}
}
