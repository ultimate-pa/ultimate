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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.ConstOrLiteral;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.AbstractRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Does a preanalysis on the program before the actual heap separation is done (using the
 * abstract interpretation result from the equality domain).
 * Computes:
 *  - which arrays are equated, anywhere in the program (occur left and right each of an equality in a TransFormula)
 *  - for each array in the program the locations where it is accessed
 *     (question: does this mean that large block encoding is hurtful for heapseparation?)
 * 
 * 
 * @author Alexander Nutz
 *
 */
public class HeapSepPreAnalysisVisitor extends SimpleRCFGVisitor {

	/**
	 * set to collect all pairs of arrays which appear on left and right side
	 * of an equals, e.g., if (= a b) occurs, we record the pair (a,b), but
	 * also in the case (among many others)
	 * (= a (store b i x)) (though it is not clear to me if this case can arise in a normal
	 * Boogie program
	 */
	private final Set<Pair<IProgramVarOrConst, IProgramVarOrConst>> mEquatedArrays;
	
	private final HashRelation<IProgramVarOrConst, IcfgLocation> mArrayToAccessLocations;

	private List<ArrayEquality> mArrayEqualities;

	/**
	 * The HeapSepPreAnalysisVisitor computes and provides the following information:
	 *  - which arrays (base arrays, not store terms) are equated in the program
	 *  - for each array at which locations in the CFG it is accessed
	 * @param logger
	 */
	public HeapSepPreAnalysisVisitor(ILogger logger) {
		super(logger);
		mEquatedArrays = new HashSet<>();
		mArrayToAccessLocations = new HashRelation<>();
	}

	@Override
	public void level(IcfgEdge edge) {
		
		if (edge instanceof CodeBlock) {
			mEquatedArrays.addAll(new EquatedArraysFinder((CodeBlock) edge).getResult());
			
			mArrayEqualities = ArrayEquality.extractArrayEqualities(((CodeBlock) edge).getTransitionFormula().getFormula());
			
//			mArrayToAccessPositions.addAll(new ArrayAccessFinder((CodeBlock) edge, edge.getSource()).getResult());
			mArrayToAccessLocations.addAll(findArrayAccesses((CodeBlock) edge));
		}
		super.level(edge);
	}
	
	



	private HashRelation<IProgramVarOrConst, IcfgLocation> findArrayAccesses(CodeBlock edge) {
		HashRelation<IProgramVarOrConst, IcfgLocation> result = new HashRelation<>();
		
		for (Entry<IProgramVar, TermVariable> en : edge.getTransitionFormula().getInVars().entrySet()) {
			IProgramVar pv = en.getKey();
			if (!pv.getTermVariable().getSort().isArraySort()) {
				continue;
			}
			// we have an array variable --> store that it occurs after the source location of the edge
			result.addPair(pv, edge.getSource());
		}
		for (Entry<IProgramVar, TermVariable> en : edge.getTransitionFormula().getOutVars().entrySet()) {
			IProgramVar pv = en.getKey();
			if (!pv.getTermVariable().getSort().isArraySort()) {
				continue;
			}
			// we have an array variable --> store that it occurs after the source location of the edge
			result.addPair(pv, edge.getSource());
		}	
		return result;
	}

	@Override
	public boolean performedChanges() {
		// this visitor is only for analysis, it should not change anything
		return false;
	}

	@Override
	public boolean abortCurrentBranch() {
		return false;
	}

	@Override
	public boolean abortAll() {
		return false;
	}
	
	HashRelation<IProgramVarOrConst, IcfgLocation> getArrayToAccessLocations() {
		return mArrayToAccessLocations;
	}
}

class EquatedArraysFinder extends TermTransformer {
	private final CodeBlock mCodeBlock;
	private final Set<Pair<IProgramVarOrConst, IProgramVarOrConst>> mEquatedArrays;

	EquatedArraysFinder(CodeBlock edge) {
		mCodeBlock = edge;
		mEquatedArrays = new HashSet<>();
		transform(edge.getTransitionFormula().getFormula());
	}

	public Collection<? extends Pair<IProgramVarOrConst, IProgramVarOrConst>> getResult() {
		return mEquatedArrays;
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		final String funcName = appTerm.getFunction().getName();
		if (("=".equals(funcName) || "distinct".equals(funcName))
				&& appTerm.getParameters()[0].getSort().isArraySort()
				&& appTerm.getParameters()[1].getSort().isArraySort()) {
			// we have an array assignment
			TermVariable a1 = new ArrayFinder(appTerm.getParameters()[0]).getResult();
			TermVariable a2 = new ArrayFinder(appTerm.getParameters()[1]).getResult();

			if (a1 != a2) {
				IProgramVar pv1 = HeapSepRcfgVisitor.getBoogieVarFromTermVar(a1, 
						mCodeBlock.getTransitionFormula().getInVars(), 
						mCodeBlock.getTransitionFormula().getOutVars());
				IProgramVar pv2 = HeapSepRcfgVisitor.getBoogieVarFromTermVar(a2, 
						mCodeBlock.getTransitionFormula().getInVars(), 
						mCodeBlock.getTransitionFormula().getOutVars());
				// two non-identical arrays are equated --> store that fact
//				mEquatedArrays.add(new Pair<IProgramVar, IProgramVar>(pv1, pv2)); //TODO
			}
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}
}
//
//class ArrayAccessFinder extends TermTransformer {
//
//	private final CodeBlock mCodeBlock;
//	private final IcfgLocation mLocation;
//	private final HashRelation<IProgramVar, IcfgLocation> mResult;
//	
//	public ArrayAccessFinder(CodeBlock edge, IcfgLocation location) {
//
//		mCodeBlock = edge;
//		mResult = new HashRelation<>();
//		mLocation = location;
//	}
//
//	public HashRelation<IProgramVar, IcfgLocation> getResult() {
//		return mResult;
//	}
//
//	@Override
//	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
//		String funcName = appTerm.getFunction().getName();
//		if ("select".equals(funcName)) {
//			
//		} else if ("store".equals(funcName)) {
//
//		}
//		super.convertApplicationTerm(appTerm, newArgs);
//	}
//}
