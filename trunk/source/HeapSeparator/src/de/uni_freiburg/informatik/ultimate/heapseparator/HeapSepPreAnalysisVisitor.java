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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.BoogieVarOrConst;
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
	
	



	private AbstractRelation<IProgramVarOrConst, IcfgLocation, ?> findArrayAccesses(CodeBlock edge) {
		AbstractRelation<IProgramVar, IcfgLocation, ?> result = new HashRelation<>();
		
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
		return null;
//		return result; //TODO
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