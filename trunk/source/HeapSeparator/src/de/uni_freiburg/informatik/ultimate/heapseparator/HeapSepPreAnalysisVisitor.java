package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.visitors.SimpleRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class HeapSepPreAnalysisVisitor extends SimpleRCFGVisitor {

	/**
	 * set to collect all pairs of arrays which appear on left and right side
	 * of an equals, e.g., if (= a b) occurs, we record the pair (a,b), but
	 * also in the case (among many others)
	 * (= a (store b i x)) (though it is not clear to me if this case can arise in a normal
	 * Boogie program
	 */
	private final Set<Pair<IProgramVar, IProgramVar>> mEquatedArrays;

	public HeapSepPreAnalysisVisitor(ILogger logger) {
		super(logger);
		mEquatedArrays = new HashSet<>();
	}

	@Override
	public void level(IcfgEdge edge) {
		
		if (edge instanceof CodeBlock) {
			mEquatedArrays.addAll(new EquatedArraysFinder((CodeBlock) edge).getResult());
		}
		super.level(edge);
	}



	@Override
	public boolean performedChanges() {
		// this visitor is only for analysis, it should not change anything
		return false;
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
	
}
class EquatedArraysFinder extends TermTransformer {
	private final CodeBlock mCodeBlock;
	private final Set<Pair<IProgramVar, IProgramVar>> mEquatedArrays;

	EquatedArraysFinder(CodeBlock edge) {
		mCodeBlock = edge;
		mEquatedArrays = new HashSet<>();
		transform(edge.getTransitionFormula().getFormula());
	}

	public Collection<? extends Pair<IProgramVar, IProgramVar>> getResult() {
		return mEquatedArrays;
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		final String funcName = appTerm.getFunction().getName();
		if (funcName.equals("=")
				&& appTerm.getParameters()[0].getSort().isArraySort()
				&& appTerm.getParameters()[1].getSort().isArraySort()
				) {
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
				mEquatedArrays.add(new Pair<IProgramVar, IProgramVar>(pv1, pv2));
			}
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}
}

