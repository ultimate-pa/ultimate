package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfStateBuilder;

public class WrapperFactory {
	
	/**
	 * 
	 * 
	 * @param term
	 * @return
	 */
	public static IElementWrapper wrapElement(Term term) {
		assert !term.getSort().isArraySort();
		
		if (term instanceof TermVariable) {
			
		} else if (term instanceof ConstantTerm) {
			assert false : "TODO";
		} else if (term instanceof ApplicationTerm
				&& ((ApplicationTerm) term).getParameters().length == 0) {
			// we have a constant
			assert false : "TODO";
		} else if (term instanceof ApplicationTerm
				&& ((ApplicationTerm) term).getFunction().getName().equals("select")) {
	 	} else {
	 		assert false : "missed case?";
	 	}
		
		return null;
	}
	
	public static IArrayWrapper wrapArray(Term term) {
		
		return null;
	}

}

class ElementWrapper extends NonRecursive {
	
	
	VPTfStateBuilder mTfStateBuilder;
	TransFormula mTransFormula;



	class ElementWrapperWalker extends TermWalker {

		private IElementWrapper mResult;

		public ElementWrapperWalker(Term term) {
			super(term);
			// TODO Auto-generated constructor stub
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			
			if (term.getFunction().getName().equals("select")) {
				
				MultiDimensionalSelect mds = new MultiDimensionalSelect(term);
				
				IArrayWrapper array  = new ArrayWrapperNR(mds.getArray()).getResult();
				
				List<IElementWrapper> indices = new ArrayList<>();
				for (Term index : mds.getIndex()) {
					IElementWrapper indexWr = new ElementWrapperWalker(index).getResult();
					indices.add(indexWr);
				}
				
				mResult = new SelectTermWrapper(array, indices); // TODO
				return;
			} else if (term.getFunction().getName().equals("store")) {
				assert false : "this walker should not be called on terms with array type";
				return;
			} else if (term.getParameters().length == 0) {
				// we have a constant
				EqNode eqNode = mTfStateBuilder.getPreAnalysis().getEqNode(term, 
						Collections.emptyMap());
				VPTfNodeIdentifier nodeId = mTfStateBuilder.getNodeIdentifier(eqNode, 
						Collections.emptyMap(),
						Collections.emptyMap());
				mResult = nodeId;
				return;
			} else {
				assert false : "missing case?";
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {

			EqNode eqNode = mTfStateBuilder.getPreAnalysis().getEqNode(term, 
					VPDomainHelpers.computeProgramVarMappingFromTransFormula(mTransFormula));
			VPTfNodeIdentifier nodeId = mTfStateBuilder.getNodeIdentifier(eqNode, 
					VPDomainHelpers.projectToTerm(mTransFormula.getInVars(), term), 
					VPDomainHelpers.projectToTerm(mTransFormula.getOutVars(), term));
			mResult = nodeId;
		}
		
		public IElementWrapper getResult() {
			// TODO
			assert false;
			return null;
		}
	}
}

class ArrayWrapperNR extends NonRecursive {
	
	class ArrayWrapperWalker extends TermWalker {

		public ArrayWrapperWalker(Term term) {
			super(term);
			// TODO Auto-generated constructor stub
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			
			
		}
		
	}

	public ArrayWrapperNR(Term term) {
		// TODO Auto-generated constructor stub
	}

	public IArrayWrapper getResult() {
		// TODO Auto-generated method stub
		assert false;
		return null;
	}
}