package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class CollectAtoms extends NonRecursive{
		
	private List<Term> mAtoms;
	
	public CollectAtoms(){
		super();
	}
	
	public List<Term> getTerms(Term in){
		mAtoms = new ArrayList<>();
		run(new CollectAtoms.AtomCollector(in));
		return mAtoms;
	}
	
	private static class AtomCollector extends TermWalker {
		
		public AtomCollector(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			if(!(cnr.mAtoms.contains(term))) {
				cnr.mAtoms.add(term);
			}
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			walker.enqueueWalker(new AtomCollector(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			final String fName = term.getFunction().getName();
			if(fName.equals("and") || fName.equals("or") || fName.equals("xor") || fName.equals("not") || fName.equals("=>")){
				for(final Term t:term.getParameters()){
					walker.enqueueWalker(new AtomCollector(t));
				}
			}else if(fName.equals("true") || fName.equals("false")){
				if(!(cnr.mAtoms.contains(term)))
				 {
					cnr.mAtoms.add(term); //macht scheinbar probleme wenn mans ignoriert
				}
			}else{
				if(!(cnr.mAtoms.contains(term))) {
					cnr.mAtoms.add(term);
				}
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			if(!(cnr.mAtoms.contains(term))) {
				cnr.mAtoms.add(term);
			}
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			if(!(cnr.mAtoms.contains(term))) {
				cnr.mAtoms.add(term);
			}
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			if(!(cnr.mAtoms.contains(term))) {
				cnr.mAtoms.add(term);
			}
		}
	}
}
