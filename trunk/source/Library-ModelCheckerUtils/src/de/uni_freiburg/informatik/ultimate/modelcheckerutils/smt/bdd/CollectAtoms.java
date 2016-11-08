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
	
	public List<Term> getTerms(final Term in){
		mAtoms = new ArrayList<>();
		run(new CollectAtoms.AtomCollector(in));
		return mAtoms;
	}
	
	private static class AtomCollector extends TermWalker {
		
		public AtomCollector(final Term term) {
			super(term);
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			if(!(cnr.mAtoms.contains(term))) {
				cnr.mAtoms.add(term);
			}
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			walker.enqueueWalker(new AtomCollector(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
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
		public void walk(final NonRecursive walker, final LetTerm term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			if(!(cnr.mAtoms.contains(term))) {
				cnr.mAtoms.add(term);
			}
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			if(!(cnr.mAtoms.contains(term))) {
				cnr.mAtoms.add(term);
			}
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			final CollectAtoms cnr = (CollectAtoms)walker;
			if(!(cnr.mAtoms.contains(term))) {
				cnr.mAtoms.add(term);
			}
		}
	}
}
