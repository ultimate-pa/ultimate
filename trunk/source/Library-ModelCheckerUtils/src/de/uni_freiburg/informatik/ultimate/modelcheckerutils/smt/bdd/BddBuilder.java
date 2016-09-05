package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

public class BddBuilder extends NonRecursive{
		
	private BDDFactory mFactory;
	private List<Term> mAtoms;
	private Queue<BDD> mValues;
	
	public BddBuilder(){
		super();
	}
	
	public BDDFactory getFactory(){
		return mFactory;
	}
	
	public List<Term> getAtoms(){
		return mAtoms;
	}
	
	public BDD buildBDD(Term in, List<Term> atoms){
		mAtoms = atoms;
		mValues = new LinkedList<BDD>();
		mFactory = BDDFactory.init("java", atoms.size()+2, atoms.size()+2, false);
		mFactory.setVarNum(atoms.size());
		run(new DownWalker(in));
		return mValues.poll();
	}
	
	private static class DownWalker extends TermWalker{

		public DownWalker(Term term) {
			super(term);
		}
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			final BddBuilder bb = (BddBuilder)walker;
			bb.mValues.add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			final BddBuilder bb = (BddBuilder)walker;
			walker.enqueueWalker(new DownWalker(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			final BddBuilder bb = (BddBuilder)walker;
			final String fName = term.getFunction().getName();
			if(fName.equals("and") || fName.equals("or") || fName.equals("xor") || fName.equals("not") || fName.equals("=>")){
				bb.enqueueWalker(new UpWalker(term));
				for(final Term t:term.getParameters()){
					walker.enqueueWalker(new DownWalker(t));
				}
			}else if(fName.equals("true")){
				bb.mValues.add(bb.getFactory().one());
				
			}else if(fName.equals("false")){
				bb.mValues.add(bb.getFactory().zero());
				
			}else{
				bb.mValues.add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			final BddBuilder bb = (BddBuilder)walker;
			bb.mValues.add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			final BddBuilder bb = (BddBuilder)walker;
			bb.mValues.add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			final BddBuilder bb = (BddBuilder)walker;
			bb.mValues.add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
		}
	}
	
	private static class UpWalker extends TermWalker{

		public UpWalker(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			//should not happen
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			//should not happen
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			final BddBuilder bb = (BddBuilder)walker;
			final String fName = term.getFunction().getName();
			if(fName.equals("and")){
				BDD b = bb.mValues.poll();
				for(int i = 0; i < term.getParameters().length-1; i++){
					b = b.and(bb.mValues.poll());
				}
				bb.mValues.add(b);
			}else if(fName.equals("or")){
				BDD b = bb.mValues.poll();
				for(int i = 0; i < term.getParameters().length-1; i++){
					b = b.or(bb.mValues.poll());
				}
				bb.mValues.add(b);
			}else if(fName.equals("xor")){
				BDD b = bb.mValues.poll();
				for(int i = 0; i < term.getParameters().length-1; i++){
					b = b.xor(bb.mValues.poll());
				}
				bb.mValues.add(b);
			}else if(fName.equals("=>")){
				BDD b = bb.mValues.poll();
				for(int i = 0; i < term.getParameters().length-1; i++){
					b = b.imp(bb.mValues.poll());
				}
				bb.mValues.add(b);
			}else if(fName.equals("not")){
				final BDD b = bb.mValues.poll();
				bb.mValues.add(b.not());
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			//should not happen
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			//should not happen
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			//should not happen
		}
	}
}
