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

public class BddBuilder extends NonRecursive {
	
	private BDDFactory mFactory;
	private List<Term> mAtoms;
	private Queue<BDD> mValues;
	
	public BDDFactory getFactory() {
		return mFactory;
	}
	
	public List<Term> getAtoms() {
		return mAtoms;
	}
	
	protected Queue<BDD> getValues() {
		return mValues;
	}
	
	public BDD buildBDD(final Term in, final List<Term> atoms) {
		mAtoms = atoms;
		mValues = new LinkedList<>();
		mFactory = BDDFactory.init("java", atoms.size() + 2, atoms.size() + 2, false);
		mFactory.setVarNum(atoms.size());
		run(new DownWalker(in));
		return mValues.poll();
	}
	
	private static class DownWalker extends TermWalker {
		
		public DownWalker(final Term term) {
			super(term);
		}
		
		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			final BddBuilder bb = (BddBuilder) walker;
			bb.getValues().add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
		}
		
		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			final BddBuilder bb = (BddBuilder) walker;
			walker.enqueueWalker(new DownWalker(term.getSubterm()));
		}
		
		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			final BddBuilder bb = (BddBuilder) walker;
			final String fName = term.getFunction().getName();
			if (fName.equals("and") || fName.equals("or") || fName.equals("xor") || fName.equals("not")
					|| fName.equals("=>")) {
				bb.enqueueWalker(new UpWalker(term));
				for (final Term t : term.getParameters()) {
					walker.enqueueWalker(new DownWalker(t));
				}
			} else if (fName.equals("true")) {
				bb.getValues().add(bb.getFactory().one());
				
			} else if (fName.equals("false")) {
				bb.getValues().add(bb.getFactory().zero());
				
			} else {
				bb.getValues().add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
			}
		}
		
		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			final BddBuilder bb = (BddBuilder) walker;
			bb.getValues().add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
		}
		
		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			final BddBuilder bb = (BddBuilder) walker;
			bb.getValues().add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
		}
		
		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			final BddBuilder bb = (BddBuilder) walker;
			bb.getValues().add(bb.getFactory().ithVar(bb.getAtoms().indexOf(term)));
		}
	}
	
	private static class UpWalker extends TermWalker {
		
		public UpWalker(final Term term) {
			super(term);
		}
		
		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			//should not happen
		}
		
		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			//should not happen
		}
		
		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			final BddBuilder bb = (BddBuilder) walker;
			final String fName = term.getFunction().getName();
			if (fName.equals("and")) {
				BDD b = bb.getValues().poll();
				for (int i = 0; i < term.getParameters().length - 1; i++) {
					b = b.and(bb.getValues().poll());
				}
				bb.getValues().add(b);
			} else if (fName.equals("or")) {
				BDD b = bb.getValues().poll();
				for (int i = 0; i < term.getParameters().length - 1; i++) {
					b = b.or(bb.getValues().poll());
				}
				bb.getValues().add(b);
			} else if (fName.equals("xor")) {
				BDD b = bb.getValues().poll();
				for (int i = 0; i < term.getParameters().length - 1; i++) {
					b = b.xor(bb.getValues().poll());
				}
				bb.getValues().add(b);
			} else if (fName.equals("=>")) {
				BDD b = bb.getValues().poll();
				for (int i = 0; i < term.getParameters().length - 1; i++) {
					b = b.imp(bb.getValues().poll());
				}
				bb.getValues().add(b);
			} else if (fName.equals("not")) {
				final BDD b = bb.getValues().poll();
				bb.getValues().add(b.not());
			}
		}
		
		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			//should not happen
		}
		
		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			//should not happen
		}
		
		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			//should not happen
		}
	}
}
