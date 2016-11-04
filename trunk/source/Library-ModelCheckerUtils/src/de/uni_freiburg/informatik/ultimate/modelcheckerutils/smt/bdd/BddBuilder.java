package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.util.ArrayList;
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

	private BDD mResult;

	public BddBuilder() {
		super();
	}

	public BDD buildBDD(Term in, List<Term> atoms) {
		BDDFactory factory = BDDFactory.init("java", atoms.size() + 2, atoms.size() + 2, false);
		factory.setVarNum(atoms.size());
		this.run(new Walker(in, factory, atoms, null));
		return mResult;
	}

	private class Walker implements NonRecursive.Walker {

		private Term mTerm;
		private BDDFactory mFactory;
		private List<Term> mAtoms;
		private Walker mParent;
		private List<BDD> mParams;
		private int mCall;

		public Walker(Term t, BDDFactory factory, List<Term> atoms, Walker parent) {
			mTerm = t;
			mFactory = factory;
			mAtoms = atoms;
			mParent = parent;
			mCall = 0;
			mParams = new ArrayList<BDD>();
		}
		
		public void ret(BDD bdd){
			if (mParent != null) {
				mParent.mParams.add(bdd);
			} else {
				mResult = bdd;
			}
		}

		@Override
		public void walk(NonRecursive engine) {
			if (mTerm instanceof ApplicationTerm) {
				ApplicationTerm term = (ApplicationTerm) mTerm;
				String fName = term.getFunction().getName();
				if (fName.equals("and") || fName.equals("or") || fName.equals("xor") || fName.equals("not") || fName.equals("=>")){
					if (mCall == 0) {
						engine.enqueueWalker(this);
						for (Term th : term.getParameters()) {
							Walker w = new Walker(th, mFactory, mAtoms, this);
							engine.enqueueWalker(w);
						}
						mCall++;
						return;
					} else if (mCall == 1) {
						if (fName.equals("and")) {
							BDD result = mParams.remove(0);
							for (BDD bdd : mParams) {
								result = result.and(bdd);
							}
							ret(result);
							
						} else if (fName.equals("or")) {
							BDD result = mParams.remove(0);
							for (BDD bdd : mParams) {
								result = result.or(bdd);
							}
							
							ret(result);
						} else if (fName.equals("xor")) {
							BDD result = mParams.remove(0);
							for (BDD bdd : mParams) {
								result = result.xor(bdd);
							}
							ret(result);
							
						} else if (fName.equals("=>")) {
							BDD result = mParams.remove(0);
							for (BDD bdd : mParams) {
								result = result.imp(bdd);
							}
							ret(result);
							
						} else if (fName.equals("not")) {
							BDD bdd = mParams.remove(0).not();
							ret(bdd);
							
						}
					}
				} else if (fName.equals("true")) {
					BDD bdd = mFactory.one();
					ret(bdd);

				} else if (fName.equals("false")) {
					BDD bdd = mFactory.zero();
					ret(bdd);

				} else {
					BDD bdd = mFactory.ithVar(mAtoms.indexOf(mTerm));
					ret(bdd);
					
				}
			} else if (mTerm instanceof AnnotatedTerm) {
				if (mCall == 0) {
					engine.enqueueWalker(this);
					Walker w = new Walker(((AnnotatedTerm) mTerm).getSubterm(), mFactory, mAtoms, this);
					engine.enqueueWalker(w);
					mCall++;
					return;
					
				} else if (mCall == 1) {
					BDD bdd = mParams.get(0);
					ret(bdd);
				}

			} else {
				BDD bdd = mFactory.ithVar(mAtoms.indexOf(mTerm));
				ret(bdd);
				
			}
		}
	}
}
