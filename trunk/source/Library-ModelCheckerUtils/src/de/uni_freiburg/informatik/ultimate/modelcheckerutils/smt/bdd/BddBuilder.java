package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

public class BddBuilder extends NonRecursive {

	private BDD mResult;

	public BddBuilder() {
		super();
	}

	public BDD buildBDD(final Term in, final List<Term> atoms) {
		final BDDFactory factory = BDDFactory.init("java", atoms.size() + 2, atoms.size() + 2, false);
		factory.setVarNum(atoms.size());
		this.run(new Walker(in, factory, atoms, null));
		return mResult;
	}

	private class Walker implements NonRecursive.Walker {

		private final Term mTerm;
		private final BDDFactory mFactory;
		private final List<Term> mAtoms;
		private final Walker mParent;
		private final List<BDD> mParams;
		private int mCall;

		public Walker(final Term t, final BDDFactory factory, final List<Term> atoms, final Walker parent) {
			mTerm = t;
			mFactory = factory;
			mAtoms = atoms;
			mParent = parent;
			mCall = 0;
			mParams = new ArrayList<>();
		}

		public void ret(final BDD bdd) {
			if (mParent != null) {
				mParent.mParams.add(bdd);
			} else {
				mResult = bdd;
			}
		}

		@Override
		public void walk(final NonRecursive engine) {
			if (mTerm instanceof ApplicationTerm) {
				final ApplicationTerm term = (ApplicationTerm) mTerm;
				final String fName = term.getFunction().getName();
				if (fName.equals("and") || fName.equals("or") || fName.equals("xor") || fName.equals("not")
						|| fName.equals("=>")) {
					if (mCall == 0) {
						engine.enqueueWalker(this);
						for (final Term th : term.getParameters()) {
							final Walker w = new Walker(th, mFactory, mAtoms, this);
							engine.enqueueWalker(w);
						}
						mCall++;
						return;
					} else if (mCall == 1) {
						if (fName.equals("and")) {
							BDD result = mParams.remove(0);
							for (final BDD bdd : mParams) {
								result = result.and(bdd);
							}
							ret(result);

						} else if (fName.equals("or")) {
							BDD result = mParams.remove(0);
							for (final BDD bdd : mParams) {
								result = result.or(bdd);
							}

							ret(result);
						} else if (fName.equals("xor")) {
							BDD result = mParams.remove(0);
							for (final BDD bdd : mParams) {
								result = result.xor(bdd);
							}
							ret(result);

						} else if (fName.equals("=>")) {
							BDD result = mParams.remove(0);
							for (final BDD bdd : mParams) {
								result = result.imp(bdd);
							}
							ret(result);

						} else if (fName.equals("not")) {
							final BDD bdd = mParams.remove(0).not();
							ret(bdd);

						}
					}
				} else if (fName.equals("true")) {
					final BDD bdd = mFactory.one();
					ret(bdd);

				} else if (fName.equals("false")) {
					final BDD bdd = mFactory.zero();
					ret(bdd);

				} else {
					final BDD bdd = mFactory.ithVar(mAtoms.indexOf(mTerm));
					ret(bdd);

				}
			} else if (mTerm instanceof AnnotatedTerm) {
				if (mCall == 0) {
					engine.enqueueWalker(this);
					final Walker w = new Walker(((AnnotatedTerm) mTerm).getSubterm(), mFactory, mAtoms, this);
					engine.enqueueWalker(w);
					mCall++;
					return;

				} else if (mCall == 1) {
					final BDD bdd = mParams.get(0);
					ret(bdd);
				}

			} else {
				final BDD bdd = mFactory.ithVar(mAtoms.indexOf(mTerm));
				ret(bdd);

			}
		}
	}
}
