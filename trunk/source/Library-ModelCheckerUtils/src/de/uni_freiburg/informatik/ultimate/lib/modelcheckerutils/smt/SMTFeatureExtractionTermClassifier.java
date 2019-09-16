package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class SMTFeatureExtractionTermClassifier extends NonRecursive{
	
	private final ILogger mLogger;

	private Set<Term> mTermsInWhichWeAlreadyDescended;

	private final Set<String> mOccuringSortNames;
	private final Set<String> mOccuringFunctionNames;
	private final Set<Integer> mOccuringQuantifiers;
	private boolean mHasArrays;

	private int mNumberOfVariables;
	private int mNumberOfFunctions;
	private int mNumberOfQuantifiers;
	private int mDAGSize;
	private long mTreeSize;
	
	private UnionFind<Term> mUnionFind;

	private final ArrayList<String> mTerms;

	public SMTFeatureExtractionTermClassifier(ILogger logger) {
		super();
		mLogger = logger;
		mOccuringSortNames = new HashSet<>();
		mOccuringFunctionNames = new HashSet<>();
		mOccuringQuantifiers = new HashSet<>();
		mHasArrays = false;
		mNumberOfVariables = 0;
		mNumberOfFunctions = 0;
		mNumberOfQuantifiers = 0;
		mDAGSize = 0;
		mTreeSize = 0;
		mTerms = new ArrayList<String>();
		mUnionFind = new UnionFind<>();
	}

	public Set<String> getOccuringSortNames() {
		return mOccuringSortNames;
	}

	public Set<String> getOccuringFunctionNames() {
		return mOccuringFunctionNames;
	}

	public Set<Integer> getOccuringQuantifiers() {
		return mOccuringQuantifiers;
	}

	public int getNumberOfVariables() {
		return mNumberOfVariables;
	}

	public int getNumberOfFunctions() {
		return mNumberOfFunctions;
	}

	public int getNumberOfQuantifiers() {
		return mNumberOfQuantifiers;
	}

	public boolean hasArrays() {
		return mHasArrays;
	}

	public ArrayList<String> getTerm() {
		return mTerms;
	}

	public int getDAGSize() {
		return mDAGSize;
	}

	public long getTreeSize() {
		return mTreeSize;
	}

	public String getStats() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Formula ").append(mTerms).append("\n");
		sb.append("Occuring sorts ").append(mOccuringSortNames.toString()).append("\n");
		sb.append("Occuring functions  ").append(mOccuringFunctionNames.toString()).append("\n");
		sb.append("Occuring Quantifiers  ").append(mOccuringQuantifiers.toString()).append("\n");
		sb.append("DAGSize  ").append(mDAGSize).append("\n");
		sb.append("TreeSize  ").append(mTreeSize).append("\n");
		sb.append("Number of functions ").append(mNumberOfFunctions).append("\n");
		sb.append("Number of quantifiers ").append(mNumberOfQuantifiers).append("\n");
		sb.append("Number of variables ").append(mNumberOfVariables).append("\n");
		return sb.toString();
	}

	/**
	 * Check a/another Term and add the result to the existing classification results.
	 */
	public void checkTerm(final Term term) {
		mTermsInWhichWeAlreadyDescended = new HashSet<>();
		mTerms.add(term.toString());
		mDAGSize += new DAGSize().size(term);
		mTreeSize += new DAGSize().treesize(term);
		mLogger.warn("FULL TERM: " + term.toStringDirect());
		run(new MyWalker(term));
		mTermsInWhichWeAlreadyDescended = null;
		mLogger.warn("UNION FIND: "  + mUnionFind.toString());
	}
	
	private boolean isApplicationTermWithArityZero(Term term) {
		if (term instanceof ApplicationTerm) {
	    	ApplicationTerm appterm = (ApplicationTerm) term;
	    	if(appterm.getParameters().length == 0) {
	    		return true;
	    	}
		}
		return false;
	}

	private class MyWalker extends TermWalker {
		MyWalker(final Term term) {
			super(term);
		}

		@Override
		public void walk(final NonRecursive walker) {
			if (mTermsInWhichWeAlreadyDescended.contains(getTerm())) {
				// do nothing
			} else {
				Term term = getTerm();
			    // Add sorts only if term is TermVariable or ApplicationTerm with arity 0.
			    if(!term.toStringDirect().equals("true") && !term.toStringDirect().equals("false") 
			       && (term instanceof TermVariable || isApplicationTermWithArityZero(term))) {
			    	final Sort currentSort = term.getSort();
			    	mOccuringSortNames.add(currentSort.toString());
			    	if (currentSort.isArraySort()) {
			    		mHasArrays = true;
					}
				}
				super.walk(walker);
			}
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// cannot descend
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			mTermsInWhichWeAlreadyDescended.add(term);
			walker.enqueueWalker(new MyWalker(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			int numberOfParameters = term.getParameters().length;
	    	if(numberOfParameters > 0) {
	    		final String functionName = term.getFunction().getName();
	    		mOccuringFunctionNames.add(functionName);
	    		mLogger.warn("######################## START #######################");
	    		mLogger.warn("FUNCTION: " + functionName);
	    		mLogger.warn("TERM: " + term.toStringDirect());
	    		final Term[] termParameters = term.getParameters();
	    		for (int i = 0; i < termParameters.length - 1; i++) {	    				
	    			final Term term1 = termParameters[i];
	    			final Term term2 = termParameters[i+1];
	    			if (isApplicationTermWithArityZero(term1)  && isApplicationTermWithArityZero(term2) ) {
					    	final Term rep1 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(term1);
					    	final Term rep2 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(term2);
					    	mLogger.warn("REP1: " + rep1.toStringDirect());
					    	mLogger.warn("REP2: " + rep2.toStringDirect());
					    	mUnionFind.union(rep1, rep2);
					    }
					}
	    			mLogger.warn("######################### END #########################");
	    		
	    		mNumberOfFunctions += 1;
	    	}else {	    	
	    		mNumberOfVariables += 1;
	    	}
			
			mTermsInWhichWeAlreadyDescended.add(term);
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new MyWalker(t));
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			mTermsInWhichWeAlreadyDescended.add(term);
			walker.enqueueWalker(new MyWalker(term.getSubTerm()));
			for (final Term v : term.getValues()) {
				walker.enqueueWalker(new MyWalker(v));
			}

		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			mOccuringQuantifiers.add(term.getQuantifier());
			mNumberOfQuantifiers += 1;
			walker.enqueueWalker(new MyWalker(term.getSubformula()));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// cannot descend
		}

		@Override
		public void walk(final NonRecursive walker, final MatchTerm term) {
			throw new UnsupportedOperationException("not yet implemented: MatchTerm");
		}
	}
}
