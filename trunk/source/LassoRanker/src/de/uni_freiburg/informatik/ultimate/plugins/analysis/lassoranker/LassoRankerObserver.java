package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;


/**
 * Observer for LassoRanker
 * 
 * Extracts the lasso program's stem and loop transition from the RCFG builder's
 * transition graph. This is then passed to the LassoAnalysis
 * class, which serves as an interface to LassoRanker's termination and
 * non-termination analysis methods.
 * 
 * Termination and non-termination arguments are synthesizer via constraint
 * solving. The generated constraints are non-linear algebraic constraints.
 * We use an external SMT solver to solve these constraints.
 * 
 * @see LassoAnalysis
 * @author Matthias Heizmann, Jan Leike
 */
public class LassoRankerObserver implements IUnmanagedObserver {

	
	@Override
	public boolean process(IElement root) {
		if (!(root instanceof RootNode)) {
			throw new UnsupportedOperationException(
					"LassoRanker can only be applied to models constructed" +
					" by the RCFGBuilder");
		}
		new LassoRankerStarter((RootNode) root);
		return false;
	}
	
	/**
	 * @return the root of the CFG.
	 */
	public IElement getRoot(){
		return null;
	}
	
	@Override
	public void init() {
//		Ordinal.testcases();
	}

	@Override
	public void finish() {
		// nothing to do
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null; // not required
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}