package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.ExampleNWAFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoAnalysis;
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

	
	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;
	
	public LassoRankerObserver(IUltimateServiceProvider services, IToolchainStorage storage){
		mServices = services;
		mStorage = storage;
	}

	@Override
	public boolean process(IElement root) {
		
		//TODO: Now you can get instances of your library classes for the current toolchain like this: 
		//NWA is nevertheless very broken, as its static initialization prevents parallelism 
		//Surprisingly, this call lazily initializes the static fields of NWA Lib and, like magic, the toolchain works ...
		mServices.getServiceInstance(ExampleNWAFactory.class);
		
		if (!(root instanceof RootNode)) {
			throw new UnsupportedOperationException(
					"LassoRanker can only be applied to models constructed" +
					" by the RCFGBuilder");
		}
		new LassoRankerStarter((RootNode) root, mServices, mStorage);
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