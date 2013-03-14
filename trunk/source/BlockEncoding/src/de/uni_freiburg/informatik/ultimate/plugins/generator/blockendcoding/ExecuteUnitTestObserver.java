/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding;

import org.apache.log4j.Logger;
import org.junit.runner.JUnitCore;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.util.RCFGStore;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * The purpose of this observer is to execute unit tests, defined in test folder
 * of this plugin. Since we need a complete RCFG, it makes sense to execute
 * these test at the end of a toolchain with Ultimate.
 * 
 * @author Stefan Wissert
 * 
 */
public class ExecuteUnitTestObserver implements IUnmanagedObserver {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);

	private IElement root;

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.access.IObserver#init()
	 */
	@Override
	public void init() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.access.IObserver#finish()
	 */
	@Override
	public void finish() {
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.access.IObserver#getWalkerOptions()
	 */
	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.access.IObserver#performedChanges()
	 */
	@Override
	public boolean performedChanges() {
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver#process
	 * (de.uni_freiburg.informatik.ultimate.model.IElement)
	 */
	@Override
	public boolean process(IElement root) {
		// TODO: Execute Unit Tests!
		this.root = root;
		RCFGStore.setRCFG((RCFGNode) root);
		Result res = JUnitCore
				.runClasses(
						de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestAbstractMinimizationVisitor.class,
						de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestMinimizeBranchVisitor.class,
						de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestMinimizeLoopVisitor.class,
						de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestMinimizeCallReturnVisitor.class,
						de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestMinModelConversion.class);
		// Print out the result of the test!
		if (res.getFailureCount() > 0) {
			s_Logger.error("A JUnit Test Case have failed!");
		}
		for (Failure failure : res.getFailures()) {
			// TODO: More output, how get the logging right here!
			s_Logger.error(failure);
			s_Logger.error(failure.getDescription());
			s_Logger.error(failure.getException());
			s_Logger.error(failure.getMessage());
			s_Logger.error(failure.getTrace());
		}
		return false;
	}

	/**
	 * @return the root
	 */
	public IElement getRoot() {
		return root;
	}
}
