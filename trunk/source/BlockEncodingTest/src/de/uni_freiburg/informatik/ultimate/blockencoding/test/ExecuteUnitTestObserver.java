/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.test;

import org.apache.log4j.Logger;
import org.junit.runner.JUnitCore;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.util.RCFGStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
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

	private static Logger sLogger;
	private static IUltimateServiceProvider sServices;

	/**
	 * Dirty hack for unit tests. Do not use elsewhere, will only work if there
	 * is an instance of {@link ExecuteUnitTestObserver}
	 * 
	 * @return Nothing of your damn business.
	 */
	public static Logger getLogger() {
		return sLogger;
	}

	/**
	 * Dirty hack for unit tests. Do not use elsewhere, will only work if there
	 * is an instance of {@link ExecuteUnitTestObserver}
	 * 
	 * @return Nothing of your damn business.
	 */
	public static IUltimateServiceProvider getServices() {
		return sServices;
	}

	private IElement root;

	public ExecuteUnitTestObserver(IUltimateServiceProvider services) {
		sServices = services;
		sLogger = sServices.getLoggingService().getLogger("BlockEncodingTest");
	}

	@Override
	public void init() {
	}

	@Override
	public void finish() {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean process(IElement root) {
		this.root = root;
		RCFGStore.setRCFG((RCFGNode) root);
		Result res = JUnitCore.runClasses(
				de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestAbstractMinimizationVisitor.class,
				de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestMinimizeBranchVisitor.class,
				de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestMinimizeLoopVisitor.class,
				de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestMinimizeCallReturnVisitor.class,
				de.uni_freiburg.informatik.ultimate.blockencoding.test.unit.TestMinModelConversion.class);
		// Print out the result of the test!
		if (res.getFailureCount() > 0) {
			sLogger.error("A JUnit Test Case have failed!");
		}

		for (Failure failure : res.getFailures()) {
			sLogger.error(failure);
			sLogger.error(failure.getDescription());
			sLogger.error(failure.getException());
			sLogger.error(failure.getMessage());
			sLogger.error(failure.getTrace());
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
