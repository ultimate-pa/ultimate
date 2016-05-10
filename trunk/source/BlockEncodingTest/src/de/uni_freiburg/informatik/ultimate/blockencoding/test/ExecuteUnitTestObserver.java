/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 * 
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.test;

import org.apache.log4j.Logger;
import org.junit.runner.JUnitCore;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.util.RCFGStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.models.IElement;
import de.uni_freiburg.informatik.ultimate.models.ModelType;
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
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) {
	}

	@Override
	public void finish() {
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
