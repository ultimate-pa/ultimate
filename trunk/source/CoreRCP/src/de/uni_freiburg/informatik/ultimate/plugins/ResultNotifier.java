/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Evren Ermis
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.result.model.IResult;

public class ResultNotifier {

	private enum ToolchainResult {
		NORESULT(-1),
		GENERICRESULT(0), 
		CORRECT(1), 
		UNPROVABLE(2), 
		TIMEOUT(3), 
		INCORRECT(4), 
		SYNTAXERROR(5);

		private int mValue;

		ToolchainResult(int i) {
			mValue = i;
		}

		boolean isLess(ToolchainResult other) {
			return mValue < other.mValue;
		}

		boolean isLessOrEqual(ToolchainResult other) {
			return mValue <= other.mValue;
		}
	}

	private final IController mController;
	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;

	public ResultNotifier(IController controller, IUltimateServiceProvider services) {
		assert services != null;
		mController = controller;
		mServices = services;
		mLogger = mServices.getLoggingService().getControllerLogger();
	}

	public void processResults() {
		ToolchainResult toolchainResult = ToolchainResult.NORESULT;
		String description = "Toolchain returned no Result.";

		for (List<IResult> PluginResults : mServices.getResultService().getResults().values()) {
			for (IResult result : PluginResults) {
				if (result instanceof SyntaxErrorResult) {
					toolchainResult = ToolchainResult.SYNTAXERROR;
					description = result.getShortDescription();
				} else if (result instanceof UnprovableResult) {
					if (toolchainResult.isLess(ToolchainResult.UNPROVABLE)) {
						toolchainResult = ToolchainResult.UNPROVABLE;
						description = "unable to determine feasibility of some traces";
					}
				} else if (result instanceof CounterExampleResult) {
					if (toolchainResult.isLess(ToolchainResult.INCORRECT))
						toolchainResult = ToolchainResult.INCORRECT;
				} else if (result instanceof PositiveResult) {
					if (toolchainResult.isLess(ToolchainResult.CORRECT))
						toolchainResult = ToolchainResult.CORRECT;
				} else if (result instanceof TimeoutResultAtElement) {
					if (toolchainResult.isLess(ToolchainResult.TIMEOUT)) {
						toolchainResult = ToolchainResult.TIMEOUT;
						description = "Timeout";
					}
				} else if (result instanceof GenericResultAtElement) {
					if (toolchainResult.isLessOrEqual(ToolchainResult.GENERICRESULT)) {
						toolchainResult = ToolchainResult.GENERICRESULT;
						description = result.getShortDescription() + "  " + result.getLongDescription();
					}
				}
			}
		}
		switch (toolchainResult) {
		case SYNTAXERROR:
		case UNPROVABLE:
		case TIMEOUT:
		case NORESULT:
			programUnknown(description);
			break;
		case INCORRECT:
			programIncorrect();
			break;
		case CORRECT:
			programCorrect();
			break;
		case GENERICRESULT:
			mLogger.info(description);
			break;
		default:
			throw new AssertionError("unknown result");
		}
	}

	private void programCorrect() {
		mLogger.info("RESULT: Ultimate proved your program to be correct!");
		mController.displayToolchainResultProgramCorrect();
	}

	private void programIncorrect() {
		mLogger.info("RESULT: Ultimate proved your program to be incorrect!");
		mController.displayToolchainResultProgramIncorrect();
	}

	private void programUnknown(final String text) {
		mLogger.info("RESULT: Ultimate could not prove your program: " + text);
		mController.displayToolchainResultProgramUnknown(text);
	}
}
