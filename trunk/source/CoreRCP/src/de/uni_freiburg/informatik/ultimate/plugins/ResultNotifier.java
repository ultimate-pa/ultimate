package de.uni_freiburg.informatik.ultimate.plugins;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

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
