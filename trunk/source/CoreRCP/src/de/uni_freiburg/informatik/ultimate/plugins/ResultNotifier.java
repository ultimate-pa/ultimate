package de.uni_freiburg.informatik.ultimate.plugins;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

public class ResultNotifier {

	private static final int NORESULT = -1;
	private static final int GENERICRESULT = 0;
	private static final int CORRECT = 1;
	private static final int UNPROVABLE = 2;
	private static final int TIMEOUT = 3;
	private static final int INCORRECT = 4;
	private static final int SYNTAXERROR = 5;

	private IController mCurrentController;
	private final Logger mLogger;

	public ResultNotifier(IController controller) {
		mCurrentController = controller;
		mLogger = UltimateServices.getInstance().getControllerLogger();
	}

	public void processResults() {
		int toolchainResult = ResultNotifier.NORESULT;
		String description = "Toolchain returned no Result.";

		for (List<IResult> PluginResults : UltimateServices.getInstance()
				.getResultMap().values()) {
			for (IResult result : PluginResults) {
				if (result instanceof SyntaxErrorResult) {
					toolchainResult = ResultNotifier.SYNTAXERROR;
					description = result.getShortDescription();
				} else if (result instanceof UnprovableResult) {
					if (toolchainResult < ResultNotifier.UNPROVABLE) {
						toolchainResult = ResultNotifier.UNPROVABLE;
						description = "unable to determine feasibility of some traces";
					}
				} else if (result instanceof CounterExampleResult) {
					if (toolchainResult < ResultNotifier.INCORRECT)
						toolchainResult = ResultNotifier.INCORRECT;
				} else if (result instanceof PositiveResult) {
					if (toolchainResult < ResultNotifier.CORRECT)
						toolchainResult = ResultNotifier.CORRECT;
				} else if (result instanceof TimeoutResult) {
					if (toolchainResult < ResultNotifier.TIMEOUT) {
						toolchainResult = ResultNotifier.TIMEOUT;
						description = "Timeout";
					}
				} else if (result instanceof GenericResultAtElement) {
					if (toolchainResult <= ResultNotifier.GENERICRESULT) {
						toolchainResult = ResultNotifier.GENERICRESULT;
						description = result.getShortDescription() + "  " 
												+ result.getLongDescription();
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
		mCurrentController.displayToolchainResultProgramCorrect();
	}

	private void programIncorrect() {
		mLogger.info("RESULT: Ultimate proved your program to be incorrect!");
		mCurrentController.displayToolchainResultProgramIncorrect();
	}

	private void programUnknown(final String text) {
		mLogger.info("RESULT: Ultimate could not prove your program: " + text);
		mCurrentController.displayToolchainResultProgramUnknown(text);
	}
}
